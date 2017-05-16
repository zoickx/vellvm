Require Import paco.
Require Import Bool String Ascii List.
Require Import Omega.
Require Import Vellvm.MiniLLVM.
Require Import Vellvm.Util Vellvm.Misc.

Import ListNotations.

Set Implicit Arguments.

Definition instr_ids_of_block blk :=
  (blk_term_id blk) :: (map fst (blk_instrs blk)).

Definition no_dups_block blk :=
  NoDup (instr_ids_of_block blk).

Definition no_dups_defn defn :=
  (forall d, In d (df_instrs defn) -> no_dups_block d) /\
  (forall d1 d2 x, In d1 (df_instrs defn) -> In d2 (df_instrs defn) ->
                   In x (instr_ids_of_block d1) -> In x (instr_ids_of_block d2) ->
                   d1 = d2).

Inductive no_dups_tles : toplevel_entities -> Prop :=
| no_dups_tles_nil : no_dups_tles []
| no_dups_tles_cons :
    forall d tles, no_dups_defn d -> no_dups_tles tles ->
                   no_dups_tles ((TLE_Definition d) :: tles).

(* How does this interact with memory effects? 
   There should be a case for Eff here *)
Inductive trace cfg : list path -> Prop :=
| trace_init : trace cfg [init cfg]
| trace_ret :
    forall p e k l p' e' k', stepD cfg (p, e, k) = Ret (p', e', k') ->
                             trace cfg (p' :: p :: l)
| trace_alloca :
    forall p e k l p' e' k' i cont t, stepD cfg (p, e, k) = Eff (Alloc t cont) ->
                                      cont i = Ret (p', e', k') ->
                                      trace cfg (p' :: p :: l)
| trace_load :
    forall p e k l p' e' k' i cont a, stepD cfg (p, e, k) = Eff (Load a cont) ->
                                      cont i = Ret (p', e', k') ->
                                      trace cfg (p' :: p :: l)
| trace_store :
    forall p e k l p' e' k' a v, stepD cfg (p, e, k) = Eff (Store a v (Ret (p', e', k'))) ->
                                 trace cfg (p' :: p :: l)
.

Inductive use_value i : value -> Prop :=
| use_ident : use_value i (SV (VALUE_Ident value i))
| use_binop_l : forall iop t v1 v2, use_value i v1 -> use_value i (SV (OP_IBinop iop t v1 v2))
| use_binop_r : forall iop t v1 v2, use_value i v2 -> use_value i (SV (OP_IBinop iop t v1 v2))
| use_cmp_l : forall iop t v1 v2, use_value i v1 -> use_value i (SV (OP_ICmp iop t v1 v2))
| use_cmp_r : forall iop t v1 v2, use_value i v2 -> use_value i (SV (OP_ICmp iop t v1 v2)).

Inductive use_instr i : instr -> Prop :=
| use_op : forall v, use_value i v -> use_instr i (INSTR_Op v)
| use_call : forall f t v args, In (t, v) args -> use_value i v -> use_instr i (INSTR_Call f args)
| use_phi : forall t v id args, In (id, v) args -> use_value i v -> use_instr i (INSTR_Phi t args)
| use_load : forall t1 t2 v, use_value i v -> use_instr i (INSTR_Load t1 (t2, v))
| use_store : forall t tid v, use_value i v -> use_instr i (INSTR_Store (t, v) tid).

Inductive use_term i : terminator -> Prop :=
| use_ret : forall t v, use_value i v -> use_term i (TERM_Ret (t, v))
| use_br : forall t v b1 b2, use_value i v -> use_term i (TERM_Br (t, v) b1 b2).

Inductive use_at_path i cfg p : Prop :=
| use_step : forall ins p', code cfg p = Some (Step ins p') -> use_instr i ins -> use_at_path i cfg p
| use_jump : forall t, code cfg p = Some (Jump t) -> use_term i t -> use_at_path i cfg p.

(* This might not be correct, I might have got id/ident/raw_id wrong *)
Definition ssa cfg :=
  forall p i l p' r, trace cfg (p :: l) -> use_at_path i cfg p ->
                     def_id_of_path p' = Some r ->
                     raw_id_of_ident i = Some r -> In p' l.

Fixpoint subst_value id v v' :=
  match v' with
    | SV (VALUE_Ident _ id') => if ident_eq_dec id id' then v else SV (VALUE_Ident _ id')
    | SV (OP_IBinop iop t vl vr) => SV (OP_IBinop iop t (subst_value id v vl) (subst_value id v vr))
    | SV (OP_ICmp cmp t vl vr) => SV (OP_ICmp cmp t (subst_value id v vl) (subst_value id v vr))
    | x => x
  end.

Definition subst_tvalue id v (tv : tvalue) :=
  let '(t, v') := tv in (t, subst_value id v' v).

Definition subst_instr id v (i : instr) :=
  match i with
    | INSTR_Op v' => INSTR_Op (subst_value id v v')
    | INSTR_Call fn args => INSTR_Call fn (map (subst_tvalue id v) args)
    | INSTR_Phi t args => INSTR_Phi t (map (fun x => (fst x, subst_value id v (snd x))) args)
    | INSTR_Load t ptr => INSTR_Load t (subst_tvalue id v ptr)
    | INSTR_Store val ptr => INSTR_Store (subst_tvalue id v val) ptr
    | _ => i
  end.

Definition subst_term id v (t : terminator) :=
  match t with
    | TERM_Ret v' => TERM_Ret (subst_tvalue id v v')
    | TERM_Br v' br1 br2 => TERM_Br (subst_tvalue id v v') br1 br2
    | _ => t
  end.

Definition subst_block id v (b : block) :=
  {| blk_id := blk_id b;
     blk_instrs := map (fun p => (fst p, subst_instr id v (snd p))) (blk_instrs b);
     blk_term_id := blk_term_id b;
     blk_term := subst_term id v (blk_term b)
  |}.

Definition subst_def id v d :=
  {| df_prototype := df_prototype d;
     df_args := df_args d;
     df_instrs := map (subst_block id v) (df_instrs d)
  |}.

Definition subst_entity id v e :=
  match e with
    | TLE_Definition d => TLE_Definition (subst_def id v d)
  end.

Definition subst_entities id v es :=
  map (subst_entity id v) es.

Theorem subst_equiv :
  forall es cfg cfg' p id x p' r,
    no_dups_tles es -> ssa cfg -> TLE_to_cfg es = Some cfg ->
    TLE_to_cfg (subst_entities id (SV (VALUE_Integer value x)) es) = Some cfg' ->
    code cfg p = Some (Step (INSTR_Op (SV (VALUE_Integer value x))) p') ->
    def_id_of_path p = Some r -> raw_id_of_ident id = Some r ->
    CFG_equiv cfg cfg'.
Proof.
  (* Needs a well-formedness predicate as with the decompiler stuff 
     relating environment to set of paths visited *)
Abort.

