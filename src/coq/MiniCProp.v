Require Import paco.
Require Import Bool String Ascii List.
Require Import Omega.
Require Import Vellvm.MiniLLVM.
Require Import Vellvm.Util Vellvm.Misc.

Import ListNotations.

Set Implicit Arguments.

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

Fixpoint subst_instr_list l i :=
  match l with
    | [] => i
    | (id, v) :: t => subst_instr_list t (subst_instr id v i)
  end.

Fixpoint subst_term_list l term :=
  match l with
    | [] => term
    | (id, v) :: t => subst_term_list t (subst_term id v term)
  end.

Definition get_constants_from_block (l : block) :=
  fold_right (fun i subs =>
                match i with
                  | (IId id, INSTR_Op (SV (VALUE_Integer _ i) as val)) =>
                    (ID_Local id, val) :: subs
                  | sub => subs
                end) [] (blk_instrs l).

Definition get_constants_from_blocks (l : list block) :=
  fold_right (fun i subs => get_constants_from_block i ++ subs) [] l.

Definition get_constants es :=
  fold_right (fun d acc =>
                match d with
                  | TLE_Definition d => get_constants_from_blocks (df_instrs d) ++ acc
                end) [] es.

Definition prop_const_block_instrs subs (l : list (instr_id * instr)) :=
  fold_right (fun i l =>
                let '(id, v) := i in
                match (id, subst_instr_list subs v) with
                  | (IId id, INSTR_Op (SV (VALUE_Integer _ i) as val)) =>
                    l
                  | sub => sub :: l
                end) [] l.

Definition remove_const_block_instrs subs (l : list (instr_id * instr)) :=
  fold_right (fun i l =>
                let '(id, v) := i in
                match (subst_instr_list subs v) with
                  | (INSTR_Op (SV (VALUE_Integer _ i) as val)) =>
                    l
                  | sub => (id, v) :: l
                end) [] l.
                    
Definition prop_const_block subs b :=
  {| blk_id := blk_id b;
     blk_instrs := prop_const_block_instrs subs (blk_instrs b);
     blk_term_id := blk_term_id b;
     blk_term := subst_term_list subs (blk_term b)
  |}.

Definition remove_const_block subs b :=
  {| blk_id := blk_id b;
     blk_instrs := remove_const_block_instrs subs (blk_instrs b);
     blk_term_id := blk_term_id b;
     blk_term := blk_term b
  |}.

Definition prop_const_def subs d :=
  {| df_prototype := df_prototype d;
     df_args := df_args d;
     df_instrs := map (prop_const_block subs) (df_instrs d)
  |}.

Definition remove_const_def subs d :=
  {| df_prototype := df_prototype d;
     df_args := df_args d;
     df_instrs := map (remove_const_block subs) (df_instrs d)
  |}.

Definition prop_const_entity subs e :=
  match e with
    | TLE_Definition d => TLE_Definition (prop_const_def subs d)
  end.

Definition remove_const_entity subs e :=
  match e with
    | TLE_Definition d => TLE_Definition (remove_const_def subs d)
  end.

Definition prop_const_entities es :=
  let constants := get_constants es in
  map (prop_const_entity constants) es.

Definition remove_const_entities es :=
  let constants := get_constants es in
  map (remove_const_entity constants) es.

Lemma prop_const_preserve_id :
  forall subs b, blk_id b = blk_id (prop_const_block subs b).
Proof.
  intros. unfold prop_const_block.
  destruct (prop_const_block_instrs subs (blk_instrs b)); simpl; eauto. 
Qed.

Fixpoint value_to_dvalue (x : value) : dvalue :=
  match x with
    | SV (VALUE_Ident _ x) => DV (VALUE_Ident _ x)
    | SV (VALUE_Integer _ i) => DV (VALUE_Integer _ i)
    | SV (VALUE_Bool _ b) => DV (VALUE_Bool _ b)
    | SV (VALUE_Null _) => DV (VALUE_Null _)
    | SV (VALUE_Undef _) => DV (VALUE_Undef _)
    | SV (OP_IBinop b t e1 e2) => DV (OP_IBinop b t (value_to_dvalue e1) (value_to_dvalue e2))
    | SV (OP_ICmp b t e1 e2) => DV (OP_ICmp b t (value_to_dvalue e1) (value_to_dvalue e2))
  end.

Inductive wf_dvalue : dvalue -> Prop :=
| wf_code_pointer : forall p, wf_dvalue (DVALUE_CodePointer p)
| wf_addr : forall a, wf_dvalue (DVALUE_Addr a)
| wf_int : forall i, wf_dvalue (DV (VALUE_Integer dvalue i))
| wf_bool : forall b, wf_dvalue (DV (VALUE_Bool dvalue b))
| wf_null : wf_dvalue (DV (VALUE_Null dvalue))
| wf_undef : wf_dvalue (DV (VALUE_Undef dvalue))
.

Lemma eval_subst_env :
  forall x i env exp,
    wf_dvalue (value_to_dvalue x) ->
    eval_op env (subst_value (ID_Local i) x exp) = eval_op ((i, value_to_dvalue x) :: env) exp.
Proof.
  intros. induction exp using value_ind'; eauto.
  - simpl. destruct id; simpl; eauto. unfold lookup_env; simpl. simpl.
    compare id i; try intro; try (repeat decide equality); subst.
    + destruct (raw_id_eq_dec i i); try solve [exfalso; apply n; eauto].
      destruct (ident_eq_dec (ID_Local i) (ID_Local i)); try solve [exfalso; apply n; eauto]. destruct x.
      inversion H; destruct e1; inversion H1; subst; eauto.
    + destruct (raw_id_eq_dec id i); try solve [exfalso; eauto].
      destruct (ident_eq_dec (ID_Local i) (ID_Local id)); try solve [exfalso; inversion e; eauto].
      simpl; eauto.
  - simpl. rewrite IHexp1. rewrite IHexp2. eauto.
  - simpl. rewrite IHexp1. rewrite IHexp2. eauto.
Qed.

Definition constants_to_env (e : list (ident * value)) :=
  map (fun x => let '(id, v) := x in
                match id with
                  | ID_Local i
                  | ID_Global i => (i, value_to_dvalue v)
                end) e.

Definition stepConstants subs CFG s : D state :=
  let '(p, e, k) := s in
  stepD CFG (p, subs ++ e, k).

CoFixpoint semConstants subs CFG s : DLim :=
  bind (stepConstants subs CFG s) (semConstants subs CFG).

Lemma prop_remove_equiv :
  forall cs es CFG1 CFG2,
    cs = get_constants es ->
    TLE_to_cfg (prop_const_entities es) = Some CFG1 ->
    TLE_to_cfg (remove_const_entities es) = Some CFG2 ->
    d_equiv (semConstants (constants_to_env cs) CFG2 (init_state CFG2)) (sem CFG1 (init_state CFG1)).
Proof.
Admitted.