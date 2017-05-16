Require Import paco.
Require Import Bool String Ascii List.
Require Import Omega.
Require Import Vellvm.MiniLLVM.
Require Import Vellvm.Util Vellvm.Misc.

Set Implicit Arguments.

Fixpoint cfold_val (d : value) : value :=
  match d with
    | SV s =>
      match s with
        | VALUE_Ident _ id => SV (VALUE_Ident value id)  
        | VALUE_Integer _ x => SV (VALUE_Integer value x)
        | VALUE_Bool _ b => SV (VALUE_Bool value b)
        | VALUE_Null _ => SV (VALUE_Null value)
        | VALUE_Undef _ => SV (VALUE_Undef value)
        | OP_IBinop ib t v1 v2 =>
          let cv1 := cfold_val v1 in
          let cv2 := cfold_val v2 in
          match cv1, cv2 with
            | SV (VALUE_Integer _ x), SV (VALUE_Integer _ y) =>
              match ib with
                | Add => SV (VALUE_Integer value (x + y))
                | Sub => SV (VALUE_Integer value (x - y))
                | Mul => SV (VALUE_Integer value (x * y))
              end
            | _ , _ => SV (OP_IBinop ib t cv1 cv2)
          end
        | OP_ICmp ic t v1 v2 =>
          let cv1 := cfold_val v1 in
          let cv2 := cfold_val v2 in
          match cv1, cv2 with
            | SV (VALUE_Integer _ x), SV (VALUE_Integer _ y) =>
              match ic with
                | Eq => SV (VALUE_Bool value (nat_beq x y))
                | Ule => SV (VALUE_Bool value (leb x y)) 
              end
            | _, _ => SV (OP_ICmp ic t cv1 cv2)
          end
      end
  end.

Definition cfold_instr i :=
  match i with
    | INSTR_Op o => INSTR_Op (cfold_val o)
    | INSTR_Call fn args => INSTR_Call fn (map (fun p => (fst p, cfold_val (snd p))) args)
    | INSTR_Phi t args => INSTR_Phi t (map (fun p => (fst p, cfold_val (snd p))) args)
    | INSTR_Alloca t => INSTR_Alloca t
    | INSTR_Load t (a, b) => INSTR_Load t (a, cfold_val b) 
    | INSTR_Store (a, b) ptr => INSTR_Store (a, cfold_val b) ptr
    | INSTR_Unreachable => INSTR_Unreachable
  end.

Definition cfold_term t :=                                            
  match t with
    | TERM_Ret (a, b) => TERM_Ret (a, cfold_val b)
    | TERM_Ret_void => TERM_Ret_void
    | TERM_Br (a, b) v1 v2 => TERM_Br (a, cfold_val b) v1 v2 
    | TERM_Br_1 b => TERM_Br_1 b
  end.

Definition cfold_cmd c :=
  match c with
    | Step i p => Step (cfold_instr i) p
    | Jump t => Jump (cfold_term t)
  end.

Definition cfold_phis (ps : list (local_id * instr)) :=
  map (fun p => (fst p, cfold_instr (snd p))) ps.

Definition cfold_block_entry b :=
  match b with
    | Phis ls p => Phis (cfold_phis ls) p
  end.

Definition cfold cfg :=
  {|
    init := init cfg;
    code := fun p => match (code cfg p) with
                       | None => None
                       | Some x => Some (cfold_cmd x)
                     end;
    funs := funs cfg;
    blks := fun fid bid =>
              match (blks cfg fid bid) with
                | None => None
                | Some x => Some (cfold_block_entry x)
              end
  |}.

Lemma cfold_eval_op_correct :
  forall v st, eval_op st (cfold_val v) = eval_op st v.
Proof.
  intros. induction v using value_ind'; eauto.
  - simpl. rewrite <- IHv1. rewrite <- IHv2.
    destruct (cfold_val v1); eauto.
    destruct e; eauto.
    destruct (cfold_val v2); eauto.
    destruct e; eauto.
    simpl. destruct iop; eauto.
  - simpl. rewrite <- IHv1. rewrite <- IHv2.
    destruct (cfold_val v1); eauto.
    destruct e; eauto.
    destruct (cfold_val v2); eauto.
    destruct e; eauto.
    simpl. destruct cmp; eauto. 
Qed.

Lemma cfold_jump_correct :
  forall cfg p e_old e ps q k,
    jump cfg p e_old e ps q k = jump (cfold cfg) p e_old e (cfold_phis ps) q k.
Proof.
  intros. generalize dependent e. induction ps; eauto. destruct a. simpl.
  intros. destruct i; eauto.
  - simpl. rewrite assoc_map.
    destruct (assoc ident_eq_dec (ID_Local (bn p)) args); simpl; eauto.
    rewrite cfold_eval_op_correct; eauto.
    destruct (eval_op e_old v); eauto. 
  - destruct ptr. eauto.
  - destruct ptr. destruct val; eauto.
Qed.

Lemma cfold_stepD_correct : forall CFG s, stepD CFG s = stepD (cfold CFG) s.
Proof.
  intros. destruct s. destruct p. destruct CFG. simpl.
  destruct (code p); eauto; simpl.
  destruct c; unfold cfold_cmd.
  - destruct i; simpl; try (destruct ptr); try (destruct val); try (destruct v); eauto.
    + destruct (def_id_of_path p); eauto; simpl.
      rewrite cfold_eval_op_correct; eauto.
    + destruct fn. destruct i; eauto.
      destruct (def_id_of_path p); eauto; simpl.
      destruct (funs id); eauto; simpl.
      destruct p1. destruct p1.
      destruct (map_option raw_id_of_ident l); eauto; simpl.
      rewrite map_map.
      rewrite map_option_map. rewrite map_option_map.
      simpl.
      assert (map_option (fun x => eval_op e (snd x)) args = map_option (fun x => eval_op e (cfold_val (snd x))) args).
      induction args; eauto. simpl. rewrite cfold_eval_op_correct.
      rewrite IHargs; eauto.
      rewrite <- H; eauto. 
    + rewrite cfold_eval_op_correct; eauto.
    + rewrite cfold_eval_op_correct; eauto.
  - destruct t; simpl; eauto.
    + destruct v. destruct s; rewrite cfold_eval_op_correct; eauto.
    + destruct v. destruct br1. destruct br2.
      rewrite cfold_eval_op_correct; eauto.
      destruct (eval_op e v); eauto. destruct d; eauto.
      destruct e0; eauto. destruct b; simpl.
      destruct (raw_id_of_ident i); simpl; eauto.
      destruct (blks (bn p) r); simpl; eauto.
      * destruct b; simpl. rewrite cfold_jump_correct; eauto.
      * destruct (raw_id_of_ident i0); simpl; eauto.
        destruct (blks (bn p) r); simpl; eauto.
        destruct b; simpl. rewrite cfold_jump_correct.  eauto.
    + destruct br. destruct (raw_id_of_ident i); simpl; eauto.
      destruct (blks (bn p) r); simpl; eauto.
      destruct b; simpl; rewrite cfold_jump_correct; eauto.
Qed.

Lemma cfold_init_state: forall CFG, init_state CFG = init_state (cfold CFG).
Proof.
  destruct CFG; eauto.
Qed.

Lemma CFG_cfold_bind_equiv :
  forall d CFG, d_equiv (bind d (sem CFG)) (bind d (sem (cfold CFG))).
Proof.
  pcofix CIH. intros. pfold.
  rewrite id_d_eq; rewrite id_d_eq at 1.
  destruct d; try solve [constructor; eauto].
  - constructor. rewrite sem_unfold. rewrite sem_unfold.
    right. rewrite <- cfold_stepD_correct. apply CIH.
  - constructor. fold (bind d (sem CFG)).
    fold (bind d (sem (cfold CFG))). right; eapply CIH.
  - constructor. destruct m.
    + simpl. constructor. intro. right.
      fold (bind (k a) (sem CFG)). fold (bind (k a) (sem (cfold CFG))).
      eapply CIH.
    + simpl. constructor. intro. right.
      fold (bind (k dv) (sem CFG)). fold (bind (k dv) (sem (cfold CFG))).
      eapply CIH.
    + simpl. constructor. right.
      fold (bind k (sem CFG)). fold (bind k (sem (cfold CFG))).
      eapply CIH.
Qed.

Lemma CFG_cfold_sem_equiv : forall st CFG, d_equiv (sem CFG st) (sem (cfold CFG) st).
Proof.
  intros. repeat (rewrite sem_unfold). rewrite <- cfold_stepD_correct.
  eapply CFG_cfold_bind_equiv.
Qed.

Theorem CFG_equiv_cfold : forall CFG, CFG_equiv CFG (cfold CFG).
Proof.
  intros. unfold CFG_equiv. rewrite <- cfold_init_state.
  apply CFG_cfold_sem_equiv.
Qed.