Require Import paco.
Require Import Bool String Ascii List.
Require Import Omega.
Require Import Vellvm.MiniLLVM_nop.
Require Import Vellvm.Util Vellvm.Misc.

Import ListNotations.

Set Implicit Arguments.

Definition remove_nops_block_instrs (b : list (instr_id * instr)) :=
  filter (fun x => match snd x with
                     | INSTR_Nop => true
                     | _ => false
                   end) b.

Definition remove_nops_block b :=
  {| blk_id := blk_id b;
     blk_instrs := remove_nops_block_instrs (blk_instrs b);
     blk_term_id := blk_term_id b;
     blk_term := blk_term b
  |}.

Definition remove_nops_def d :=
  {| df_prototype := df_prototype d;
     df_args := df_args d;
     df_instrs := map remove_nops_block (df_instrs d)
  |}.

Definition remove_nops_entity e :=
  match e with
    | TLE_Definition d => TLE_Definition (remove_nops_def d)
  end.

Definition remove_nops_entities es :=
  map remove_nops_entity es.

Lemma remove_nops_preserves_wf :
  forall tles p, Some p = entities_to_init tles ->
                 exists p', Some p' = entities_to_init (remove_nops_entities tles).
Proof.
  intros. induction tles; try solve [inversion H].
  simpl in H. destruct a; simpl.
  destruct (raw_id_beq (dc_name (df_prototype defn)) (Name "main")); eauto.
  destruct (df_instrs defn); try solve [inversion H].
  simpl. destruct (remove_nops_block_instrs (blk_instrs b)); eapply ex_intro; eauto.
Qed.

Theorem remove_nops_block_scope :
  forall b p instrs,
    Some b =
    List.find (fun b : block => raw_id_beq (bn p) (blk_id b))
         (map remove_nops_block instrs) ->
    exists b', Some b' = List.find (fun b : block => raw_id_beq (bn p) (blk_id b)) instrs /\ b = remove_nops_block b'.
Proof.
  intros. induction instrs; try solve [simpl in H; inversion H].
  simpl in *. destruct (raw_id_beq (bn p) (blk_id a)); try (eapply IHinstrs; eapply H).
  exists a. inversion H; split; eauto.
Qed.

(* Removing nops doesn't affect commands that aren't removed *)
Theorem remove_nops_cmd_from_block :
  forall p b b' x,
    remove_nops_block b = b' ->
    Some x = cmd_from_block (ins p) (fn p) (bn p) (blk_term_id b') (blk_instrs b') ->
    Some x = cmd_from_block (ins p) (fn p) (bn p) (blk_term_id b) (blk_instrs b).
Proof.
  intros. unfold remove_nops_block in *. subst; simpl in *.
  destruct b; simpl in *.
  induction blk_instrs. simpl in *; inversion H0.
  simpl in *. destruct a; simpl in *.
  destruct i0; simpl in *. apply IHblk_instrs in H0.
  (* Need uniqueness here *)
Admitted.

(* Intuitively,  if something is removed it is a NOP *)
Theorem remove_nops_missing :
  forall p b b' x,
    remove_nops_block b = b' ->
    Some x = cmd_from_block (ins p) (fn p) (bn p) (blk_term_id b) (blk_instrs b) ->
    None = cmd_from_block (ins p) (fn p) (bn p) (blk_term_id b') (blk_instrs b') ->
    exists p', x = Step INSTR_Nop p'.
Proof.
  intros. destruct b; simpl in *. generalize dependent b'.
  induction blk_instrs; try solve [simpl in H0; inversion H0].
  intro. destruct a.
  simpl in H0. destruct (instr_id_eq_dec (ins p) i).
  - intros. eapply IHblk_instrs; eauto.
    + destruct i0; admit.
    + admit.
  - intros.
    eapply IHblk_instrs; eauto.
    destruct i0; eauto. simpl. unfold remove_nops_block in H. simpl in H.
    subst. destruct i0; eauto. simpl in H1.
    destruct (instr_id_eq_dec (ins p) i); eauto. inversion H1.
Admitted.

(* We also need a property that says something like:
   If we remove nops and encounter something missing, we eventually
   reach the command that we stepped to in the block with the NOPs 
   removed, and only encountered NOPs in between.

   Or: if the nop-removed cfg and regular cfg step to different things
    from some state, then the regular cfg will eventually step to the
    same state as the nop-removed cfg did after one step.

   We don't want to state this as a coinductive property because it
    inherently needs to be finite.
   I'm not sure exactly how to phrase this.
 *)
CoFixpoint step_until_id id CFG (s : state) : D state :=
  let '(p, e, c) := s in
  if instr_id_eq_dec id (ins p) then
    stepD CFG s
  else bind (stepD CFG s) (step_until_id id CFG).

(* Intuitively this is true because of the above lemma: that we only 
   encounter NOPs *)
Theorem remove_nops_finite_missing :
  forall p p' tles CFG CFG' st next e c,
    Some p = entities_to_init tles ->
    Some p' = entities_to_init (remove_nops_entities tles) ->
    TLE_to_cfg tles = Some CFG ->
    TLE_to_cfg (remove_nops_entities tles) = Some CFG' ->
    stepD CFG' st = Ret (next, e, c) ->
    d_equiv (stepD CFG' st) (step_until_id (ins next) CFG st).
Proof.
Abort.

(* Then the general idea of the proof would be that we destruct
   the (code cfg). The result would then be either None or Some.
   In the some case we can remove the thing that is the same and 
   then apply the coinductive hypothesis.
   In the None case, we use the remove_nops_finite_missing lemma to
   say that we eventually reach the same state as on the NOP-removed
   case.

   A similar argument should apply in the constant propagation case
   except you need to thread some more state through (information about
   which constants were propagated away).
 *)
  
Theorem remove_nops_scope :
  forall p p' p'' tles CFG CFG' cmd,
    Some p' = entities_to_init tles ->
    Some p'' = entities_to_init (remove_nops_entities tles) ->
    TLE_to_cfg tles = Some CFG ->
    TLE_to_cfg (remove_nops_entities tles) = Some CFG' ->
    code CFG' p = Some cmd -> code CFG p = Some cmd.
Proof.
  intros. unfold code in *; destruct CFG; destruct CFG'; simpl in *.
  unfold TLE_to_cfg in *. rewrite <- H in H1; rewrite <- H0 in H2.
  simpl in *. inversion H1; clear H1; inversion H2; clear H2.
  rewrite <- H9 in H3. clear H7 H8 H10 H11 H H0 H5 H4.
  generalize dependent code0. generalize dependent code. induction tles.
  - intros. unfold entities_to_code in H3; simpl in H3. inversion H3. 
  - intros. simpl. simpl in H3. destruct a; simpl in H3.
    destruct (raw_id_beq (dc_name (df_prototype defn)) (fn p)).
    + remember (find (fun b => raw_id_beq (bn p) (blk_id b)) (map remove_nops_block (df_instrs defn))).
      destruct o; simpl in H3; try (solve [inversion H3]).
      assert (Heqo' := Heqo); eauto.
      eapply remove_nops_block_scope in Heqo'.
      destruct Heqo' as [b']. destruct H. rewrite <- H; simpl.
      admit.
      
    + eapply IHtles; eauto.
Abort.
      
Theorem remove_nops_equiv :
  forall p p' p'' cont env tles CFG CFG',
    Some p' = entities_to_init tles ->
    Some p'' = entities_to_init (remove_nops_entities tles) ->
    TLE_to_cfg tles = Some CFG ->
    TLE_to_cfg (remove_nops_entities tles) = Some CFG' ->
    code CFG' p <> None ->
    d_equiv (bind (stepD CFG (p, env, cont)) (sem CFG))
            (bind (stepD CFG' (p, env, cont)) (sem CFG')).
Proof.
  intros. pcofix CIH. pfold. unfold TLE_to_cfg in *.
  rewrite <- H in H1. rewrite <- H0 in H2. simpl in *.
  inversion H1; clear H1. inversion H2; clear H2.
 
  unfold stepD.
  
Abort.

Theorem remove_nops_equiv :
  forall st tles CFG, TLE_to_cfg tles = Some CFG ->
                      exists cfg', TLE_to_cfg (remove_nops_entities tles) = Some cfg' /\
                                   d_equiv (sem CFG st) (sem cfg' st).
Proof.
  intros. unfold TLE_to_cfg in H. remember (entities_to_init tles).
  destruct o; simpl in H; try solve [inversion H].
  assert (Heqo' := Heqo); eauto.
  eapply remove_nops_preserves_wf in Heqo'; destruct Heqo' as [p'].
  unfold TLE_to_cfg. rewrite <- H0; simpl.
  eapply ex_intro; split; eauto.
  inversion H; simpl; eauto. clear H. clear H2.
  (* We do need at least some properties of the state here *)
  rewrite sem_unfold. rewrite sem_unfold.
  pcofix CIH.
Abort.