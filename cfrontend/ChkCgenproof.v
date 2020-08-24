(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for expression simplification. *)

Require Import FunInd.
Require Import Coqlib Maps Errors Integers.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Ctypes ChkCtypes Cop ChkCop ChkCsyntax Csyntax ChkCsem Csem ChkCstrategy Cstrategy.
Require Import ChkCgen ChkCgenspec.

(** ** Relational specification of the translation. *)

Definition match_prog (p: ChkCsyntax.program) (tp: Csyntax.program) :=
  match_program (fun ctx f tf => tr_fundef f tf) eq p tp
  /\ prog_types tp = prog_types p.

Lemma transf_program_match:
  forall p tp, transl_program p = OK tp -> match_prog p tp.
Proof.
  unfold transl_program; intros. monadInv H. split; auto.
  unfold program_of_program; simpl. destruct x; simpl.
  eapply match_transform_partial_program_contextual. eexact EQ.
  intros. apply transl_fundef_spec; auto.
Qed.

Section PRESERVATION.

  Variable prog: ChkCsyntax.program.
  Variable tprog: Csyntax.program.
  Hypothesis TRANSL: match_prog prog tprog.

  Let ge := ChkCsem.globalenv prog.
  Let tge := Csem.globalenv tprog.

  Lemma senv_preserved:
    Senv.equiv ge tge.
  Proof.
    Admitted.
(* (Genv.senv_match (proj1 TRANSL)). *)


  (** Anti-stuttering measure *)

(** There are some stuttering steps in the translation:
- The execution of [Sdo a] where [a] is side-effect free,
  which is three transitions in the source:
<<
    Sdo a, k  --->  a, Kdo k ---> rval v, Kdo k ---> Sskip, k
>>
  but the translation, which is [Sskip], makes no transitions.
- The reduction [Ecomma (Eval v) r2 --> r2].
- The reduction [Eparen (Eval v) --> Eval v] in a [For_effects] context.

The following measure decreases for these stuttering steps. *)

Fixpoint esize (a: ChkCsyntax.expr) : nat :=
  match a with
  | ChkCsyntax.Eloc _ _ _ => 1%nat
  | ChkCsyntax.Evar _ _ => 1%nat
  | ChkCsyntax.Ederef r1 _ => S(esize r1)
  | ChkCsyntax.Efield l1 _ _ => S(esize l1)
  | ChkCsyntax.Eval _ _ => O
  | ChkCsyntax.Evalof l1 _ => S(esize l1)
  | ChkCsyntax.Eaddrof l1 _ => S(esize l1)
  | ChkCsyntax.Eunop _ r1 _ => S(esize r1)
  | ChkCsyntax.Ebinop _ r1 r2 _ => S(esize r1 + esize r2)%nat
  | ChkCsyntax.Ecast r1 _ => S(esize r1)
  | ChkCsyntax.Eseqand r1 _ _ => S(esize r1)
  | ChkCsyntax.Eseqor r1 _ _ => S(esize r1)
  | ChkCsyntax.Econdition r1 _ _ _ => S(esize r1)
  | ChkCsyntax.Esizeof _ _ => 1%nat
  | ChkCsyntax.Ealignof _ _ => 1%nat
  | ChkCsyntax.Eassign l1 r2 _ => S(esize l1 + esize r2)%nat
  | ChkCsyntax.Eassignop _ l1 r2 _ _ => S(esize l1 + esize r2)%nat
  | ChkCsyntax.Epostincr _ l1 _ => S(esize l1)
  | ChkCsyntax.Ecomma r1 r2 _ => S(esize r1 + esize r2)%nat
  | ChkCsyntax.Ecall r1 rl2 _ => S(esize r1 + esizelist rl2)%nat
  | ChkCsyntax.Ebuiltin ef _ rl _ => S(esizelist rl)%nat
  | ChkCsyntax.Eparen r1 _ _ => S(esize r1)
  end

with esizelist (el: ChkCsyntax.exprlist) : nat :=
  match el with
  | ChkCsyntax.Enil => O
  | ChkCsyntax.Econs r1 rl2 => (esize r1 + esizelist rl2)%nat
  end.

Definition measure (st: ChkCsem.state) : nat :=
  match st with
  | ChkCsem.ExprState _ r _ _ _ => (esize r + 1)%nat
  | ChkCsem.State _ ChkCsyntax.Sskip _ _ _ => 0%nat
  | ChkCsem.State _ (ChkCsyntax.Sdo r) _ _ _ => (esize r + 2)%nat
  | ChkCsem.State _ (ChkCsyntax.Sifthenelse r _ _) _ _ _ => (esize r + 2)%nat
  | _ => 0%nat
  end.

Inductive match_ctx : (ChkCsyntax.expr -> ChkCsyntax.expr) -> (expr -> expr) -> Prop :=
| match_ctx_transl: forall C tC,
    (forall e te,
      tr_expr e te ->
      tr_expr (C e) (tC te)) ->
      match_ctx C tC.

Hint Constructors match_ctx.

Inductive match_cont : ChkCsem.cont -> cont -> Prop :=
  | match_Kstop:
      match_cont ChkCsem.Kstop Kstop
  | match_Kdo: forall k tk,
      match_cont k tk ->
      match_cont (ChkCsem.Kdo k) (Kdo tk)
  | match_Kseq: forall s k ts tk,
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (ChkCsem.Kseq s k) (Kseq ts tk)
  | match_Kifthenelse: forall s1 s2 k ts1 ts2 tk,
      tr_stmt s1 ts1 ->
      tr_stmt s2 ts2 ->
      match_cont k tk ->
      match_cont (ChkCsem.Kifthenelse s1 s2 k)
                 (Kifthenelse ts1 ts2 tk)
  | match_Kwhile1: forall e te s ts k tk,
      tr_expr e te ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (ChkCsem.Kwhile1 e s k)
                 (Kwhile1 te ts tk)
  | match_Kwhile2: forall e te s ts k tk,
      tr_expr e te ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (ChkCsem.Kwhile2 e s k)
                 (Kwhile2 te ts tk)
  | match_Kdowhile1: forall e te s ts k tk,
      tr_expr e te ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (ChkCsem.Kdowhile1 e s k)
                 (Kdowhile1 te ts tk)
  | match_Kdowhile2: forall e te s ts k tk,
      tr_expr e te ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (ChkCsem.Kdowhile2 e s k)
                 (Kdowhile2 te ts tk)
  | match_Kfor2: forall e te s1 ts1 s2 ts2 k tk,
      tr_expr e te ->
      tr_stmt s1 ts1 ->
      tr_stmt s2 ts2 ->
      match_cont k tk ->
      match_cont (ChkCsem.Kfor2 e s1 s2 k)
                 (Kfor2 te ts1 ts2 tk)
  | match_Kfor3: forall e te s1 ts1 s2 ts2 k tk,
      tr_expr e te ->
      tr_stmt s1 ts1 ->
      tr_stmt s2 ts2 ->
      match_cont k tk ->
      match_cont (ChkCsem.Kfor3 e s1 s2 k)
                 (Kfor3 te ts1 ts2 tk)
  | match_Kfor4: forall e te s1 ts1 s2 ts2 k tk,
      tr_expr e te ->
      tr_stmt s1 ts1 ->
      tr_stmt s2 ts2 ->
      match_cont k tk ->
      match_cont (ChkCsem.Kfor4 e s1 s2 k)
                 (Kfor4 te ts1 ts2 tk)
  | match_Kswitch1: forall ss tss k tk,
      tr_lblstmts ss tss ->
      match_cont k tk ->
      match_cont (ChkCsem.Kswitch1 ss k)
                 (Kswitch1 tss tk)
  | match_Kswitch2: forall k tk,
      match_cont k tk ->
      match_cont (ChkCsem.Kswitch2 k)
                 (Kswitch2 tk)
  | match_Kreturn: forall k tk,
      match_cont k tk ->
      match_cont (ChkCsem.Kreturn k)
                 (Kreturn tk)
  | match_Kcall: forall f tf e C tC t k tk,
      tr_function f tf ->
      match_ctx C tC ->
      match_cont k tk ->
      match_cont (ChkCsem.Kcall f e C t k)
                 (Kcall tf e tC t tk).

Hint Constructors match_cont.

Inductive match_states: ChkCsem.state -> state -> Prop :=
| match_regstates: forall f tf s ts k tk e m,
    tr_function f tf ->
    tr_stmt s ts ->
    match_cont k tk ->
      match_states (ChkCsem.State f s k e m)
                   (State tf ts tk e m)
| match_exprstates: forall f tf e te k tk env m,
    tr_function f tf ->
    tr_expr e te ->
    match_cont k tk ->
      match_states (ChkCsem.ExprState f e k env m)
                   (ExprState tf te tk env m)
| match_callstates: forall fd tfd args k tk m,
    tr_fundef fd tfd ->
    match_cont k tk ->
    match_states (ChkCsem.Callstate fd args k m)
                 (Csem.Callstate tfd args tk m)
| match_returnstates: forall res k tk m,
    match_cont k tk ->
    match_states (ChkCsem.Returnstate res k m)
                 (Csem.Returnstate res tk m)
| match_stuckstates:
    match_states ChkCsem.Stuckstate Csem.Stuckstate.

Hint Constructors match_states.

Hint Constructors sstep.
Hint Constructors estep.
Hint Constructors tr_stmt.
Hint Constructors tr_expr.

Lemma transl_not_skip:
  forall a a',
    a <> ChkCsyntax.Sskip ->
    tr_stmt a a' ->
    a' <> Csyntax.Sskip.
Proof.
  intros.
  induction H0; try discriminate.
  destruct H. reflexivity.
Qed.

Hint Resolve transl_not_skip.

Lemma transl_mem:
  forall m e m',
    Mem.free_list m (ChkCsem.blocks_of_env ge e) = Some m' ->
    Mem.free_list m (Csem.blocks_of_env tge e) = Some m'.
Proof.
Admitted.

Hint Resolve transl_mem.

Lemma transl_f_cast:
  forall v1 ty f tf m v2,
    tr_function f tf ->
    sem_cast v1 ty (ChkCsyntax.fn_return f) m = Some v2 ->
    sem_cast v1 ty (Csyntax.fn_return tf) m = Some v2.
Proof.
Admitted.

Hint Resolve transl_f_cast.

Lemma transl_call_cont:
  forall k tk,
    match_cont k tk ->
    match_cont (ChkCsem.call_cont k) (Csem.call_cont tk).
Proof.
  induction 1; try simpl; eauto.
Qed.

Hint Resolve transl_call_cont.

Lemma transl_fn_body:
  forall f tf,
    tr_function f tf ->
    tr_stmt (ChkCsyntax.fn_body f) (Csyntax.fn_body tf).
Proof.
  destruct 1. assumption.
Qed.

Hint Resolve transl_fn_body.

Lemma transl_is_call_cont:
  forall k tk,
    match_cont k tk ->
    ChkCsem.is_call_cont k ->
    is_call_cont tk.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve transl_is_call_cont.

Lemma transl_lblstmts:
  forall n ss tss,
    tr_lblstmts ss tss ->
    tr_stmt (ChkCsem.seq_of_labeled_statement (ChkCsem.select_switch n ss))
            (seq_of_labeled_statement (select_switch n tss)).
Proof.
Admitted.

Hint Resolve transl_lblstmts.

Lemma transl_find_label:
  forall lbl f tf k tk s' k',
    tr_function f tf ->
    match_cont k tk ->
    ChkCsem.find_label
      lbl (ChkCsyntax.fn_body f) (ChkCsem.call_cont k) = Some (s', k') ->
    exists ts' tk', find_label lbl (fn_body tf) (call_cont tk) = Some (ts', tk') /\
               tr_stmt s' ts' /\ match_cont k' tk'.
Proof.
Admitted.

Hint Resolve transl_find_label.

Lemma estep_simulation:
  forall S1 t S2, ChkCstrategy.estep ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  exists S2', Cstrategy.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
Admitted.

Lemma transl_list_norepet:
  forall f tf,
    tr_function f tf ->
    list_norepet
      (ChkCsyntax.var_names (ChkCsyntax.fn_params f) ++
                            ChkCsyntax.var_names (ChkCsyntax.fn_vars f)) ->
    list_norepet (var_names (fn_params tf) ++ var_names (fn_vars tf)).
Proof.
  intros.
  destruct H.
  destruct f.
  simpl in *.
  rewrite H3.
  rewrite H4.
  apply H0.
Qed.

Hint Resolve transl_list_norepet.

Lemma transl_variables:
  forall f tf m1 e m2 vargs m3,
    tr_function f tf ->
    ChkCsem.alloc_variables ge ChkCsem.empty_env m1
                            (ChkCsyntax.fn_params f ++ ChkCsyntax.fn_vars f) e m2 ->
    ChkCsem.bind_parameters ge e m2 (ChkCsyntax.fn_params f) vargs m3 ->
    exists trm2,
      alloc_variables tge empty_env m1 (fn_params tf ++ fn_vars tf) e trm2 /\
      bind_parameters tge e trm2 (fn_params tf) vargs m3.
Proof.
Admitted.

Lemma transl_external:
  forall ef vargs m t vres m',
    external_call ef ge vargs m t vres m' ->
    external_call ef tge vargs m t vres m'.
Proof.
Admitted.

Hint Resolve transl_external.

Lemma sstep_simulation:
  forall S1 t S2, ChkCsem.sstep ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  exists S2', Cstrategy.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  - inv H6. econstructor. split; try right; eauto.
  - inv H6. inv H7. econstructor. split; try right; eauto.
  - inv H6. econstructor. split; try right; eauto.
  - inv H6. inv H7. econstructor. split; try right; eauto.
  - inv H6. inv H7. econstructor. split; try right; eauto.
  - inv H6. inv H7. econstructor. split; try right; eauto.
  - inv H6. econstructor. split; try right; eauto.
  - inv H7. inv H8. destruct b; econstructor; split; try right; eauto.
  - inv H6. econstructor. split; try right; eauto.
  - inv H7. inv H8. econstructor. split; try right; eauto.
  - inv H7. inv H8. econstructor. split; try right; eauto.
  - inv H; inv H7; inv H8; econstructor; split; try right; eauto.
  - inv H6. inv H7. econstructor; split; try right; eauto.
  - inv H6. econstructor. split; try right; eauto.
  - inv H; inv H7; inv H8; econstructor; split; try right; eauto.
  - inv H7. inv H8. econstructor. split; try right; eauto.
  - inv H7. inv H8. econstructor. split; try right; eauto.
  - inv H6. inv H7. econstructor. split; try right; eauto.
  - inv H7. econstructor. split; try right; eauto.
  - inv H6. inv H3. econstructor. split; try right; eauto.
  - inv H7. inv H8. econstructor. split; try right; eauto.
  - inv H7. inv H8. econstructor. split; try right; eauto.
  - inv H; inv H7; inv H8; econstructor; split; try right; eauto.
  - inv H6. inv H7. econstructor. split; try right; eauto.
  - inv H6. inv H7. econstructor. split; try right; eauto.
  - inv H7. econstructor. split; try right; eauto.
  - inv H6. econstructor. split; try right; eauto.
  - inv H8. inv H9. econstructor. split; try right; eauto.
  - inv H8. econstructor. split; try right; eauto.
  - inv H6. econstructor. split; try right; eauto.
  - inv H7. inv H8. econstructor. split; try right; eauto.
  - inv H; inv H7; inv H8; econstructor; split; try right; eauto.
  - inv H6. inv H7. econstructor. split; try right; eauto.
  - inv H6. econstructor. split; try right; eauto.
  - apply transl_find_label with (tf := tf) (tk := tk) in H.
    inv H. inv H0. inv H. inv H1. inv H7.
    econstructor; split; try right; eauto. assumption. assumption.
  - inv H7. econstructor. split; try right; eauto.
    pose proof transl_variables.
    specialize (H2 f tf m e m1 vargs m2 H3 H0 H1).
    inv H2. inv H4.
    econstructor. eauto.
    apply H2.
    apply H5.
  - inv H5. econstructor. split; try right; eauto.
  - inv H3. econstructor. split; try right; eauto.
    inv H7.
    econstructor. assumption.
    apply H. econstructor. assumption.
Qed.

Lemma simulation:
  forall S1 t S2, ChkCstrategy.step ge S1 t S2 ->
             forall S1' (MS: match_states S1 S1'),
             exists S2', Cstrategy.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  intros S1 t S2 STEP.
  destruct STEP.
  apply estep_simulation; auto.
  apply sstep_simulation; auto.
Qed.

Lemma transl_initial_states:
  forall S,
    ChkCsem.initial_state prog S ->
    exists S', Csem.initial_state tprog S' /\ match_states S S'.
Proof.
Admitted.

Lemma transl_final_states:
  forall S S' r,
    match_states S S' -> ChkCsem.final_state S r -> Csem.final_state S' r.
Proof.
Admitted.


Theorem transl_program_correct:
  forward_simulation (ChkCstrategy.semantics prog) (Cstrategy.semantics tprog).
Proof.
  eapply forward_simulation_step.
  eapply senv_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  exact simulation.
Qed.

End PRESERVATION.

Instance TransfChkCGenLink : TransfLink match_prog.
Proof.
  red; intros. eapply Ctypes.link_match_program; eauto.
  - intros.
    Local Transparent Linker_fundef.
    simpl in *; unfold link_fundef in *. inv H3; inv H4; try discriminate.
    destruct ef; inv H2. exists (Internal tf); split; auto. constructor; auto.
    destruct ef; inv H2. exists (Internal tf); split; auto. constructor; auto.
    destruct (external_function_eq ef ef0 && typelist_eq targs targs0 &&
                                   type_eq tres tres0 && calling_convention_eq cconv cconv0); inv H2.
    exists (External ef targs tres cconv); split; auto. constructor.
Qed.
