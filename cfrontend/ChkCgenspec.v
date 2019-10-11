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

(** Relational specification of expression simplification. *)

Require Import Coqlib Maps Errors Integers Floats.
Require Import AST Linking Memory.
Require Import Ctypes Cop ChkCsyntax Csyntax ChkCgen.

Section SPEC.

Local Open Scope gensym_monad_scope.

(** * Relational specification of the translation. *)

(** ** Translation of expressions *)

(** This specification covers:
- all cases of [transl_lvalue] and [transl_rvalue];
- two additional cases for [Csyntax.Eparen], so that reductions of [Csyntax.Econdition]
  expressions are properly tracked;
- three additional cases allowing [Csyntax.Eval v] C expressions to match
  any Clight expression [a] that evaluates to [v] in any environment
  matching the given temporary environment [le].
*)

Inductive tr_expr: ChkCsyntax.expr -> expr -> Prop :=
| tr_val: forall v ty,
    tr_expr (ChkCsyntax.Eval v ty) (Eval v ty)
| tr_var: forall x ty,
    tr_expr (ChkCsyntax.Evar x ty) (Evar x ty)
| tr_field: forall l tl f ty,
    tr_expr l tl ->
    tr_expr (ChkCsyntax.Efield l f ty) (Efield tl f ty)
| tr_valof: forall l tl ty,
    tr_expr l tl ->
    tr_expr (ChkCsyntax.Evalof l ty) (Evalof tl ty)
| tr_deref: forall r tr ty,
    tr_expr r tr ->
    tr_expr (ChkCsyntax.Ederef r ty) (Ederef tr ty)
| tr_addrof: forall l tl ty,
    tr_expr l tl ->
    tr_expr (ChkCsyntax.Eaddrof l ty) (Eaddrof tl ty)
| tr_unop: forall op r tr ty,
    tr_expr r tr ->
    tr_expr (ChkCsyntax.Eunop op r ty) (Eunop op tr ty)
| tr_binop: forall op r1 tr1 r2 tr2 ty,
    tr_expr r1 tr1 ->
    tr_expr r2 tr2 ->
    tr_expr (ChkCsyntax.Ebinop op r1 r2 ty) (Ebinop op tr1 tr2 ty)
| tr_cast: forall r tr ty,
    tr_expr r tr ->
    tr_expr (ChkCsyntax.Ecast r ty) (Ecast tr ty)
| tr_seqand: forall r1 tr1 r2 tr2 ty,
    tr_expr r1 tr1 ->
    tr_expr r2 tr2 ->
    tr_expr (ChkCsyntax.Eseqand r1 r2 ty) (Eseqand tr1 tr2 ty)
| tr_seqor: forall r1 tr1 r2 tr2 ty,
    tr_expr r1 tr1 ->
    tr_expr r2 tr2 ->
    tr_expr (ChkCsyntax.Eseqor r1 r2 ty) (Eseqor tr1 tr2 ty)
| tr_cond: forall r1 tr1 r2 tr2 r3 tr3 ty,
    tr_expr r1 tr1 ->
    tr_expr r2 tr2 ->
    tr_expr r3 tr3 ->
    tr_expr (ChkCsyntax.Econdition r1 r2 r3 ty) (Econdition tr1 tr2 tr3 ty)
| tr_sizeof: forall ty' ty,
    tr_expr (ChkCsyntax.Esizeof ty' ty) (Esizeof ty' ty)
| tr_alignof: forall ty' ty,
    tr_expr (ChkCsyntax.Ealignof ty' ty) (Ealignof ty' ty)
| tr_assign: forall l tl r tr ty,
    tr_expr l tl ->
    tr_expr r tr ->
    tr_expr (ChkCsyntax.Eassign l r ty) (Eassign tl tr ty)
| tr_assignop: forall op l tl r tr tyres ty,
    tr_expr l tl ->
    tr_expr r tr ->
    tr_expr (ChkCsyntax.Eassignop op l r tyres ty) (Eassignop op tl tr tyres ty)
| tr_postincr: forall id l tl ty,
    tr_expr l tl ->
    tr_expr (ChkCsyntax.Epostincr id l ty) (Epostincr id tl ty)
| tr_comma: forall r1 tr1 r2 tr2 ty,
    tr_expr r1 tr1 ->
    tr_expr r2 tr2 ->
    tr_expr (ChkCsyntax.Ecomma r1 r2 ty) (Ecomma tr1 tr2 ty)
| tr_call: forall r1 tr1 rargs trargs ty,
    tr_expr r1 tr1 ->
    tr_exprlist rargs trargs ->
    tr_expr (ChkCsyntax.Ecall r1 rargs ty) (Ecall tr1 trargs ty)
| tr_builtin: forall ef tyargs rargs trargs ty,
    tr_exprlist rargs trargs ->
    tr_expr (ChkCsyntax.Ebuiltin ef tyargs rargs ty) (Ebuiltin ef tyargs trargs ty)
| tr_loc: forall b ofs ty,
    tr_expr (ChkCsyntax.Eloc b ofs ty) (Eloc b ofs ty)
| tr_paren: forall r tr tycast ty,
    tr_expr r tr ->
    tr_expr (ChkCsyntax.Eparen r tycast ty) (Eparen tr tycast ty)

with tr_exprlist: ChkCsyntax.exprlist -> exprlist -> Prop :=
| tr_nil:
    tr_exprlist ChkCsyntax.Enil Enil
| tr_cons: forall r1 tr1 rl trl,
    tr_expr r1 tr1 ->
    tr_exprlist rl trl ->
    tr_exprlist (ChkCsyntax.Econs r1 rl) (Econs tr1 trl).

Hint Constructors tr_expr.
Hint Constructors tr_exprlist.

Scheme expr_ind2 := Induction for ChkCsyntax.expr Sort Prop
  with exprlist_ind2 := Induction for ChkCsyntax.exprlist Sort Prop.
Combined Scheme expr_exprlist_ind from expr_ind2, exprlist_ind2.

Inductive tr_stmt: ChkCsyntax.statement -> statement -> Prop :=
  | tr_skip:
      tr_stmt ChkCsyntax.Sskip Sskip
  | tr_do: forall e te,
      tr_expr e te ->
      tr_stmt (ChkCsyntax.Sdo e) (Sdo te)
  | tr_seq: forall s1 s2 ts1 ts2,
      tr_stmt s1 ts1 ->
      tr_stmt s2 ts2 ->
      tr_stmt (ChkCsyntax.Ssequence s1 s2) (Ssequence ts1 ts2)
  | tr_ifthenelse: forall e te s1 ts1 s2 ts2,
      tr_expr e te ->
      tr_stmt s1 ts1 ->
      tr_stmt s2 ts2 ->
      tr_stmt (ChkCsyntax.Sifthenelse e s1 s2) (Sifthenelse te ts1 ts2)
  | tr_while: forall e te s1 ts1,
      tr_expr e te ->
      tr_stmt s1 ts1 ->
      tr_stmt (ChkCsyntax.Swhile e s1) (Swhile te ts1)
  | tr_dowhile: forall e te s1 ts1,
      tr_expr e te ->
      tr_stmt s1 ts1 ->
      tr_stmt (ChkCsyntax.Sdowhile e s1) (Sdowhile te ts1)
  | tr_for: forall s1 ts1 e2 te2 s3 ts3 s4 ts4,
      tr_stmt s1 ts1 ->
      tr_expr e2 te2 ->
      tr_stmt s3 ts3 ->
      tr_stmt s4 ts4 ->
      tr_stmt (ChkCsyntax.Sfor s1 e2 s3 s4) (Sfor ts1 te2 ts3 ts4)
  | tr_break:
      tr_stmt ChkCsyntax.Sbreak Sbreak
  | tr_continue:
      tr_stmt ChkCsyntax.Scontinue Scontinue
  | tr_return_none:
      tr_stmt (ChkCsyntax.Sreturn None) (Sreturn None)
  | tr_return_some: forall e te,
      tr_expr e te ->
      tr_stmt (ChkCsyntax.Sreturn (Some e)) (Sreturn (Some te))
  | tr_switch: forall e te ls tls,
      tr_expr e te ->
      tr_lblstmts ls tls ->
      tr_stmt (ChkCsyntax.Sswitch e ls) (Sswitch te tls)
  | tr_label: forall lbl s ts,
      tr_stmt s ts ->
      tr_stmt (ChkCsyntax.Slabel lbl s) (Slabel lbl ts)
  | tr_goto: forall lbl,
      tr_stmt (ChkCsyntax.Sgoto lbl) (Sgoto lbl)

with tr_lblstmts: ChkCsyntax.labeled_statements -> labeled_statements -> Prop :=
  | tr_ls_nil:
      tr_lblstmts ChkCsyntax.LSnil LSnil
  | tr_ls_cons: forall c s ls ts tls,
      tr_stmt s ts ->
      tr_lblstmts ls tls ->
      tr_lblstmts (ChkCsyntax.LScons c s ls) (LScons c ts tls).

Hint Constructors tr_stmt.
Hint Constructors tr_lblstmts.

(** * Correctness proof with respect to the specification. *)

(** ** Properties of the monad *)

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B) (y: B) (z1 z3: generator) I,
  bind f g z1 = Res y z3 I ->
  exists x, exists z2, exists I1, exists I2,
  f z1 = Res x z2 I1 /\ g x z2 = Res y z3 I2.
Proof.
  intros until I. unfold bind. destruct (f z1).
  congruence.
  caseEq (g a g'); intros; inv H0.
  econstructor; econstructor; econstructor; econstructor; eauto.
Qed.

Remark bind2_inversion:
  forall (A B Csyntax: Type) (f: mon (A*B)) (g: A -> B -> mon Csyntax) (y: Csyntax) (z1 z3: generator) I,
  bind2 f g z1 = Res y z3 I ->
  exists x1, exists x2, exists z2, exists I1, exists I2,
  f z1 = Res (x1,x2) z2 I1 /\ g x1 x2 z2 = Res y z3 I2.
Proof.
  unfold bind2. intros.
  exploit bind_inversion; eauto.
  intros [[x1 x2] [z2 [I1 [I2 [P Q]]]]]. simpl in Q.
  exists x1; exists x2; exists z2; exists I1; exists I2; auto.
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (Res _ _ _ = Res _ _ _) =>
      inversion H; clear H; try subst
  | (@ret _ _ _ = Res _ _ _) =>
      inversion H; clear H; try subst
  | (@error _ _ _ = Res _ _ _) =>
      inversion H
  | (bind ?F ?G ?Z = Res ?X ?Z' ?I) =>
      let x := fresh "x" in (
      let z := fresh "z" in (
      let I1 := fresh "I" in (
      let I2 := fresh "I" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X Z Z' I H) as [x [z [I1 [I2 [EQ1 EQ2]]]]];
      clear H;
      try (monadInv1 EQ2)))))))
   | (bind2 ?F ?G ?Z = Res ?X ?Z' ?I) =>
      let x := fresh "x" in (
      let y := fresh "y" in (
      let z := fresh "z" in (
      let I1 := fresh "I" in (
      let I2 := fresh "I" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion _ _ _ F G X Z Z' I H) as [x [y [z [I1 [I2 [EQ1 EQ2]]]]]];
      clear H;
      try (monadInv1 EQ2))))))))
 end.

Ltac monadInv H :=
  match type of H with
  | (@ret _ _ _ = Res _ _ _) => monadInv1 H
  | (@error _ _ _ = Res _ _ _) => monadInv1 H
  | (bind ?F ?G ?Z = Res ?X ?Z' ?I) => monadInv1 H
  | (bind2 ?F ?G ?Z = Res ?X ?Z' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.
(*
(** ** Freshness and separation properties. *)

Definition within (id: ident) (g1 g2: generator) : Prop :=
  Ple (gen_next g1) id /\ Plt id (gen_next g2).

Lemma gensym_within:
  forall ty g1 id g2 I,
  gensym ty g1 = Res id g2 I -> within id g1 g2.
Proof.
  intros. monadInv H. split. apply Ple_refl. apply Plt_succ.
Qed.

Lemma within_widen:
  forall id g1 g2 g1' g2',
  within id g1 g2 ->
  Ple (gen_next g1') (gen_next g1) ->
  Ple (gen_next g2) (gen_next g2') ->
  within id g1' g2'.
Proof.
  intros. destruct H. split.
  eapply Ple_trans; eauto.
  eapply Plt_Ple_trans; eauto.
Qed.

Definition contained (l: list ident) (g1 g2: generator) : Prop :=
  forall id, In id l -> within id g1 g2.

Lemma contained_nil:
  forall g1 g2, contained nil g1 g2.
Proof.
  intros; red; intros; contradiction.
Qed.

Lemma contained_widen:
  forall l g1 g2 g1' g2',
  contained l g1 g2 ->
  Ple (gen_next g1') (gen_next g1) ->
  Ple (gen_next g2) (gen_next g2') ->
  contained l g1' g2'.
Proof.
  intros; red; intros. eapply within_widen; eauto.
Qed.

Lemma contained_cons:
  forall id l g1 g2,
  within id g1 g2 -> contained l g1 g2 -> contained (id :: l) g1 g2.
Proof.
  intros; red; intros. simpl in H1; destruct H1. subst id0. auto. auto.
Qed.

Lemma contained_app:
  forall l1 l2 g1 g2,
  contained l1 g1 g2 -> contained l2 g1 g2 -> contained (l1 ++ l2) g1 g2.
Proof.
  intros; red; intros. destruct (in_app_or _ _ _ H1); auto.
Qed.

Lemma contained_disjoint:
  forall g1 l1 g2 l2 g3,
  contained l1 g1 g2 -> contained l2 g2 g3 -> list_disjoint l1 l2.
Proof.
  intros; red; intros. red; intro; subst y.
  exploit H; eauto. intros [A B]. exploit H0; eauto. intros [Csyntax D].
  elim (Plt_strict x). apply Plt_Ple_trans with (gen_next g2); auto.
Qed.

Lemma contained_notin:
  forall g1 l g2 id g3,
  contained l g1 g2 -> within id g2 g3 -> ~In id l.
Proof.
  intros; red; intros. exploit H; eauto. intros [Csyntax D]. destruct H0 as [A B].
  elim (Plt_strict id). apply Plt_Ple_trans with (gen_next g2); auto.
Qed.

Definition dest_below (dst: destination) (g: generator) : Prop :=
  match dst with
  | For_set sd => Plt (sd_temp sd) g.(gen_next)
  | _ => True
  end.

Remark dest_for_val_below: forall g, dest_below For_val g.
Proof. intros; simpl; auto. Qed.

Remark dest_for_effect_below: forall g, dest_below For_effects g.
Proof. intros; simpl; auto. Qed.

Lemma dest_for_set_seqbool_val:
  forall tmp ty g1 g2,
  within tmp g1 g2 -> dest_below (For_set (sd_seqbool_val tmp ty)) g2.
Proof.
  intros. destruct H. simpl. auto.
Qed.

Lemma dest_for_set_seqbool_set:
  forall sd ty g, dest_below (For_set sd) g -> dest_below (For_set (sd_seqbool_set ty sd)) g.
Proof.
  intros. assumption.
Qed.

Lemma dest_for_set_condition_val:
  forall tmp tycast ty g1 g2, within tmp g1 g2 -> dest_below (For_set (SDbase tycast ty tmp)) g2.
Proof.
  intros. destruct H. simpl. auto.
Qed.

Lemma dest_for_set_condition_set:
  forall sd tmp tycast ty g1 g2, dest_below (For_set sd) g2 -> within tmp g1 g2 -> dest_below (For_set (SDcons tycast ty tmp sd)) g2.
Proof.
  intros. destruct H0. simpl. auto.
Qed.

Lemma sd_temp_notin:
  forall sd g1 g2 l, dest_below (For_set sd) g1 -> contained l g1 g2 -> ~In (sd_temp sd) l.
Proof.
  intros. simpl in H. red; intros. exploit H0; eauto. intros [A B].
  elim (Plt_strict (sd_temp sd)). apply Plt_Ple_trans with (gen_next g1); auto.
Qed.

Lemma dest_below_le:
  forall dst g1 g2,
  dest_below dst g1 -> Ple g1.(gen_next) g2.(gen_next) -> dest_below dst g2.
Proof.
  intros. destruct dst; simpl in *; auto. eapply Plt_Ple_trans; eauto.
Qed.

Hint Resolve gensym_within within_widen contained_widen
             contained_cons contained_app contained_disjoint
             contained_notin contained_nil
             dest_for_set_seqbool_val dest_for_set_seqbool_set
             dest_for_set_condition_val dest_for_set_condition_set
             sd_temp_notin dest_below_le
             incl_refl incl_tl incl_app incl_appl incl_appr incl_same_head
             in_eq in_cons
             Ple_trans Ple_refl: gensym.

Local Hint Resolve dest_for_val_below dest_for_effect_below : core.

(** ** Correctness of the translation functions *)

Lemma finish_meets_spec_1:
  forall dst sl a sl' a',
  finish dst sl a = (sl', a') -> sl' = sl ++ final dst a.
Proof.
  intros. destruct dst; simpl in *; inv H. apply app_nil_end. apply app_nil_end. auto.
Qed.

Lemma finish_meets_spec_2:
  forall dst sl a sl' a',
  finish dst sl a = (sl', a') -> a' = a.
Proof.
  intros. destruct dst; simpl in *; inv H; auto.
Qed.

Ltac UseFinish :=
  match goal with
  | [ H: finish _ _ _ = (_, _) |- _ ] =>
      try (rewrite (finish_meets_spec_2 _ _ _ _ _ H));
      try (rewrite (finish_meets_spec_1 _ _ _ _ _ H));
      repeat rewrite app_ass
  end.

(*
Fixpoint add_set_dest (sd: set_destination) (tmps: list ident) :=
  match sd with
  | SDbase ty tmp => tmp :: tmps
  | SDcons ty tmp sd' => tmp :: add_set_dest sd' tmps
  end.
*)

Definition add_dest (dst: destination) (tmps: list ident) :=
  match dst with
  | For_set sd => sd_temp sd :: tmps
  | _ => tmps
  end.

Lemma add_dest_incl:
  forall dst tmps, incl tmps (add_dest dst tmps).
Proof.
  intros. destruct dst; simpl; eauto with coqlib.
Qed.

Lemma tr_expr_add_dest:
  forall le dst r sl a tmps,
  tr_expr le dst r sl a tmps ->
  tr_expr le dst r sl a (add_dest dst tmps).
Proof.
  intros. apply tr_expr_monotone with tmps; auto. apply add_dest_incl.
Qed.

Lemma transl_valof_meets_spec:
  forall ty a g sl b g' I,
  transl_valof ty a g = Res (sl, b) g' I ->
  exists tmps, tr_rvalof ty a sl b tmps /\ contained tmps g g'.
Proof.
  unfold transl_valof; intros.
  destruct (type_is_volatile ty) eqn:?; monadInv H.
  exists (x :: nil); split; eauto with gensym. econstructor; eauto with coqlib.
  exists (@nil ident); split; eauto with gensym. constructor; auto.
Qed.

Scheme expr_ind2 := Induction for Csyntax.expr Sort Prop
  with exprlist_ind2 := Induction for Csyntax.exprlist Sort Prop.
Combined Scheme expr_exprlist_ind from expr_ind2, exprlist_ind2.

Lemma transl_meets_spec:
   (forall r dst g sl a g' I,
    transl_expr dst r g = Res (sl, a) g' I ->
    dest_below dst g ->
    exists tmps, (forall le, tr_expr le dst r sl a (add_dest dst tmps)) /\ contained tmps g g')
  /\
   (forall rl g sl al g' I,
    transl_exprlist rl g = Res (sl, al) g' I ->
    exists tmps, (forall le, tr_exprlist le rl sl al tmps) /\ contained tmps g g').
Proof.
  apply expr_exprlist_ind; simpl add_dest; intros.
(* val *)
  simpl in H. destruct v; monadInv H; exists (@nil ident); split; auto with gensym.
Opaque makeif.
  intros. destruct dst; simpl in *; inv H2.
    constructor. auto. intros; constructor.
    constructor.
    constructor. auto. intros; constructor.
  intros. destruct dst; simpl in *; inv H2.
    constructor. auto. intros; constructor.
    constructor.
    constructor. auto. intros; constructor.
  intros. destruct dst; simpl in *; inv H2.
    constructor. auto. intros; constructor.
    constructor.
    constructor. auto. intros; constructor.
  intros. destruct dst; simpl in *; inv H2.
    constructor. auto. intros; constructor.
    constructor.
    constructor. auto. intros; constructor.
(* var *)
  monadInv H; econstructor; split; auto with gensym. UseFinish. constructor.
(* field *)
  monadInv H0. exploit H; eauto. auto. intros [tmp [A B]]. UseFinish.
  econstructor; split; eauto. intros; apply tr_expr_add_dest. constructor; auto.
(* valof *)
  monadInv H0. exploit H; eauto. intros [tmp1 [A B]].
  exploit transl_valof_meets_spec; eauto. intros [tmp2 [Csyntax D]]. UseFinish.
  exists (tmp1 ++ tmp2); split.
  intros; apply tr_expr_add_dest. econstructor; eauto with gensym.
  eauto with gensym.
(* deref *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish.
  econstructor; split; eauto. intros; apply tr_expr_add_dest. constructor; auto.
(* addrof *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish.
  econstructor; split; eauto. intros; apply tr_expr_add_dest. econstructor; eauto.
(* unop *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish.
  econstructor; split; eauto. intros; apply tr_expr_add_dest. constructor; auto.
(* binop *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [Csyntax D]]. UseFinish.
  exists (tmp1 ++ tmp2); split.
  intros; apply tr_expr_add_dest. econstructor; eauto with gensym.
  eauto with gensym.
(* cast *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish.
  econstructor; split; eauto. intros; apply tr_expr_add_dest. constructor; auto.
(* seqand *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  destruct dst; monadInv EQ0.
  (* for value *)
  exploit H0; eauto with gensym. intros [tmp2 [C D]].
  simpl add_dest in *.
  exists (x0 :: tmp1 ++ tmp2); split.
  intros; eapply tr_seqand_val; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply contained_cons. eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for effects *)
  exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
  simpl add_dest in *.
  exists (tmp1 ++ tmp2); split.
  intros; eapply tr_seqand_effects; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for set *)
  exploit H0; eauto with gensym. intros [tmp2 [C D]].
  simpl add_dest in *.
  exists (tmp1 ++ tmp2); split.
  intros; eapply tr_seqand_set; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply contained_app; eauto with gensym.
(* seqor *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  destruct dst; monadInv EQ0.
  (* for value *)
  exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
  simpl add_dest in *.
  exists (x0 :: tmp1 ++ tmp2); split.
  intros; eapply tr_seqor_val; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply contained_cons. eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for effects *)
  exploit H0; eauto with gensym. intros [tmp2 [C D]].
  simpl add_dest in *.
  exists (tmp1 ++ tmp2); split.
  intros; eapply tr_seqor_effects; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for set *)
  exploit H0; eauto with gensym. intros [tmp2 [C D]].
  simpl add_dest in *.
  exists (tmp1 ++ tmp2); split.
  intros; eapply tr_seqor_set; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply contained_app; eauto with gensym.
(* condition *)
  monadInv H2. exploit H; eauto. intros [tmp1 [A B]].
  destruct dst; monadInv EQ0.
  (* for value *)
  exploit H0; eauto with gensym. intros [tmp2 [C D]].
  exploit H1; eauto with gensym. intros [tmp3 [E F]].
  simpl add_dest in *.
  exists (x0 :: tmp1 ++ tmp2 ++ tmp3); split.
  simpl; intros; eapply tr_condition_val; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply contained_cons. eauto with gensym.
  apply contained_app. eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for effects *)
  exploit H0; eauto. intros [tmp2 [Csyntax D]].
  exploit H1; eauto. intros [tmp3 [E F]].
  simpl add_dest in *.
  exists (tmp1 ++ tmp2 ++ tmp3); split.
  intros; eapply tr_condition_effects; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for test *)
  exploit H0; eauto with gensym. intros [tmp2 [C D]].
  exploit H1; eauto 10 with gensym. intros [tmp3 [E F]].
  simpl add_dest in *.
  exists (x0 :: tmp1 ++ tmp2 ++ tmp3); split.
  intros; eapply tr_condition_set; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply contained_cons; eauto with gensym.
  apply contained_app; eauto with gensym.
  apply contained_app; eauto with gensym.
(* sizeof *)
  monadInv H. UseFinish.
  exists (@nil ident); split; auto with gensym. constructor.
(* alignof *)
  monadInv H. UseFinish.
  exists (@nil ident); split; auto with gensym. constructor.
(* assign *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [Csyntax D]].
  destruct dst; monadInv EQ2; simpl add_dest in *.
  (* for value *)
  exists (x1 :: tmp1 ++ tmp2); split.
  intros. eapply tr_assign_val with (dst := For_val); eauto with gensym.
  apply contained_cons. eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for effects *)
  exists (tmp1 ++ tmp2); split.
  econstructor; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for set *)
  exists (x1 :: tmp1 ++ tmp2); split.
  repeat rewrite app_ass. simpl.
  intros. eapply tr_assign_val with (dst := For_set sd); eauto with gensym.
  apply contained_cons. eauto with gensym.
  apply contained_app; eauto with gensym.
(* assignop *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [Csyntax D]].
  exploit transl_valof_meets_spec; eauto. intros [tmp3 [E F]].
  destruct dst; monadInv EQ3; simpl add_dest in *.
  (* for value *)
  exists (x2 :: tmp1 ++ tmp2 ++ tmp3); split.
  intros. eapply tr_assignop_val with (dst := For_val); eauto with gensym.
  apply contained_cons. eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for effects *)
  exists (tmp1 ++ tmp2 ++ tmp3); split.
  econstructor; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for set *)
  exists (x2 :: tmp1 ++ tmp2 ++ tmp3); split.
  repeat rewrite app_ass. simpl.
  intros. eapply tr_assignop_val with (dst := For_set sd); eauto with gensym.
  apply contained_cons. eauto with gensym.
  apply contained_app; eauto with gensym.
(* postincr *)
  monadInv H0. exploit H; eauto. intros [tmp1 [A B]].
  destruct dst; monadInv EQ0; simpl add_dest in *.
  (* for value *)
  exists (x0 :: tmp1); split.
  econstructor; eauto with gensym.
  apply contained_cons; eauto with gensym.
  (* for effects *)
  exploit transl_valof_meets_spec; eauto. intros [tmp2 [Csyntax D]].
  exists (tmp1 ++ tmp2); split.
  econstructor; eauto with gensym.
  eauto with gensym.
  (* for set *)
  repeat rewrite app_ass; simpl.
  exists (x0 :: tmp1); split.
  econstructor; eauto with gensym.
  apply contained_cons; eauto with gensym.
(* comma *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
  exists (tmp1 ++ tmp2); split.
  econstructor; eauto with gensym.
  destruct dst; simpl; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  simpl. eapply incl_tran. 2: apply add_dest_incl. auto with gensym.
  destruct dst; simpl; auto with gensym.
  apply contained_app; eauto with gensym.
(* call *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [Csyntax D]].
  destruct dst; monadInv EQ2; simpl add_dest in *.
  (* for value *)
  exists (x1 :: tmp1 ++ tmp2); split.
  econstructor; eauto with gensym. congruence.
  apply contained_cons. eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for effects *)
  exists (tmp1 ++ tmp2); split.
  econstructor; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for set *)
  exists (x1 :: tmp1 ++ tmp2); split.
  repeat rewrite app_ass. econstructor; eauto with gensym. congruence.
  apply contained_cons. eauto with gensym.
  apply contained_app; eauto with gensym.
(* builtin *)
  monadInv H0. exploit H; eauto. intros [tmp1 [A B]].
  destruct dst; monadInv EQ0; simpl add_dest in *.
  (* for value *)
  exists (x0 :: tmp1); split.
  econstructor; eauto with gensym. congruence.
  apply contained_cons; eauto with gensym.
  (* for effects *)
  exists tmp1; split.
  econstructor; eauto with gensym.
  auto.
  (* for set *)
  exists (x0 :: tmp1); split.
  repeat rewrite app_ass. econstructor; eauto with gensym. congruence.
  apply contained_cons; eauto with gensym.
(* loc *)
  monadInv H.
(* paren *)
  monadInv H0.
(* nil *)
  monadInv H; exists (@nil ident); split; auto with gensym. constructor.
(* cons *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [Csyntax D]].
  exists (tmp1 ++ tmp2); split.
  econstructor; eauto with gensym.
  eauto with gensym.
Qed.

Lemma transl_expr_meets_spec:
   forall r dst g sl a g' I,
   transl_expr dst r g = Res (sl, a) g' I ->
   dest_below dst g ->
   exists tmps, forall ge e le m, tr_top ge e le m dst r sl a tmps.
Proof.
  intros. exploit (proj1 transl_meets_spec); eauto. intros [tmps [A B]].
  exists (add_dest dst tmps); intros. apply tr_top_base. auto.
Qed.

Lemma transl_expression_meets_spec:
  forall r g s a g' I,
  transl_expression r g = Res (s, a) g' I ->
  tr_expression r s a.
Proof.
  intros. monadInv H. exploit transl_expr_meets_spec; eauto.
  intros [tmps A]. econstructor; eauto.
Qed.
 *)

Lemma transl_expr_meets_spec:
  forall e g te g' I,
  transl_expr e g = Res te g' I ->
  tr_expr e te.
Proof.
  Check expr_exprlist_ind.
  apply (expr_exprlist_ind
           (fun e => forall g te g' I, transl_expr e g = Res te g' I -> tr_expr e te)
           (fun es => forall g tes g' I, transl_exprlist es g = Res tes g' I -> tr_exprlist es tes)); intros;
    try monadInv H; eauto;
    try monadInv H0; eauto;
    try monadInv H1; eauto;
    try monadInv H2; eauto.
Qed.

Lemma transl_stmt_meets_spec:
  forall s g ts g' I, transl_stmt s g = Res ts g' I -> tr_stmt s ts
with transl_lblstmt_meets_spec:
  forall s g ts g' I, transl_lblstmt s g = Res ts g' I -> tr_lblstmts s ts.
Proof.
  generalize transl_expr_meets_spec.
  intros T.
  clear transl_stmt_meets_spec.
  intros s. induction s; intros; try destruct o;
              try monadInv H; try eauto 20.
  clear transl_lblstmt_meets_spec.
  intros s. induction s; intros; try monadInv H; try eauto.
Qed.

(** Relational presentation for the transformation of functions, fundefs, and variables. *)

Inductive tr_function: ChkCsyntax.function -> Csyntax.function -> Prop :=
  | tr_function_intro: forall f tf,
      tr_stmt f.(ChkCsyntax.fn_body) tf.(fn_body) ->
      fn_return tf = ChkCsyntax.fn_return f ->
      fn_callconv tf = ChkCsyntax.fn_callconv f ->
      fn_params tf = ChkCsyntax.fn_params f ->
      fn_vars tf = ChkCsyntax.fn_vars f ->
      tr_function f tf.

Inductive tr_fundef: ChkCsyntax.fundef -> Csyntax.fundef -> Prop :=
  | tr_internal: forall f tf,
      tr_function f tf ->
      tr_fundef (Internal f) (Internal tf)
  | tr_external: forall ef targs tres cconv,
      tr_fundef (External ef targs tres cconv) (External ef targs tres cconv).

Lemma transl_function_spec:
  forall f tf,
  transl_function f = OK tf ->
  tr_function f tf.
Proof.
  unfold transl_function; intros.
  destruct (transl_stmt (ChkCsyntax.fn_body f) (initial_generator tt)) eqn:T; inv H.
  constructor; auto. simpl. eapply transl_stmt_meets_spec; eauto.
Qed.

Lemma transl_fundef_spec:
  forall fd tfd,
  transl_fundef fd = OK tfd ->
  tr_fundef fd tfd.
Proof.
  unfold transl_fundef; intros.
  destruct fd; Errors.monadInv H.
+ constructor. eapply transl_function_spec; eauto.
+ constructor.
Qed.

End SPEC.
