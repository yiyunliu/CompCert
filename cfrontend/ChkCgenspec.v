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
