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
Require Import Ctypes Cop ChkCsyntax Csyntax ChkCsem Csem ChkCstrategy Cstrategy.
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

Theorem transl_program_correct:
  forward_simulation (ChkCstrategy.semantics prog) (Cstrategy.semantics tprog).
Proof.
Admitted.
(*
  eapply forward_simulation_star_wf with (order := ltof _ measure).
  eapply senv_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  apply well_founded_ltof.
  exact simulation.
Qed.
*)

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
