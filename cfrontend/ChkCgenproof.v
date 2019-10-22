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
Require Import Ctypes Cop ChkCsyntax Csyntax Csem Cstrategy Clight.
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
