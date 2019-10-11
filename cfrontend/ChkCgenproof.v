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
