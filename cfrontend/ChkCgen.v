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

(** Translation from Checked C to Compcert C.
    Side effects are pulled out of Compcert C expressions. *)

Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import AST.
Require Import Ctypes.
Require Import ChkCtypes.
Require Import Cop.
Require Import ChkCsyntax.
Require Import Csyntax.

Local Open Scope string_scope.
Local Open Scope list_scope.

(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
  gen_next: ident;
  gen_trail: list (ident * type)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.

Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g (Ple_refl (gen_next g)).

Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' i =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
      end
    end.

Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Parameter first_unused_ident: unit -> ident.

Definition initial_generator (x: unit) : generator :=
  mkgenerator (first_unused_ident x) nil.

Fixpoint transl_type (e: ChkCtypes.type) : Ctypes.type.
Admitted.

Fixpoint transl_typelist (e: ChkCtypes.typelist) : Ctypes.typelist.
Admitted.

Fixpoint transl_expr (e: ChkCsyntax.expr) : mon expr :=
  match e with
  | ChkCsyntax.Eval v ty =>
    ret (Eval v (transl_type ty))
  | ChkCsyntax.Evar x ty =>
    ret (Evar x (transl_type ty))
  | ChkCsyntax.Efield l f ty =>
    do tl <- transl_expr l;
    ret (Efield tl f (transl_type ty))
  | ChkCsyntax.Evalof l ty =>
    do tl <- transl_expr l;
    ret (Evalof tl (transl_type ty))
  (* | ChkCsyntax.Ederef r (Tchkcptr _ _ as ty) => *)
  (*   do tr <- transl_expr r; *)
    
  (*   ret (Ederef tr (transl_type ty)) *)
  | ChkCsyntax.Ederef r ty =>
    do tr <- transl_expr r;
    ret (Ederef tr (transl_type ty))
  | ChkCsyntax.Eaddrof l ty =>
    do tl <- transl_expr l;
    ret (Eaddrof tl (transl_type ty))
  | ChkCsyntax.Eunop op r ty =>
    do tr <- transl_expr r;
    ret (Eunop op tr (transl_type ty))
  | ChkCsyntax.Ebinop op r1 r2 ty =>
    do tr1 <- transl_expr r1;
    do tr2 <- transl_expr r2;
    ret (Ebinop op tr1 tr2 (transl_type ty))
  | ChkCsyntax.Ecast r ty =>
    do tr <- transl_expr r;
    ret (Ecast tr (transl_type ty))
  | ChkCsyntax.Eseqand r1 r2 ty =>
    do tr1 <- transl_expr r1;
    do tr2 <- transl_expr r2;
    ret (Eseqand tr1 tr2 (transl_type ty))
  | ChkCsyntax.Eseqor r1 r2 ty =>
    do tr1 <- transl_expr r1;
    do tr2 <- transl_expr r2;
    ret (Eseqor tr1 tr2 (transl_type ty))
  | ChkCsyntax.Econdition r1 r2 r3 ty =>
    do tr1 <- transl_expr r1;
    do tr2 <- transl_expr r2;
    do tr3 <- transl_expr r3;
    ret (Econdition tr1 tr2 tr3 (transl_type ty))
  | ChkCsyntax.Esizeof ty' ty =>
    ret (Esizeof (transl_type ty') (transl_type ty))
  | ChkCsyntax.Ealignof ty' ty =>
    ret (Ealignof (transl_type ty') (transl_type ty))
  | ChkCsyntax.Eassign l r ty =>
    do tl <- transl_expr l;
    do tr <- transl_expr r;
    ret (Eassign tl tr (transl_type ty))
  | ChkCsyntax.Eassignop op l r tyres ty =>
    do tl <- transl_expr l;
    do tr <- transl_expr r;
    ret (Eassignop op tl tr (transl_type tyres) (transl_type ty))
  | ChkCsyntax.Epostincr id l ty =>
    do tl <- transl_expr l;
    ret (Epostincr id tl (transl_type ty))
  | ChkCsyntax.Ecomma r1 r2 ty =>
    do tr1 <- transl_expr r1;
    do tr2 <- transl_expr r2;
    ret (Ecomma tr1 tr2 (transl_type ty))
  | ChkCsyntax.Ecall r1 rargs ty =>
    do tr1    <- transl_expr r1;
    do trargs <- transl_exprlist rargs;
    ret (Ecall tr1 trargs (transl_type ty))
  | ChkCsyntax.Ebuiltin ef tyargs rargs ty =>
    do trargs <- transl_exprlist rargs;
    ret (Ebuiltin ef (transl_typelist tyargs) trargs (transl_type ty))
  | ChkCsyntax.Eloc b ofs ty =>
    ret (Eloc b ofs (transl_type ty))
  | ChkCsyntax.Eparen r tycast ty =>
    do tr <- transl_expr r;
    ret (Eparen tr (transl_type tycast) (transl_type ty))
  end

with transl_exprlist (rl : ChkCsyntax.exprlist) : mon exprlist :=
       match rl with
       | ChkCsyntax.Enil => ret Enil
       | ChkCsyntax.Econs r1 rl2 =>
         do tr1  <- transl_expr r1;
         do trl2 <- transl_exprlist rl2;
         ret (Econs tr1 trl2)
       end.

Fixpoint transl_stmt (s: ChkCsyntax.statement) : mon statement :=
  match s with
  | ChkCsyntax.Sskip => ret Sskip
  | ChkCsyntax.Sdo e =>
      do te <- transl_expr e;
      ret (Sdo te)
  | ChkCsyntax.Ssequence s1 s2 =>
      do ts1 <- transl_stmt s1;
      do ts2 <- transl_stmt s2;
      ret (Ssequence ts1 ts2)
  | ChkCsyntax.Sifthenelse e s1 s2 =>
      do te  <- transl_expr e;
      do ts1 <- transl_stmt s1;
      do ts2 <- transl_stmt s2;
      ret (Sifthenelse te ts1 ts2)
  | ChkCsyntax.Swhile e s1 =>
      do te  <- transl_expr e;
      do ts1 <- transl_stmt s1;
      ret (Swhile te ts1)
  | ChkCsyntax.Sdowhile e s1 =>
      do te  <- transl_expr e;
      do ts1 <- transl_stmt s1;
      ret (Sdowhile te ts1)
  | ChkCsyntax.Sfor s1 e2 s3 s4 =>
      do ts1 <- transl_stmt s1;
      do te2 <- transl_expr e2;
      do ts3 <- transl_stmt s3;
      do ts4 <- transl_stmt s4;
      ret (Sfor ts1 te2 ts3 ts4)
  | ChkCsyntax.Sbreak =>
      ret Sbreak
  | ChkCsyntax.Scontinue =>
      ret Scontinue
  | ChkCsyntax.Sreturn None =>
      ret (Sreturn None)
  | ChkCsyntax.Sreturn (Some e) =>
      do te <- transl_expr e;
      ret (Sreturn (Some te))
  | ChkCsyntax.Sswitch e ls =>
      do te <- transl_expr e;
      do tls <- transl_lblstmt ls;
      ret (Sswitch te tls)
  | ChkCsyntax.Slabel lbl s1 =>
      do ts1 <- transl_stmt s1;
      ret (Slabel lbl ts1)
  | ChkCsyntax.Sgoto lbl =>
      ret (Sgoto lbl)
  end

with transl_lblstmt (ls: ChkCsyntax.labeled_statements) : mon labeled_statements :=
  match ls with
  | ChkCsyntax.LSnil =>
      ret LSnil
  | ChkCsyntax.LScons c s ls1 =>
      do ts <- transl_stmt s;
      do tls1 <- transl_lblstmt ls1;
      ret (LScons c ts tls1)
  end.

(** Translation of a function *)

Check Csyntax.mkfunction.

Definition transl_function (f: ChkCsyntax.function) : res function :=
  match transl_stmt f.(ChkCsyntax.fn_body) (initial_generator tt) with
  | Err msg =>
      Error msg
  | Res tbody _ i =>
      OK (mkfunction
              f.(ChkCsyntax.fn_return)
              f.(ChkCsyntax.fn_callconv)
              f.(ChkCsyntax.fn_params)
              f.(ChkCsyntax.fn_vars)
              tbody)
  end.

Local Open Scope error_monad_scope.

Definition transl_fundef (fd: ChkCsyntax.fundef) : res fundef :=
  match fd with
  | Internal f =>
      do tf <- transl_function f; OK (Internal tf)
  | External ef targs tres cc =>
      OK (External ef targs tres cc)
  end.

Definition transl_program (p: ChkCsyntax.program) : res program :=
  do p1 <- AST.transform_partial_program transl_fundef p;
  OK {| prog_defs := AST.prog_defs p1;
        prog_public := AST.prog_public p1;
        prog_main := AST.prog_main p1;
        prog_types := prog_types p;
        prog_comp_env := prog_comp_env p;
        prog_comp_env_eq := prog_comp_env_eq p |}.
