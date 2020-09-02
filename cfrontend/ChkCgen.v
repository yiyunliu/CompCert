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
    Dynamic checks are inserted at this stage and maybe optimized away in later stages. *)

Require Import Maps.
Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import AST.
Require Import ChkCtypes.
Require Import Ctypes.
Require Import ChkCop.
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


(* we can either pull the signedness etc. out to a separate module  *)
(* or do brute force translation like this: *)


Definition transl_signedness (t: ChkCtypes.signedness) : signedness :=
  match t with
  | ChkCtypes.Signed  =>
      Signed 
  | ChkCtypes.Unsigned  =>
      Unsigned 
  end.

Definition transl_intsize (t: ChkCtypes.intsize) : intsize :=
  match t with
  | ChkCtypes.I8  =>
      I8 
  | ChkCtypes.I16  =>
      I16 
  | ChkCtypes.I32  =>
      I32 
  | ChkCtypes.IBool  =>
      IBool 
  end.

Definition transl_floatsize (t: ChkCtypes.floatsize) : floatsize :=
  match t with
  | ChkCtypes.F32  =>
      F32 
  | ChkCtypes.F64  =>
      F64 
  end.

(* Record attr : Type := mk_attr { *)
(*   attr_volatile: bool; *)
(*   attr_alignas: option N         (**r log2 of required alignment *) *)
(* }. *)

Definition transl_attr (t: ChkCtypes.attr) : attr :=
  {| attr_volatile := ChkCtypes.attr_volatile t;
     attr_alignas := ChkCtypes.attr_alignas t |}.


Fixpoint transl_type (t: ChkCtypes.type) : type :=
  match t with
  | ChkCtypes.Tvoid  =>
      Tvoid 
  | ChkCtypes.Tint a b c =>
      Tint (transl_intsize a) (transl_signedness b) (transl_attr c)
  | ChkCtypes.Tlong a b =>
      Tlong (transl_signedness a) (transl_attr b)
  | ChkCtypes.Tfloat a b =>
      Tfloat (transl_floatsize a) (transl_attr b)
  | ChkCtypes.Tpointer a b =>
      Tpointer (transl_type a) (transl_attr b)
  | ChkCtypes.Tarray a b c =>
      Tarray (transl_type a) b (transl_attr c)
  | ChkCtypes.Tfunction a b c =>
      Tfunction (transl_typelist a) (transl_type b) c
  | ChkCtypes.Tstruct a b =>
      Tstruct a (transl_attr b)
  | ChkCtypes.Tunion a b =>
      Tunion a (transl_attr b)
  | ChkCtypes.Tchkcptr a b =>
      Tpointer (transl_type a) (transl_attr b)
  end
with transl_typelist (ts: ChkCtypes.typelist) : Ctypes.typelist :=
       match ts with
       | ChkCtypes.Tnil => Tnil
       | ChkCtypes.Tcons t ts' => Tcons (transl_type t) (transl_typelist ts')
       end.

Definition transl_unary_operation (t: ChkCop.unary_operation) : unary_operation :=
  match t with
  | ChkCop.Onotbool  =>
      Onotbool 
  | ChkCop.Onotint  =>
      Onotint 
  | ChkCop.Oneg  =>
      Oneg 
  | ChkCop.Oabsfloat  =>
      Oabsfloat 
  end.

Definition transl_binary_operation (t: ChkCop.binary_operation) : binary_operation :=
  match t with
  | ChkCop.Oadd  =>
      Oadd 
  | ChkCop.Osub  =>
      Osub 
  | ChkCop.Omul  =>
      Omul 
  | ChkCop.Odiv  =>
      Odiv 
  | ChkCop.Omod  =>
      Omod 
  | ChkCop.Oand  =>
      Oand 
  | ChkCop.Oor  =>
      Oor 
  | ChkCop.Oxor  =>
      Oxor 
  | ChkCop.Oshl  =>
      Oshl 
  | ChkCop.Oshr  =>
      Oshr 
  | ChkCop.Oeq  =>
      Oeq 
  | ChkCop.One  =>
      One 
  | ChkCop.Olt  =>
      Olt 
  | ChkCop.Ogt  =>
      Ogt 
  | ChkCop.Ole  =>
      Ole 
  | ChkCop.Oge  =>
      Oge 
  end.


Definition transl_incr_or_decr (e: ChkCop.incr_or_decr) : incr_or_decr :=
  match e with
  | ChkCop.Incr => Incr
  | ChkCop.Decr => Decr
  end.


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
  | ChkCsyntax.Ederef r (Tchkcptr _ _ as ty) =>
    do tr <- transl_expr r;
    ret (Ebuiltin (EF_chkc CE_NULLPTR) Tnil Enil (transl_type ty))
  | ChkCsyntax.Ederef r ty =>
    do tr <- transl_expr r;
  (* TODO: if then else here *)
    (* ret (Ebuiltin (EF_chkc CE_NULLPTR) Tnil Enil (transl_type ty)) *)
    ret (Ederef tr (transl_type ty))
  | ChkCsyntax.Eaddrof l ty =>
    do tl <- transl_expr l;
    ret (Eaddrof tl (transl_type ty))
  | ChkCsyntax.Eunop op r ty =>
    do tr <- transl_expr r;
    ret (Eunop (transl_unary_operation op) tr (transl_type ty))
  | ChkCsyntax.Ebinop op r1 r2 ty =>
    do tr1 <- transl_expr r1;
    do tr2 <- transl_expr r2;
    ret (Ebinop (transl_binary_operation op) tr1 tr2 (transl_type ty))
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
    (* YL: testing if invalid instruction works *)
    (* ret (Ebuiltin (EF_chkc CE_NULLPTR) Tnil Enil Tvoid) *)
    ret (Eassign tl tr (transl_type ty))
  | ChkCsyntax.Eassignop op l r tyres ty =>
    do tl <- transl_expr l;
    do tr <- transl_expr r;
    ret (Eassignop (transl_binary_operation op) tl tr (transl_type tyres) (transl_type ty))
  | ChkCsyntax.Epostincr id l ty =>
    do tl <- transl_expr l;
    ret (Epostincr (transl_incr_or_decr id) tl (transl_type ty))
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

Definition transl_function (f: ChkCsyntax.function) : res Csyntax.function :=
  match transl_stmt f.(ChkCsyntax.fn_body) (initial_generator tt) with
  | Err msg =>
      Error msg
  | Res tbody _ i =>
      OK (mkfunction
              (transl_type f.(ChkCsyntax.fn_return))
              f.(ChkCsyntax.fn_callconv)
              (map (fun '(id, ty) => (id, transl_type ty)) f.(ChkCsyntax.fn_params))
              (map (fun '(id, ty) => (id, transl_type ty)) f.(ChkCsyntax.fn_vars))
              tbody)
  end.

Local Open Scope error_monad_scope.

Definition transl_fundef (fd: ChkCsyntax.fundef) : res Csyntax.fundef :=
  match fd with
  | ChkCtypes.Internal f =>
      do tf <- transl_function f; OK (Ctypes.Internal tf)
  | ChkCtypes.External ef targs tres cc =>
      OK (Ctypes.External ef (transl_typelist targs) (transl_type tres) cc)
  end.

Definition transl_struct_or_union (su: ChkCtypes.struct_or_union) : Ctypes.struct_or_union :=
  match su with
  | ChkCtypes.Struct => Ctypes.Struct
  | ChkCtypes.Union => Ctypes.Union
  end.


Definition transl_members : ChkCtypes.members -> members :=
  map (fun '(i, ty) => (i, transl_type ty)).

Definition transl_composite (comp: ChkCtypes.composite) : Ctypes.composite.
Proof with eauto.
  destruct comp.
  econstructor...
  - apply transl_struct_or_union...
  - apply transl_members...
  - apply transl_attr...
Defined.

Definition transl_composite_def (defs: ChkCtypes.composite_definition) : Ctypes.composite_definition :=
  match defs with
  | ChkCtypes.Composite id su m a => 
    Composite id
            (transl_struct_or_union su)
            (transl_members m)
            (transl_attr a)
  end.

Definition transl_composite_env (defs: ChkCtypes.composite_env) : Ctypes.composite_env.
  eapply PTree.map1.
  apply transl_composite.
  intuition.
Defined.

Lemma transl_composite_env_eq
      (prog_types: list ChkCtypes.composite_definition)
      (prog_comp_env: ChkCtypes.composite_env)
      (prog_comp_env_eq: ChkCtypes.build_composite_env prog_types = OK prog_comp_env)
  : Ctypes.build_composite_env (map transl_composite_def prog_types) = OK (transl_composite_env prog_comp_env).
Admitted.


Definition transl_program (p: ChkCsyntax.program) : res Csyntax.program :=
  do p1 <- AST.transform_partial_program2 (fun _ => transl_fundef) (fun _ ty => OK (transl_type ty)) p;
  OK {| prog_defs := AST.prog_defs p1;
        prog_public := AST.prog_public p1;
        prog_main := AST.prog_main p1;
        prog_types := map transl_composite_def (ChkCtypes.prog_types p);
        prog_comp_env := transl_composite_env (ChkCtypes.prog_comp_env p);
        prog_comp_env_eq := transl_composite_env_eq (ChkCtypes.prog_types p) (ChkCtypes.prog_comp_env p) (ChkCtypes.prog_comp_env_eq p) |}.
