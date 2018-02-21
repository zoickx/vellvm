(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Import Vellvm.Classes Vellvm.Util Vellvm.Trace.
Require Import Vellvm.LLVMAst Vellvm.LLVMBaseTypes.

Set Implicit Arguments.
Set Contextual Implicit.

Module Type ADDR.
  Parameter addr : Set.
  Parameter null : addr.
End ADDR.  

Module DVALUE(A:ADDR).
       
(* The set of dynamic values manipulated by an LLVM program. *)
Inductive dvalue : Set :=
| DVALUE_FunPtr (fid : function_id)
| DVALUE_Addr (a:A.addr)
| DVALUE_I1 (x:int1)
| DVALUE_I32 (x:int32)
| DVALUE_I64 (x:int64)
| DVALUE_Double (x:ll_double)
| DVALUE_Float (x:ll_float)
| DVALUE_Undef (t:typ) (v:option exp)
| DVALUE_Poison
| DVALUE_None
| DVALUE_Struct        (fields: list (typ * dvalue))
| DVALUE_Packed_struct (fields: list (typ * dvalue))
| DVALUE_Array         (elts: list (typ * dvalue))
| DVALUE_Vector        (elts: list (typ * dvalue))
.

Definition undef t := DVALUE_Undef t None.
Definition undef_i1  := undef (TYPE_I 1).
Definition undef_i32 := undef (TYPE_I 32).
Definition undef_i64 := undef (TYPE_I 64).

Inductive IO : Type -> Type :=
| Alloca : forall (t:typ), (IO dvalue)
| Load   : forall (t:typ) (a:dvalue), (IO dvalue)
| Store  : forall (a:dvalue) (v:dvalue), (IO unit)
| GEP    : forall (t:typ) (v:dvalue) (vs:list dvalue), (IO dvalue)
| ItoP   : forall (t:typ) (i:dvalue), (IO dvalue)
| PtoI   : forall (t:typ) (a:dvalue), (IO dvalue)
| Call   : forall (t:typ) (f:string) (args:list dvalue), (IO dvalue)
| DeclareFun : forall (f:function_id), (IO dvalue)
.    

(* Trace of events generated by a computation. *)
Definition Trace X := M IO X.
Instance functor_trace : Functor Trace := (@mapM IO).
Instance monad_trace : (@Monad Trace) (@mapM IO) := { mret X x := Ret x; mbind := @bindM IO }.
Instance exn_trace : (@ExceptionMonad string Trace _ _) := fun _ s => Err s.

(* Trace Utilities ---------------------------------------------------------- *)

(* Lift the error monad into the trace monad. *)
Definition lift_err_d {A X} (m:err A) (f: A -> Trace X) : Trace X :=
  match m with
  | inl s => raise s
  | inr b => f b
  end.

Notation "'do' x <- m ; f" := (lift_err_d m (fun x => f)) 
                               (at level 200, x ident, m at level 100, f at level 200).

End DVALUE.