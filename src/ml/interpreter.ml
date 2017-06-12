(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

;; open Memory


let print_int_dvalue dv : unit =
  match dv with
  (* Should this branch of the pattern be an error? *)
  | SS.DV (Ollvm_ast.VALUE_Integer i) -> Printf.printf "Program terminated with VALUE_Integer: %d\n" (Camlcoq.Z.to_int i)
  | SS.DV (Ollvm_ast.VALUE_Undef) -> Printf.printf "Program terminated with: undefined value.\n"
  | SS.DVALUE_I64 i -> Printf.printf "Program terminated with: %Ld\n"
                                    (Camlcoq.Z.to_int64 (Integers.Int64.signed i))
  | SS.DVALUE_I32 i -> Printf.printf "Program terminated with: %ld\n"
                                    (Camlcoq.Z.to_int32 (Integers.Int.signed i))
  | SS.DVALUE_I1 i -> Printf.printf "Program terminated with: %d\n"
                                   (Camlcoq.Z.to_int (StepSemantics.Int1.unsigned i))
  | SS.DVALUE_Poison -> Printf.printf "Program terminated with: poison value.\n"
  | _ -> Printf.printf "Program terminated with non-Integer value.\n"

let rec step m =
  match Lazy.force m with
  | SS.E.Tau x -> step x
  | SS.E.Fin v -> v
  | SS.E.Err s -> failwith (Printf.sprintf "ERROR: %s" (Camlcoq.camlstring_of_coqstring s))
  | SS.E.Ret _ -> failwith "should be impossible"
  | SS.E.Eff (SS.E.Call(f, args, k)) -> failwith "unimplemented"
  | SS.E.Eff _ -> failwith "should have been handled by the memory model"  
      

let interpret (prog:(Ollvm_ast.block list) Ollvm_ast.toplevel_entity list) : SS.dvalue =
  let scfg = AstLib.modul_of_toplevel_entities prog in
  match CFG.mcfg_of_modul scfg with
  | None -> failwith "bad module"
  | Some mcfg ->
     match SS.init_state mcfg (Camlcoq.coqstring_of_camlstring "main") with
     | Datatypes.Coq_inl err -> failwith (Camlcoq.camlstring_of_coqstring err)
     | Datatypes.Coq_inr s ->
        let sem = SS.sem mcfg s in
        let mem = memD [] sem in
        step mem
  
