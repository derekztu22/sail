(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

open Libsail

open Ast
open Ast_defs
open Ast_util
open Jib
open Jib_compile
open Jib_util
open Type_check
open PPrint
open Value2

open Anf

module Big_int = Nat_big_num

let opt_ext = ref "mm"

let str_contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false

let rec tensorops_rgenircl rgenircl_string_list outtype=
  match rgenircl_string_list with
  | [] -> ""
  | h :: t ->
    let rec find_return_type str_list =
      match str_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "description" then
          find_return_type t
        else
          if str_contains h "output" then
            let out_type = String.split_on_char ':' h in
            let out_type = List.hd(String.split_on_char '(' (List.nth out_type 1)) in
            out_type
          else
            find_return_type t
    in
    if str_contains h "Sail_"  then
  
      let rec tensorops_rgenircli str_list instr_name outtype  =
        match str_list with
        | [] -> ""
        | h :: t ->
          if str_contains h "summary" then
            "" ^ tensorops_rgenircli t instr_name outtype
          else if str_contains h "description" then
            "" ^ tensorops_rgenircli t instr_name outtype
          else if str_contains h "input1" then
            let rec further_inputs str_list num =
              match str_list with
              | [] -> ("", Int.add num 1)
              | h :: t ->
                if str_contains (List.hd (String.split_on_char ':' h)) "input"  then
                  let in_type = String.split_on_char ':' h in
                  let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
                  let further_input_strings, n = further_inputs t (Int.add num 1) in 
                   ", const " ^ in_type ^ "& input" ^ string_of_int(num) ^ further_input_strings, n
                else
                  let further_input_strings, n = (further_inputs t (Int.add num 1)) in 
                  ("" ^ further_input_strings, num)
            in
    
            let in_type = String.split_on_char ':' h in
            let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
            let further_input_string, n = (further_inputs t 2) in
    
            let rec execute_function str_list outtype n = 
              match str_list with
              | [] -> ""
              | h :: t ->
                if str_contains h (!opt_ext) then
                  if outtype = "norm" then
                    (*let headers = "\n#ifndef MM_H\n#define MM_H\n#include <c10/util/irange.h>\n#endif\n" in *)
                    let quotation_regex = Str.regexp "\"" in 
                    let whitespace_regex = Str.regexp " " in 
                    let semicolon_regex = Str.regexp ";" in 
                    let execute_str = Str.global_replace quotation_regex "" (List.nth (String.split_on_char '=' h) 1) in
                    let scalar_t = List.hd (String.split_on_char '@' execute_str) in
                    let scalar_t_def = "\n using scalar_t = " ^ scalar_t ^ ";\n" in
                    let length_def = "const int64_t length = input1_sizes[0];\n" in
                    let setup_var = "" in
                    let abcd_list = ["."; "a"; "b"; "c"; "d"] in
    
                    let setup_var n =
                      let rec loop i limit = 
                        if i = limit then 
                          ""
                        else
                          let size_str = ("  const auto input" ^ string_of_int(i) ^  "_sizes = input" ^
                                         string_of_int(i) ^ ".sizes();\n") in
                          let tensor_str = ("  Tensor " ^ List.nth abcd_list i ^ " = input" ^
                                           string_of_int(i) ^ ".clone(at::MemoryFormat::Contiguous);\n") in
                          let ptr_str = ("  auto " ^ List.nth abcd_list i ^ "_ptr = " ^
                                        List.nth abcd_list i ^ ".data_ptr<scalar_t>();\n") in
                          size_str ^ tensor_str ^ ptr_str ^ (loop (Int.add i 1) n)
                      in
                      loop 1 n
                    in
     
                    let rec find_ops ex_str =
                      match ex_str with
                      | [] -> ""
                      | h :: t ->
                        let op_list = ["*"; "-"; "+"] in
                        let str = Str.global_replace whitespace_regex "" h in
                        if List.exists ((=)str) op_list then
                          str ^ " " ^ find_ops t
                        else 
                          "" ^ find_ops t 
                    in
     
                    let get_execute n instr_name execute_str = 
                      let mm_regex = Str.regexp "mm" in
                      let explode s = List.init (String.length s) (String.get s) in
                      let instr_name = String.of_seq (List.to_seq (List.rev (explode instr_name))) in
                      let instr_name = Str.replace_first mm_regex "mm." instr_name in
                      let assem_name = String.of_seq (List.to_seq (List.rev (explode instr_name))) in

                      if n = 4 then 
                        let load_str = "asm volatile (\"loadxy.mm m1, (%0) \\n\\t\" ::\"r\"((int64_t) a_ptr));\n" ^
                                       "asm volatile (\"loadxy.mm m2, (%0) \\n\\t\" ::\"r\"((int64_t) b_ptr));\n" ^
                                       "asm volatile (\"loadz.mm m0, (%0) \\n\\t\" ::\"r\"((int64_t) c_ptr));\n" in 
                        let load_str = load_str ^ "asm volatile (\"" ^ assem_name ^ " m0, m2, m1 \\n\\t\");\n" in
                        let store_str = "asm volatile (\"storez.mm m0, (%0) \\n\\t\" ::\"r\"((int64_t) c_ptr));\n" in
                        load_str ^ store_str
                     else if n = 3 then
                        let load_str = "asm volatile (\"loadxy.mm m1, (%0) \\n\\t\" ::\"r\"((int64_t) a_ptr));\n" in
                        let load_str = load_str ^ "asm volatile (\"" ^ assem_name ^ " m0, m1 \\n\\t\");\n" in
                        let store_str = "asm volatile (\"storez.mm m0, (%0) \\n\\t\" ::\"r\"((int64_t) b_ptr));\n" in
                        load_str ^ store_str
                     else
                       ""
                    in
    
                    let forward_def_str instr_name scalar_t n =
                      let rec loop i limit =
                        if i = limit then
                          ""
                        else
                          scalar_t ^ "*" ^ List.nth abcd_list i ^ "_ptr," ^ (loop (Int.add i 1) n)
                      in
                      "void external_" ^ instr_name ^ "(" ^ (loop 1 n) ^ " int64_t length);\n\n"
                    in

                    let pytorch_func_end_str instr_name n =
                      let rec loop i limit =
                        if i = limit then
                          ""
                        else
                         List.nth abcd_list i ^ "_ptr," ^ (loop (Int.add i 1) n)
                      in
                      "external_" ^ instr_name ^ "(" ^ (loop 1 n) ^ "  length);\nreturn " ^
                      List.nth abcd_list (n-1) ^ ";\n}\n\n" 
                    in

                    let pytorch_func_end = pytorch_func_end_str instr_name n in
                    let forward_def = forward_def_str instr_name scalar_t n in
                    let forward_def_impl = Str.global_replace semicolon_regex "{" forward_def in
                    let forward_def_impl = forward_def_impl ^ (get_execute n instr_name execute_str) ^ "}\n\n" in
    
                    scalar_t_def ^ (setup_var n) ^ length_def ^ pytorch_func_end ^ forward_def ^ forward_def_impl
    
                  else if outtype = "_" then
                    "\nreturn input1;\n}\n"
                  else if outtype = "_out" then
                    "\nreturn result;\n}\n"
                  else
                  ""
                else if str_contains h "execute_func" then
                  if outtype = "norm" then
                    "\nreturn input1;\n}\n"
                  else if outtype = "_" then
                    "\nreturn input1;\n}\n"
                  else if outtype = "_out" then
                    "\nreturn result;\n}\n"
                  else
                  ""
                else
                  "" ^ execute_function t outtype n
            in
    
            if outtype = "norm" then   
              "const " ^ in_type ^ "& input1" ^ further_input_string ^ ") {" ^ execute_function t outtype n
            else if outtype = "_" then 
              in_type ^ "& input1" ^ further_input_string ^ ") {" ^ execute_function t outtype n
            else if outtype = "_out" then 
              "const " ^ in_type ^ "& input1" ^ further_input_string ^ "," ^ find_return_type t ^ "& result) {" ^ execute_function t outtype n
            else
              ""
          else
            tensorops_rgenircli t instr_name outtype
      in

      let instr_name = List.nth (String.split_on_char '"' h) 1 in
      if outtype = "norm" then 
        (find_return_type t) ^ " " ^ instr_name ^ "(" ^ tensorops_rgenircli t instr_name outtype 
      else if outtype = "_" || outtype = "_out" then 
        (find_return_type t) ^ "& " ^ instr_name ^ outtype ^ "(" ^ tensorops_rgenircli t instr_name outtype 
      else
        tensorops_rgenircli t instr_name outtype

    else
      "" ^ tensorops_rgenircl t outtype

let rec nfunctions_rgenircl rgenircl_string_list outtype=
  let rec find_instr_name str_list =
    match str_list with
    | [] -> ""
    | h :: t ->
      if str_contains h "Sail_" then
        let instr_name = List.nth (String.split_on_char '"' h) 1 in
        instr_name ^ find_instr_name t
      else
        "" ^ find_instr_name t
  in
  let instr_name = ref (find_instr_name rgenircl_string_list) in
  let whitespace_regex = Str.regexp " " in

  match rgenircl_string_list with
  | [] -> ""
  | h :: t ->
    let rec find_return_type str_list =
      match str_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "output" then
          let out_type = String.split_on_char ':' h in
          let out_type = List.hd(String.split_on_char '(' (List.nth out_type 1)) in
          out_type
        else
          find_return_type t
    in

    if str_contains h "Sail_"  then
      let rec nfunctions_inner_rgenircl slist outtype instr_name =
        match slist with
        | [] -> ""
        | h :: t ->
        if str_contains h "summary" then
          "" ^ nfunctions_inner_rgenircl t outtype instr_name
        else if str_contains h "description" then
          "" ^ nfunctions_inner_rgenircl t outtype instr_name
        else if str_contains (List.hd (String.split_on_char ':' h)) "input1" then

          let rec further_inputs str_list num =
            match str_list with
            | [] -> ("", num)
            | h :: t ->
              if str_contains (List.hd (String.split_on_char ':' h)) "input"  then
                let in_type = String.split_on_char ':' h in
                let in_type = Str.replace_first whitespace_regex "" (List.hd (String.split_on_char '(' (List.nth in_type 1))) in
                let further_input_strings, _ = further_inputs t (Int.add num 1) in 
                 ", " ^ in_type ^ " input" ^ string_of_int(num) ^  further_input_strings, num 
              else
                let further_input_strings, _ = (further_inputs t (Int.add num 1)) in 
                ("" ^ further_input_strings, num)
          in

          let in_type = String.split_on_char ':' h in
          let in_type = Str.replace_first whitespace_regex "" (List.hd (String.split_on_char '(' (List.nth in_type 1))) in
          let further_input_string, _ = further_inputs t 2 in
          if outtype = "norm" then 
            in_type ^ " self" ^ further_input_string ^ ") -> " ^ nfunctions_inner_rgenircl t outtype instr_name
          else if outtype = "_" then 
            in_type ^ "(a!) self" ^ further_input_string ^ ") -> " ^ nfunctions_inner_rgenircl t outtype instr_name
          else if outtype = "_out" then 
            in_type ^ " self" ^ further_input_string ^ ", *, " ^ find_return_type t ^ "(a!) out) -> " ^ nfunctions_inner_rgenircl t outtype instr_name 
          else
           "" ^ nfunctions_inner_rgenircl t outtype instr_name
        else if str_contains h "output" then
          let out_type = String.split_on_char ':' h in
          let out_type = Str.replace_first whitespace_regex "" (List.hd(String.split_on_char '(' (List.nth out_type 1))) in
          if outtype = "norm" then
            out_type ^ "\n  variants: function\n  dispatch:\n    CPU: " ^ !instr_name ^  nfunctions_inner_rgenircl t outtype instr_name
          else if outtype = "_" then
            out_type ^ "(a!)\n  variants: function\n  dispatch:\n    CPU: " ^ !instr_name ^ outtype ^ nfunctions_inner_rgenircl t outtype instr_name
          else if outtype = "_out" then
            out_type ^ "(a!)\n  variants: function\n  dispatch:\n    CPU: " ^ !instr_name ^ outtype ^ nfunctions_inner_rgenircl t outtype instr_name
          else
          "" ^ nfunctions_inner_rgenircl t outtype instr_name
        else
          "" ^ nfunctions_inner_rgenircl t outtype instr_name
      in

      if outtype = "norm" then 
        "- func: " ^ !instr_name ^ "(" ^ nfunctions_inner_rgenircl t outtype instr_name
      else if outtype = "_" then 
        "- func: " ^ !instr_name ^ outtype ^ "(" ^ nfunctions_inner_rgenircl t outtype instr_name
      else if outtype = "_out" then 
        "- func: " ^ !instr_name ^ ".out(" ^ nfunctions_inner_rgenircl t outtype instr_name
      else
        "" ^ nfunctions_inner_rgenircl t outtype instr_name
    else
      "" ^ nfunctions_rgenircl t outtype

let sail_to_tosa clause outtype =
  let rgenircl_string = Pretty_print_sail.Document.to_string(Pretty_print_sail.doc_rgenircl clause) in
  let rgenircl_string_list = String.split_on_char '\n' rgenircl_string in
  if outtype = "tensorops" then
    (tensorops_rgenircl rgenircl_string_list "norm" ^ "\n" ^
    tensorops_rgenircl rgenircl_string_list "_" ^ "\n" ^
    tensorops_rgenircl rgenircl_string_list "_out" ^ "\n")
  else if outtype = "nfunctions" then
    (nfunctions_rgenircl rgenircl_string_list "norm" ^ "\n" ^
     nfunctions_rgenircl rgenircl_string_list "_" ^ "\n" ^
     nfunctions_rgenircl rgenircl_string_list "_out" ^ "\n")
  else
    ""
let rec tosa_rgenircl rgenircls outtype  =
  match rgenircls with
  | [] -> ""
  | clause :: clauses -> sail_to_tosa clause outtype ^ tosa_rgenircl clauses outtype

let rec tosa_rgenirdef (RGENIRD_aux (RGENIRD_cl (id, rgenircls), _)) outtype =
  match rgenircls with
  | [] -> failwith "No rgenir clause"
  | _ -> tosa_rgenircl rgenircls outtype

let compile_ast env effect_info output_chan ast =
  let td_def def outtype = 
    match def with
    | DEF_rgenirdef rgenirdef -> tosa_rgenirdef rgenirdef outtype
    | _ -> ""
  in

  let rec process_defs_to_tosa outtype = function
    | [] -> ""
    | DEF_aux (def, _):: defs ->
       let td  =  td_def def outtype in
       td ^  process_defs_to_tosa outtype defs
  in

  let outtype = "tensorops" in
  let tosa_tensorops = (process_defs_to_tosa outtype ast.defs) in

  let outtype = "nfunctions" in
  let tosa_nfunctions = (process_defs_to_tosa outtype ast.defs) in

  let fname4 = "generated_definitions/pytorch/ExternalOps.cpp" in
  let fname5 = "generated_definitions/pytorch/native_functions.yaml" in

  let output_chan = open_out fname4 in
  Printf.fprintf output_chan "%s" tosa_tensorops;
  close_out output_chan;

  let output_chan = open_out fname5 in
  Printf.fprintf output_chan "%s" tosa_nfunctions;
  close_out output_chan;

 (* print_endline(tosa_nfunctions);*)
 (* print_endline(tosa_tensorops)*)
