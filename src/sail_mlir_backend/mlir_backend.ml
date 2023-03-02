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

let str_contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false

let rec iterate_mlircl mlircl_string_list =
  match mlircl_string_list with
  | [] -> ""
  | h :: t -> 
    let var_regex = Str.regexp "var" in
    let str_regex = Str.regexp ": string" in
    let quote_regex = Str.regexp "\"" in
    let whitespace_regex = Str.regexp " " in
    let sail_regex = Str.regexp "Sail" in
    if str_contains h "Sail_"  then
      let parameter_list = String.split_on_char '<' h in
      let defname = Str.replace_first sail_regex "Tosa" (List.hd parameter_list) in
      "def " ^ defname ^ " : Tosa_Op<" ^ (String.concat "<" (List.tl parameter_list)) ^ "\n" ^ iterate_mlircl t

    else if str_contains h "summary" then
      let var_replace = Str.replace_first var_regex "let" h in
      Str.replace_first str_regex "" var_replace ^ "\n" ^ iterate_mlircl t

    else if str_contains h "description" then
      let var_replace = Str.replace_first var_regex "let" h in
      let type_regex_replace = Str.replace_first str_regex "" var_replace in
      let first_quote_replace = Str.replace_first quote_regex "[{" type_regex_replace in
      Str.global_replace quote_regex "}]" first_quote_replace ^ "\n" ^ iterate_mlircl t

    else if str_contains h "input1" then
      let rec further_inputs str_list num =
        match str_list with
        | [] -> ("", num)
        | h :: t ->
          if str_contains h "input"  then
            let in_type = String.split_on_char ':' h in
            let in_type = String.split_on_char '(' (List.nth in_type 1) in
            let further_input_strings, _ = further_inputs t (Int.add num 1) in 
             ", Tosa_" ^ Str.replace_first whitespace_regex "" (List.hd in_type) ^ "$input" ^ string_of_int(num) ^ further_input_strings, num 
          else
            let further_input_strings, _ = (further_inputs t (Int.add num 1)) in 
            ("" ^ further_input_strings, num)
      in
      let in_type = String.split_on_char ':' h in
      let in_type = String.split_on_char '(' (List.nth in_type 1) in
      let further_input_strings, _ = further_inputs t 2 in
      "let arguments = (ins Tosa_" ^ Str.replace_first whitespace_regex "" (List.hd in_type) ^ "$input1" ^ (further_input_strings) ^ ");" ^ "\n" ^ iterate_mlircl t

    else if str_contains h "output"  then
      let out_type = String.split_on_char ':' h in
      let out_type = String.split_on_char '(' (List.nth out_type 1) in
      "let results = (outs Tosa_" ^ Str.replace_first whitespace_regex "" (List.hd out_type) ^ ":$output);" ^ "\n" ^ iterate_mlircl t

    else
      "" ^ iterate_mlircl t

let rec ops_mlircl mlircl_string_list = 
  match mlircl_string_list with
  | [] -> ""
  | h :: t ->
    let sail_regex = Str.regexp "Sail_" in
    if str_contains h "Sail_"  then
      let parameter_list = String.split_on_char '<' h in
      let defname = Str.replace_first sail_regex "" (List.hd parameter_list) in
      "void " ^ defname ^ "::getCanonicalizationPatterns(RewritePatternSet &results,\nMLIRContext *context) {\nresults.add<AddZeroOptimization>(context);}\n" ^ ops_mlircl t
    else
      "" ^ ops_mlircl t

let rec canonicalization_mlircl mlircl_string_list = 
  match mlircl_string_list with
  | [] -> ""
  | h :: t ->
    let sail_regex = Str.regexp "Sail_" in
    if str_contains h "Sail_"  then
      let parameter_list = String.split_on_char '<' h in
      let defname = Str.replace_first sail_regex "" (List.hd parameter_list) in
      "NARY_SHAPE_INTER(tosa::" ^ defname ^ ")\n" ^ canonicalization_mlircl t
    else
      "" ^ canonicalization_mlircl t

let rec out_test_mlircl mlircl_string_list outtype =
  match mlircl_string_list with
  | [] -> ""
  | h :: t ->
    if str_contains h "Sail_"  then
      let instr_name = List.nth (String.split_on_char '"' h) 1 in
      if outtype = "test_param" then
        "func.func @test_" ^ instr_name ^ "(" ^ out_test_mlircl t outtype 
      else if outtype = "test_body" then
        "  %0 = \"tosa." ^ instr_name ^ "\" (" ^ out_test_mlircl t outtype 
      else
        "" ^ out_test_mlircl t outtype
    else if str_contains h "summary" then
      "" ^ out_test_mlircl t outtype
    else if str_contains h "description" then
      "" ^ out_test_mlircl t outtype
    else if str_contains h "input1" then
      if outtype = "test_param" then
        let rec further_inputs str_list num =
          match str_list with
          | [] -> ("", num)
          | h :: t ->
            if str_contains h "input"  then
              let in_type = String.split_on_char ':' h in
              let in_type = String.lowercase_ascii(List.hd (String.split_on_char '(' (List.nth in_type 1))) in
              let in_type = in_type ^ "<13x21x3xf32>" in
              let further_input_strings, _ = further_inputs t (Int.add num 1) in 
               ", %arg" ^ string_of_int(num) ^ ": " ^ (in_type) ^ further_input_strings, num 
            else
              let further_input_strings, _ = (further_inputs t (Int.add num 1)) in 
              ("" ^ further_input_strings, num)
        in

        let in_type = String.split_on_char ':' h in
        let in_type = String.lowercase_ascii (List.hd (String.split_on_char '(' (List.nth in_type 1))) in
        let in_type = in_type ^ "<13x21x3xf32>" in
        let further_input_strings, _ = further_inputs t 1 in
        "%arg0: " ^ in_type ^ (further_input_strings) ^ ") -> " ^ out_test_mlircl t outtype
      else if outtype = "test_body" then
        let rec further_params str_list num =
          match str_list with
          | [] -> ("", num)
          | h :: t ->
            if str_contains h "input"  then
              let further_input_strings, _ = further_params t (Int.add num 1) in 
               ", %arg" ^ string_of_int(num) ^ further_input_strings, num 
            else
              let further_input_strings, _ = (further_params t (Int.add num 1)) in 
              ("" ^ further_input_strings, num)
        in

        let rec further_types str_list=
          match str_list with
          | [] -> ""
          | h :: t ->
            if str_contains h "input"  then
              let in_type = String.split_on_char ':' h in
              let in_type = String.lowercase_ascii (List.hd (String.split_on_char '(' (List.nth in_type 1))) in
              let in_type = in_type ^ "<13x21x3xf32>" in
              let further_input_strings = further_types t in 
                ", " ^ in_type ^ further_input_strings
            else
              let further_input_strings = (further_types t) in 
              ("" ^ further_input_strings)
        in

        let in_type = String.split_on_char ':' h in
        let in_type = String.lowercase_ascii (List.hd (String.split_on_char '(' (List.nth in_type 1))) in
        let in_type = in_type ^ "<13x21x3xf32>" in
        let further_input_params, _ = further_params t 1 in
        let further_in_types = further_types t in
        "arg0" ^ further_input_params ^ ") : (" ^ in_type ^ further_in_types ^ ") -> " ^ out_test_mlircl t outtype
      else
        "" ^ out_test_mlircl t outtype

    else if str_contains h "output"  then
      if outtype = "test_param" then
        let out_type = String.split_on_char ':' h in
        let out_type = String.lowercase_ascii (List.hd(String.split_on_char '(' (List.nth out_type 1))) in
        let out_type = out_type ^ "<13x21x3xf32>" in
        out_type ^ " {\n" ^ out_test_mlircl t outtype
      else if outtype = "test_body" then
        let out_type = String.split_on_char ':' h in
        let out_type = String.lowercase_ascii (List.hd(String.split_on_char '(' (List.nth out_type 1))) in
        let out_type = out_type ^ "<13x21x3xf32>" in
        out_type ^ "\n  return %0 : " ^ out_type ^ "\n} \n" ^ out_test_mlircl t outtype
      else 
        "" ^ out_test_mlircl t outtype
    else
      "" ^ out_test_mlircl t outtype

let rec binops_mlircl mlircl_string_list outtype=
  match mlircl_string_list with
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
      let instr_name = List.nth (String.split_on_char '"' h) 1 in
      if outtype = "norm" then 
        (find_return_type t) ^ " " ^ instr_name ^ "(" ^ binops_mlircl t outtype 
      else if outtype = "_" || outtype = "_out" then 
        (find_return_type t) ^ "& " ^ instr_name ^ outtype ^ "(" ^ binops_mlircl t outtype 
      else
        "" ^ binops_mlircl t outtype

    else if str_contains h "summary" then
      "" ^ binops_mlircl t outtype
    else if str_contains h "description" then
      "" ^ binops_mlircl t outtype

    else if str_contains h "input1" then
      let rec further_inputs str_list =
        match str_list with
        | [] -> ""
        | h :: t ->
          if str_contains h "input"  then
            let in_type = String.split_on_char ':' h in
            let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
            let further_input_strings = further_inputs t in 
            "const " ^ in_type ^ "& other" ^ further_input_strings
          else
            let further_input_strings = (further_inputs t) in 
            ("" ^ further_input_strings)
      in
      if outtype = "norm" then 
        let in_type = String.split_on_char ':' h in
        let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
        "const " ^ in_type ^ "& self, " ^ further_inputs t ^ ", const Scalar& alpha) {" ^ binops_mlircl t outtype
      else if outtype = "_" then 
        let in_type = String.split_on_char ':' h in
        let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
        in_type ^ "& self, " ^ further_inputs t ^ ", const Scalar& alpha) {" ^ binops_mlircl t outtype

      else if outtype = "_out" then 
        let in_type = String.split_on_char ':' h in
        let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
        "const " ^ in_type ^ "& self, " ^ further_inputs t ^ ", const Scalar& alpha," ^ find_return_type t ^ "& result) {"^ binops_mlircl t outtype 
      else
       "" ^ binops_mlircl t outtype

    else if str_contains h "output" then
      if outtype = "norm" || outtype = "_" then
        "return self;}\n" ^ binops_mlircl t outtype
      else if outtype = "_out" then
        "return result;}\n" ^ binops_mlircl t outtype
      else
      "" ^ binops_mlircl t outtype
    else
      "" ^ binops_mlircl t outtype

let rec nfunctions_mlircl mlircl_string_list outtype=
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
  let instr_name = ref (find_instr_name mlircl_string_list) in

  match mlircl_string_list with
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
      let rec nfunctions_inner_mlircl slist outtype instr_name =
        match slist with
        | [] -> ""
        | h :: t ->
        if str_contains h "summary" then
          "" ^ nfunctions_inner_mlircl t outtype instr_name
        else if str_contains h "description" then
          "" ^ nfunctions_inner_mlircl t outtype instr_name
        else if str_contains h "input1" then
          (*TODO make names able to be changed*)
          let rec further_inputs str_list =
            match str_list with
            | [] -> ""
            | h :: t ->
              if str_contains h "input"  then
                let in_type = String.split_on_char ':' h in
                let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
                let further_input_strings = further_inputs t in 
                in_type ^ " other" ^ further_input_strings
              else
                let further_input_strings = (further_inputs t) in 
                ("" ^ further_input_strings)
          in
          if outtype = "norm" then 
            let in_type = String.split_on_char ':' h in
            let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
            in_type ^ " self, " ^ further_inputs t ^ ", *, Scalar alpha=1) -> " ^ nfunctions_inner_mlircl t outtype instr_name
          else if outtype = "_" then 
            let in_type = String.split_on_char ':' h in
            let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
            in_type ^ "(a!) self, " ^ further_inputs t ^ ", *, Scalar alpha=1) -> " ^ nfunctions_inner_mlircl t outtype instr_name
          else if outtype = "_out" then 
            let in_type = String.split_on_char ':' h in
            let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
            in_type ^ " self, " ^ further_inputs t ^ ", Scalar alpha=1," ^ find_return_type t ^ "(a!) out) ->" ^ nfunctions_inner_mlircl t outtype instr_name 
          else
           "" ^ nfunctions_inner_mlircl t outtype instr_name
        else if str_contains h "output" then
          let out_type = String.split_on_char ':' h in
          let out_type = List.hd(String.split_on_char '(' (List.nth out_type 1)) in
          if outtype = "norm" then
            out_type ^ "\n variants: function\n dispatch:\n    CPU: " ^ !instr_name ^  nfunctions_inner_mlircl t outtype instr_name
          else if outtype = "_" then
            out_type ^ "(a!)\n variants: method\n dispatch:\n    CPU: " ^ !instr_name ^ outtype ^ nfunctions_inner_mlircl t outtype instr_name
          else if outtype = "_out" then
            out_type ^ "(a!)\n variants: function\n dispatch:\n    CPU: " ^ !instr_name ^ outtype ^ nfunctions_inner_mlircl t outtype instr_name
          else
          "" ^ nfunctions_inner_mlircl t outtype instr_name
        else
          "" ^ nfunctions_inner_mlircl t outtype instr_name
      in

      if outtype = "norm" then 
        "- func: " ^ !instr_name ^ "(" ^ nfunctions_inner_mlircl t outtype instr_name
      else if outtype = "_" then 
        "- func: " ^ !instr_name ^ outtype ^ "(" ^ nfunctions_inner_mlircl t outtype instr_name
      else if outtype = "_out" then 
        "- func: " ^ !instr_name ^ ".out(" ^ nfunctions_inner_mlircl t outtype instr_name
      else
        "" ^ nfunctions_inner_mlircl t outtype instr_name
    else
      "" ^ nfunctions_mlircl t outtype

let rec rtypes_mlircl mlircl_string_list =
  match mlircl_string_list with
  | [] -> ""
  | h :: t ->
    if str_contains h "Sail_"  then
      let instr_name = List.nth (String.split_on_char '"' h) 1 in
      "// Add this to corresponding if statement in visitOperation \n" ^ "Aten" ^ String.capitalize_ascii instr_name ^ "Op\n"
    else
       "" ^ rtypes_mlircl t

let rec torch_to_tosa_mlircl mlircl_string_list =
  match mlircl_string_list with
  | [] -> ""
  | h :: t ->
    if str_contains h "Sail_"  then
      let instr_name = List.nth (String.split_on_char '"' h) 1 in
      let sail_regex = Str.regexp "Sail_" in
      let parameter_list = String.split_on_char '<' h in
      let defname = Str.replace_first sail_regex "tosa::" (List.hd parameter_list) in
      ("// Replace XXXX and add it to the correct pattern\n" ^
      "INSERT_XXXX_PATTERN(" ^ "Aten" ^ String.capitalize_ascii instr_name ^ "Op, " ^ defname ^ ")\n")
    else
       "" ^ torch_to_tosa_mlircl t

let rec uncategorized_mlircl mlircl_string_list =
  match mlircl_string_list with
  | [] -> ""
  | h :: t ->
    if str_contains h "Sail_"  then
      let instr_name = List.nth (String.split_on_char '"' h) 1 in
      let aten_name = "Aten" ^ String.capitalize_ascii instr_name in
      ("if (auto " ^ instr_name ^ " = dyn_cast<" ^ aten_name ^ "Op>(op)) {\n"
       ^ aten_name ^ "Op::Adaptor adaptor(operands);\n"
       ^ "Type dtype = converter->convertType(" ^ instr_name
       ^ ".getType()).cast<RankedTensorType>().getElementType();\n"
       ^ "Value lhs = convertScalarToDtype(b, loc, payloadArgs[0], dtype);\n"
       ^ "Value rhs = convertScalarToDtype(b, loc, payloadArgs[1], dtype);\n")
       ^ "return lhs;}\n"
    else
       "" ^ uncategorized_mlircl t

let rec shape_lib_gen_mlircl mlircl_string_list=
  match mlircl_string_list with
  | [] -> ""
  | h :: t ->
    if str_contains h "Sail_"  then
      let instr_name = List.nth (String.split_on_char '"' h) 1 in
      "def aten〇" ^ instr_name ^ "(" ^ shape_lib_gen_mlircl t

    else if str_contains h "summary" then
      "" ^ shape_lib_gen_mlircl t
    else if str_contains h "description" then
      "" ^ shape_lib_gen_mlircl t

    else if str_contains h "input1" then
      let rec further_inputs str_list =
        match str_list with
        | [] -> ""
        | h :: t ->
          if str_contains h "input"  then
            let in_type = String.split_on_char ':' h in
            let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
            let further_input_strings = further_inputs t in 
            if str_contains in_type "Tensor" then
              ", other: List[int]" ^ further_input_strings
            else
              "other: int" ^ further_input_strings
          else
            let further_input_strings = (further_inputs t) in 
            ("" ^ further_input_strings)
      in
      let in_type = String.split_on_char ':' h in
      let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
      if str_contains in_type "Tensor" then
        "self: List[int]" ^ further_inputs t ^ ", alpha: float = 1) -> " ^ shape_lib_gen_mlircl t
      else
        "self: int" ^ further_inputs t ^ ") ->" ^ shape_lib_gen_mlircl t

    else if str_contains h "output" then
      let out_type = String.split_on_char ':' h in
      let out_type = List.hd(String.split_on_char '(' (List.nth out_type 1)) in
      if str_contains out_type "Tensor" then
        "List[int]:\n    return upstream_shape_functions.broadcast(self, other)\n" ^ shape_lib_gen_mlircl t
      else
        "int:\n    return upstream_shape_functions.broadcast(self, other)\n" ^ shape_lib_gen_mlircl t
    else
      "" ^ shape_lib_gen_mlircl t

let rec torch_ods_gen_mlircl mlircl_string_list =
  match mlircl_string_list with
  | [] -> ""
  | h :: t ->
    if str_contains h "Sail_"  then
      let instr_name = List.nth (String.split_on_char '"' h) 1 in
      "\"aten::" ^ instr_name ^ " : (" ^ torch_ods_gen_mlircl t

    else if str_contains h "summary" then
      "" ^ torch_ods_gen_mlircl t
    else if str_contains h "description" then
      "" ^ torch_ods_gen_mlircl t

    else if str_contains h "input1" then
      let rec further_inputs str_list =
        match str_list with
        | [] -> ""
        | h :: t ->
          if str_contains h "input"  then
            let in_type = String.split_on_char ':' h in
            let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
            let further_input_strings = further_inputs t in 
              ", " ^ in_type ^ further_input_strings
          else
            let further_input_strings = (further_inputs t) in 
            ("" ^ further_input_strings)
      in
      let in_type = String.split_on_char ':' h in
      let in_type = List.hd (String.split_on_char '(' (List.nth in_type 1)) in
      in_type ^ further_inputs t ^ ", Scalar) -> (" ^ torch_ods_gen_mlircl t

    else if str_contains h "output" then
      let out_type = String.split_on_char ':' h in
      let out_type = List.hd(String.split_on_char '(' (List.nth out_type 1)) in
       out_type ^ ")\",\n" ^ torch_ods_gen_mlircl t
    else
      "" ^ torch_ods_gen_mlircl t

let sail_to_tosa clause outtype =
  let mlircl_string = Pretty_print_sail.to_string(Pretty_print_sail.doc_mlircl clause) in
  let mlircl_string_list = String.split_on_char '\n' mlircl_string in
  if outtype = "td" then
    iterate_mlircl mlircl_string_list ^ "} \n"
  else if outtype = "ops" then
    ops_mlircl mlircl_string_list
  else if outtype = "canonicalization" then
    canonicalization_mlircl mlircl_string_list
  else if outtype = "test_param" then
    out_test_mlircl mlircl_string_list outtype ^ out_test_mlircl mlircl_string_list "test_body"
  else if outtype = "binops" then
    (binops_mlircl mlircl_string_list "norm" ^ "\n" ^
    binops_mlircl mlircl_string_list "_" ^ "\n" ^
    binops_mlircl mlircl_string_list "_out" ^ "\n")
  else if outtype = "nfunctions" then
    (nfunctions_mlircl mlircl_string_list "norm" ^ "\n" ^
     nfunctions_mlircl mlircl_string_list "_" ^ "\n" ^
     nfunctions_mlircl mlircl_string_list "_out" ^ "\n")
  else if outtype = "rtypes" then
    rtypes_mlircl mlircl_string_list
  else if outtype = "torch_to_tosa" then
    torch_to_tosa_mlircl mlircl_string_list
  else if outtype = "uncategorized" then
    uncategorized_mlircl mlircl_string_list
  else if outtype = "shape_lib_gen" then
    shape_lib_gen_mlircl mlircl_string_list
  else if outtype = "torch_ods_gen" then
    torch_ods_gen_mlircl mlircl_string_list
  else
    ""
let rec tosa_mlircl mlircls outtype  =
  match mlircls with
  | [] -> ""
  | clause :: clauses -> sail_to_tosa clause outtype ^ tosa_mlircl clauses outtype

let rec tosa_mlirdef (MLIRD_aux (MLIRD_cl (id, mlircls), _)) outtype =
  match mlircls with
  | [] -> failwith "No mlir clause"
  | _ -> tosa_mlircl mlircls outtype

let compile_ast env effect_info output_chan ast opt_pytorch opt_tosa opt_torch_mlir =
  let td_def def outtype = 
    match def with
    | DEF_mlirdef mlirdef -> tosa_mlirdef mlirdef outtype
    | _ -> ""
  in

  let rec process_defs_to_tosa outtype = function
    | [] -> ""
    | def :: defs ->
       let td  =  td_def def outtype in
       (*if String.length td > 0 then*)
         td ^  process_defs_to_tosa outtype defs
       (*else
         process_defs_to_tosa outtype defs*)
  in

  let outtype = "td" in
  let tosa_tablegen = process_defs_to_tosa outtype ast.defs in

  let outtype = "ops" in
  let tosa_ops = process_defs_to_tosa outtype ast.defs in

  let outtype = "canonicalization" in
  let tosa_canonicalization = process_defs_to_tosa outtype ast.defs in

  let outtype = "test_param" in
  let tosa_test = (process_defs_to_tosa outtype ast.defs) in

  let outtype = "binops" in
  let tosa_binops = (process_defs_to_tosa outtype ast.defs) in

  let outtype = "nfunctions" in
  let tosa_nfunctions = (process_defs_to_tosa outtype ast.defs) in

  let outtype = "rtypes" in
  let tosa_rtypes = (process_defs_to_tosa outtype ast.defs) in

  let outtype = "shape_lib_gen" in
  let tosa_shape_lib_gen = (process_defs_to_tosa outtype ast.defs) in

  let outtype = "torch_ods_gen" in
  let tosa_torch_ods_gen = (process_defs_to_tosa outtype ast.defs) in

  let outtype = "torch_to_tosa" in
  let tosa_torch = (process_defs_to_tosa outtype ast.defs) in

  let outtype = "uncategorized" in
  let tosa_uncategorized = (process_defs_to_tosa outtype ast.defs) in

  let fname0 = "generated_definitions/mlir/llvm/TosaOps.td" in
  let fname1 = "generated_definitions/mlir/llvm/TosaOps.cpp" in
  let fname2 = "generated_definitions/mlir/llvm/TosaCanonicalizations.cpp" in
  let fname3 = "generated_definitions/mlir/llvm/test_tosa_ops.mlir" in
  let fname4 = "generated_definitions/mlir/pytorch/BinaryOps.cpp" in
  let fname5 = "generated_definitions/mlir/pytorch/native_functions.yaml" in
  let fname6 = "generated_definitions/mlir/torch-mlir/RefineTypes.cpp" in
  let fname7 = "generated_definitions/mlir/torch-mlir/shape_lib_gen.py" in
  let fname8 = "generated_definitions/mlir/torch-mlir/torch_ods_gen.py" in
  let fname9 = "generated_definitions/mlir/torch-mlir/TorchToTosa.cpp" in
  let fname10 = "generated_definitions/mlir/torch-mlir/Uncategorized.cpp" in
  
  let output_chan = open_out fname0 in
  Printf.fprintf output_chan "%s" tosa_tablegen;
  close_out output_chan;

  let output_chan = open_out fname1 in
  Printf.fprintf output_chan "%s" tosa_ops;
  close_out output_chan;

  let output_chan = open_out fname2 in
  Printf.fprintf output_chan "%s" tosa_canonicalization;
  close_out output_chan;

  let output_chan = open_out fname3 in
  Printf.fprintf output_chan "%s" tosa_test;
  close_out output_chan;

  let output_chan = open_out fname4 in
  Printf.fprintf output_chan "%s" tosa_binops;
  close_out output_chan;

  let output_chan = open_out fname5 in
  Printf.fprintf output_chan "%s" tosa_nfunctions;
  close_out output_chan;

  let output_chan = open_out fname6 in
  Printf.fprintf output_chan "%s" tosa_rtypes;
  close_out output_chan;

  let output_chan = open_out fname7 in
  Printf.fprintf output_chan "%s" tosa_shape_lib_gen;
  close_out output_chan;

  let output_chan = open_out fname8 in
  Printf.fprintf output_chan "%s" tosa_torch_ods_gen;
  close_out output_chan;

  let output_chan = open_out fname9 in
  Printf.fprintf output_chan "%s" tosa_torch;
  close_out output_chan;

  let output_chan = open_out fname10 in
  Printf.fprintf output_chan "%s" tosa_uncategorized;
  close_out output_chan;

  print_endline(tosa_nfunctions)
