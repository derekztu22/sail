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

let qemu_execute_string_parse funcl_string_list =
    let mm_regex = Str.regexp_string "_MM" in
    let leftp_regex = Str.regexp_string "(" in
    let rightp_regex = Str.regexp_string ")" in
    let whitespace_regex = Str.regexp_string " " in
    let comma_regex = Str.regexp_string "," in

    let rec fn_setup funcl_string_list = 
      match funcl_string_list with
      | [] -> "", ""
      | h :: t ->
        if str_contains h "execute" then
          let inst_name = String.lowercase_ascii(List.nth (String.split_on_char ' ' (List.hd (Str.split mm_regex h) ^ "_MM")) 1) in
          let params = List.nth (Str.split mm_regex h) 1 in
          let params = List.hd (String.split_on_char '=' params) in
          let params = Str.global_replace leftp_regex "" params in
          let params = Str.global_replace rightp_regex "" params in
          let params = Str.global_replace whitespace_regex "" params in
          let params = String.split_on_char ',' params in
          
          let rec setup_fn_params params =
            match params with
            | [] -> "CPURISCVState *env);\n"
            | h :: t ->
              if str_contains h "vs2" then
                "void* vs2, " ^ setup_fn_params t
              else if str_contains h "vs1" then
                "void* vs1," ^ setup_fn_params t
              else if str_contains h "ms1" then
                "void* ms1," ^ setup_fn_params t
              else if str_contains h "ms2" then
                "void* ms2," ^ setup_fn_params t
              else if str_contains h "md" then
                "void * md," ^ setup_fn_params t
              else if str_contains h "ms3" then
                "void * vs3," ^ setup_fn_params t
              else if str_contains h "rs1" then
                "uint64_t base," ^ setup_fn_params t
              else
                setup_fn_params t
          in
          "typedef void " ^ inst_name ^ "_fn(" ^ setup_fn_params params, inst_name

        else
          fn_setup t
    in
    let fn_setup_def, inst_name = fn_setup funcl_string_list in

    let rec body_func_execute inst_name funcl_string_list n =
      match funcl_string_list with
      | [] -> "", n
      | h :: t ->
        let comma_regex = Str.regexp_string "," in
        let rightp_regex = Str.regexp_string ")" in
        let rightb_regex = Str.regexp_string "]" in
        let leftp_regex = Str.regexp_string "(" in
        let semicolon_regex = Str.regexp_string ";" in

        let get_idx idx = 
          (* Calcualted idx *)
          if str_contains h "_atom" then
            let atom_regex = Str.regexp_string "_atom" in

            let rec idx_calc idx_str = 
              let lhs = List.hd (Str.bounded_split atom_regex idx_str 2) in 
              let rhs = List.nth (Str.bounded_split atom_regex idx_str 2) 1 in
              let rhs = Str.global_replace leftp_regex "" rhs in
              let rhs = Str.global_replace rightp_regex "" rhs in
              let rhs = Str.global_replace rightb_regex "" rhs in
              let rhs = Str.global_replace semicolon_regex "" rhs in
        
              let get_op atom_str = 
                if str_contains atom_str "add" then
                  "+"
                else if str_contains atom_str "sub" then
                  "-"
                else if str_contains atom_str "mult" then
                  "*"
                else
                  ""
              in

              let op = get_op lhs in
              let right_var = List.hd (List.rev (String.split_on_char ',' rhs)) in
              if str_contains rhs "atom" then
                let rregex = Str.regexp_string ("," ^ right_var) in
                right_var ^ op ^
                (idx_calc (List.hd (Str.split rregex rhs)))
              else
                let left_var = List.hd (String.split_on_char ',' rhs) in 
                right_var ^ op ^ left_var
            in
            idx_calc idx 
          (* Non-calculated idx *)
          else
            let split = Str.split comma_regex idx in
            if List.length split > 1 then
              let idx = List.nth (Str.split comma_regex idx) 1 in
              let idx = Str.global_replace rightp_regex "" idx in
              let idx = Str.global_replace semicolon_regex "" idx in
              idx
            else 
              let idx = List.hd (String.split_on_char ']' (List.hd split)) in
              let idx = List.nth(String.split_on_char '[' idx) 1  in
              idx
        in

        if str_contains h "foreach" then
          let foreach_regex = Str.regexp_string "foreach" in
          let from_regex = Str.regexp_string "from" in
          let to_regex = Str.regexp_string "to " in
          let by_regex = Str.regexp_string "by" in
          let leftp_regex = Str.regexp_string "(" in
          let whitespace_regex = Str.regexp_string " " in
          let one_in_inc_regex = Str.regexp_string "1 in inc" in
          
          let idx = List.hd (Str.split from_regex h) in
          let idx = List.nth (String.split_on_char '(' idx) 1 in
          let idx = Str.global_replace whitespace_regex "" idx in

          let range  = List.hd (Str.split by_regex h) in
          let range = List.nth (Str.split to_regex range) 1 in
          let range_regex = Str.regexp_string range in

          let for_loop = Str.replace_first foreach_regex "for" h in
          let for_loop = Str.replace_first from_regex "=" for_loop in
          let for_loop = Str.replace_first to_regex "; " for_loop in
          let for_loop = Str.replace_first by_regex ";" for_loop in
          let for_loop = Str.replace_first leftp_regex "(uint32_t " for_loop in
          let for_loop = Str.replace_first one_in_inc_regex ("++" ^ idx) for_loop in
          if str_contains inst_name "loadz" || str_contains inst_name "storez" then
            let for_loop = Str.replace_first range_regex (idx ^ "< 16*16")  for_loop in
            let further_execution, next = body_func_execute inst_name t (n+1) in
            for_loop ^ "\\\n" ^ further_execution, next 
          else
            let for_loop = Str.replace_first range_regex (idx ^ "< 16")  for_loop in
            let further_execution, next = body_func_execute inst_name t (n+1) in
            for_loop ^ "\\\n" ^ further_execution, next 

        (* Get base address *)
        else if str_contains h "data_get_addr" then

          let to_bits_regex = Str.regexp_string "to_bits(" in
          let addr_idx = List.nth (Str.split to_bits_regex h) 1 in
          let addr_idx = List.hd (String.split_on_char ')' addr_idx) in
          let addr_idx = List.nth (String.split_on_char ',' addr_idx) 1 in
          let pc = "uintptr_t ra = GETPC();\\\n" in
          (*let addr = "uint64_t addr = base + " ^ addr_idx ^ ";\\\n" in*)
          let addr = "uint64_t addr = base +" ^ addr_idx ^ ";\\\n" in
          if str_contains h "Read" then
            let further_execution, next = body_func_execute inst_name t (n) in
            pc ^ addr ^ "int32_t * cur = ((int32_t*) md  + i);\\\n" ^ further_execution, next
          else if str_contains h "Write" then
            let further_execution, next = body_func_execute inst_name t (n) in
            pc ^ addr ^ "int32_t data = *((int32_t*) vs3  + i);\\\n" ^ further_execution, next
          else
            body_func_execute inst_name t n

        (* Load *)
        else if str_contains h "mem_read" then
          let further_execution, next = body_func_execute inst_name t (n) in
          "*cur = cpu_ldl_data_ra(env, adjust_addrm(env, addr), ra);\\\n" ^ further_execution, next

        (* Store *)
        else if str_contains h "mem_write_value" then
          let further_execution, next = body_func_execute inst_name t (n) in
          "cpu_stl_data_ra(env, addr, data, ra);\\\n" ^ further_execution, next

        else if str_contains h "let" then 
          let let_regex = Str.regexp_string "let" in
          let vector_regex = Str.regexp_string "plain_vector_access" in
          let comma_regex = Str.regexp_string "," in
          let rightp_regex = Str.regexp_string ")" in
          let leftp_regex = Str.regexp_string "(" in
          let semicolon_regex = Str.regexp_string ";" in
          let comma_whitespace_regex = Str.regexp_string ", " in
          let num_elem_regex = Str.regexp_string "num_elem" in

          let h = Str.global_replace num_elem_regex "16" h in 

          if str_contains h "plain_vector_access" then
            let let_str = List.hd (String.split_on_char '=' (Str.replace_first let_regex "int32_t" h)) in
            let idx = List.nth (Str.split vector_regex h) 1 in
            let idx = get_idx idx in
            let idn_regex = Str.regexp_string "__idn" in
            let idx = Str.global_replace idn_regex "16" idx in 
      
            if str_contains h "vs1" then
              let further_execution, next = body_func_execute inst_name t (n) in
              let_str ^ "= *((int32_t*) vs1 +" ^ idx ^ ");\\\n" ^ further_execution, next
            else if str_contains h "vs2" then
              let further_execution, next = body_func_execute inst_name t (n) in
              let_str ^ "= *((int32_t*) vs2 +" ^ idx ^ ");\\\n" ^ further_execution, next
            else if str_contains h "ms2" then
              let further_execution, next = body_func_execute inst_name t (n) in
              let_str ^ "= *((int32_t*) ms2 +" ^ idx ^ ");\\\n" ^ further_execution, next
            else if str_contains h "ms1" then
              let further_execution, next = body_func_execute inst_name t (n) in
              let_str ^ "= *((int32_t*) ms1 +" ^ idx ^ ");\\\n" ^ further_execution, next
            else if str_contains h "md" then
              let further_execution, next = body_func_execute inst_name t (n) in
              let_str ^ "= *((int32_t*) md +" ^ idx ^ ");\\\n" ^ further_execution, next 
            else
              body_func_execute inst_name t (n)

          else if str_contains h "mult_atom" then
            let mult_atom_regex = Str.regexp_string "mult_atom" in
            let let_str = List.hd (String.split_on_char '=' (Str.replace_first let_regex "int32_t" h)) in
            let vars = List.nth (Str.split mult_atom_regex h) 1 in
            let vars = Str.global_replace rightp_regex "" vars in 
            let vars = Str.global_replace leftp_regex "" vars in 
            let vars = Str.global_replace semicolon_regex "" vars in 
            let vars = Str.split comma_whitespace_regex vars in
            let further_execution, next = body_func_execute inst_name t (n) in
            let_str ^ " = " ^ List.hd vars ^ "*" ^ List.nth vars 1 ^ ";\\\n" ^ further_execution, next
            
          else if  str_contains h "add_bits_int" then
            let add_atom_regex = Str.regexp_string "add_bits_int" in
            let let_str = List.hd (String.split_on_char '=' (Str.replace_first let_regex "int32_t" h)) in
            let vars = List.nth (Str.split add_atom_regex h) 1 in
            let vars = Str.global_replace rightp_regex "" vars in 
            let vars = Str.global_replace leftp_regex "" vars in 
            let vars = Str.global_replace semicolon_regex "" vars in 
            let vars = Str.split comma_whitespace_regex vars in
            let further_execution, next = body_func_execute inst_name t (n) in
            let_str ^ " = " ^ List.hd vars ^ "+" ^ List.nth vars 1 ^ ";\\\n" ^ further_execution, next

          else if  str_contains h "sub_vec_int" then
            let sub_atom_regex = Str.regexp_string "sub_vec_int" in
            let let_str = List.hd (String.split_on_char '=' (Str.replace_first let_regex "int32_t" h)) in
            let vars = List.nth (Str.split sub_atom_regex h) 1 in
            let vars = Str.global_replace rightp_regex "" vars in 
            let vars = Str.global_replace leftp_regex "" vars in 
            let vars = Str.global_replace semicolon_regex "" vars in 
            let vars = Str.split comma_whitespace_regex vars in
            let further_execution, next = body_func_execute inst_name t (n) in
	    let_str ^ " = " ^ List.hd vars ^ "-" ^ List.nth vars 1 ^ ";\\\n" ^ further_execution, next

          else if (str_contains h ":") && (str_contains h "int") && (str_contains h "=") then
            let maybe_digit = List.nth (String.split_on_char '=' h) 1 in
            let maybe_digit = Str.global_replace whitespace_regex "" maybe_digit in
            let maybe_digit = Str.global_replace semicolon_regex "" maybe_digit in
            let digit_regex = Str.regexp "[0-9]+" in
            if Str.string_match digit_regex maybe_digit 0 then
              let let_regex = Str.regexp_string "let" in
              let int_regex = Str.regexp_string ": int" in
              let let_str = Str.replace_first let_regex "int32_t" h in
              let let_str = List.hd (String.split_on_char ':' let_str) in
              let further_execution, next = body_func_execute inst_name t (n) in
              let_str ^ "=" ^ maybe_digit ^ ";\\\n" ^ further_execution, next

            else
              body_func_execute inst_name t n

          else
            body_func_execute inst_name t n
        (* END LET *)
        else if str_contains h "result[" then
          let num_elem_regex = Str.regexp_string "num_elem" in

          let h = Str.global_replace num_elem_regex "16" h in 

          let get_result_idx_var h = 
            let var = List.nth (String.split_on_char '=' h) 1 in
              let idx = List.hd (String.split_on_char '=' h ) in
     
            if str_contains var "plain_vector_access" then
  
              let vector_regex = Str.regexp_string "plain_vector_access" in
              let var = List.nth (Str.split vector_regex h) 1 in
              if str_contains h "vs2" then
                get_idx idx, "*((int32_t*) vs2 +" ^ (get_idx var) ^ ")"
              else if str_contains h "vs1" then
                get_idx idx, "*((int32_t*) vs1 +" ^ (get_idx var) ^ ")"
              else if str_contains h "ms1" then
                get_idx idx, "*((int32_t*) ms1 +" ^ (get_idx var) ^ ")"
              else if str_contains h "ms2" then
                get_idx idx, "*((int32_t*) ms2 +" ^ (get_idx var) ^ ")"
              else
                get_idx idx, "*((int32_t*) vs2 +" ^ (get_idx var) ^ ")"
            else
              let idx = List.hd (String.split_on_char '=' h ) in
              get_idx idx, var
          in

          let idx, var = get_result_idx_var h in
          let idn_regex = Str.regexp_string "__idn" in

          let idx = Str.global_replace idn_regex "16" idx in 
          let further_execution, next = body_func_execute inst_name t (n) in
          "*((int32_t*) md + " ^ idx ^ ") = " ^ var ^ ";\\\n" ^ further_execution, next

        (*else if (Str.global_replace whitespace_regex "" h) = "}" then
          "}\\\n" ^ body_func_execute t
        else if (Str.global_replace whitespace_regex "" h) = "};" then
          "}\\\n" ^ body_func_execute t*)
        else if str_contains h "RETIRE_SUCCESS" then
          "", n
        else
          body_func_execute inst_name t n
        (* End body func exetute*)
    in
    let quote_regex = Str.regexp_string "'" in
    let body_func, num_bracket =  body_func_execute inst_name funcl_string_list 0 in
    let body_func = Str.global_replace quote_regex "" body_func in
 
    let rec add_bracket body n =
      if n = 0 then
        body
      else 
        let body = body ^ "}\\\n" in
        add_bracket body (n-1)
    in
    let body_func = add_bracket body_func num_bracket in

    let rec x_byte_setup funcl_string_list = 
      match funcl_string_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "execute" then
          let params = List.nth (Str.split mm_regex h) 1 in
          let params = List.hd (String.split_on_char '=' params) in
          let params = Str.global_replace leftp_regex "" params in
          let params = Str.global_replace rightp_regex "" params in
          let params = Str.global_replace whitespace_regex "" params in
          let params = String.split_on_char ',' params in
          
          let rec setup_fn_params params =
            match params with
            | [] -> "CPURISCVState *env) {\\\n"
            | h :: t ->
              if str_contains h "vs2" then
                "void* vs2, " ^ setup_fn_params t
              else if str_contains h "vs1" then
                "void* vs1," ^ setup_fn_params t
              else if str_contains h "ms1" then
                "void* ms1," ^ setup_fn_params t
              else if str_contains h "ms2" then
                "void* ms2," ^ setup_fn_params t
              else if str_contains h "md" then
                "void * md," ^ setup_fn_params t
              else if str_contains h "ms3" then
                "void * vs3," ^ setup_fn_params t
              else if str_contains h "rs1" then
                "uint64_t base," ^ setup_fn_params t
              else
                setup_fn_params t
          in
          "static void do_##NAME (" ^  setup_fn_params params

        else
          x_byte_setup t
    in


    let do_x_byte = "#define " ^ String.uppercase_ascii(inst_name) ^ "X(NAME)\\\n" ^
                    x_byte_setup funcl_string_list ^ body_func ^ "}\n" in

    let rvmmcall_def = "RVMMCALL(" ^ String.uppercase_ascii(inst_name) ^ "X," ^ inst_name ^ "_w)\n"  in

    let rec do_x_x_params_setup inst_name funcl_string_list = 
      match funcl_string_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "execute" then
          let params = List.nth (Str.split mm_regex h) 1 in
          let params = List.hd (String.split_on_char '=' params) in
          let params = Str.global_replace leftp_regex "" params in
          let params = Str.global_replace rightp_regex "" params in
          let params = Str.global_replace whitespace_regex "" params in
          let params = String.split_on_char ',' params in
          
          let rec setup_fn_params inst_name params =
            match params with
            | [] -> "CPURISCVState *env, " ^ inst_name ^ "_fn fn) {\n"
            | h :: t ->
              if str_contains h "vs2" then
                "void* vs2, " ^ setup_fn_params inst_name t
              else if str_contains h "vs1" then
                "void* vs1," ^ setup_fn_params inst_name t
              else if str_contains h "ms1" then
                "void* ms1," ^ setup_fn_params inst_name t
              else if str_contains h "ms2" then
                "void* ms2," ^ setup_fn_params inst_name t
              else if str_contains h "md" then
                "void * md," ^ setup_fn_params inst_name t
              else if str_contains h "ms3" then
                "void * vs3," ^ setup_fn_params inst_name t
              else if str_contains h "rs1" then
                "uint64_t base," ^ setup_fn_params inst_name t
              else
                setup_fn_params inst_name t
          in
          "static void do_" ^ inst_name ^ "_x(" ^  setup_fn_params inst_name params

        else
          do_x_x_params_setup inst_name t
    in

    let rec do_x_x_body_setup  funcl_string_list = 
      match funcl_string_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "execute" then
          let params = List.nth (Str.split mm_regex h) 1 in
          let params = List.hd (String.split_on_char '=' params) in
          let params = Str.global_replace leftp_regex "" params in
          let params = Str.global_replace rightp_regex "" params in
          let params = Str.global_replace whitespace_regex "" params in
          let params = String.split_on_char ',' params in
          
          let rec setup_fn_params params =
            match params with
            | [] -> "env);\n}\n"
            | h :: t ->
              if str_contains h "vs2" then
                "vs2, " ^ setup_fn_params t
              else if str_contains h "vs1" then
                "vs1," ^ setup_fn_params t
              else if str_contains h "ms1" then
                "ms1," ^ setup_fn_params t
              else if str_contains h "ms2" then
                "ms2," ^ setup_fn_params t
              else if str_contains h "md" then
                "md," ^ setup_fn_params t
              else if str_contains h "ms3" then
                "vs3," ^ setup_fn_params t
              else if str_contains h "rs1" then
                "base," ^ setup_fn_params t
              else
                setup_fn_params t
          in
          "fn("  ^ setup_fn_params params

        else
          do_x_x_body_setup t
    in

    let do_x_x = do_x_x_params_setup inst_name funcl_string_list ^ do_x_x_body_setup funcl_string_list in


    let rec gen_def_params_setup inst_name funcl_string_list = 
      match funcl_string_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "execute" then
          let params = List.nth (Str.split mm_regex h) 1 in
          let params = List.hd (String.split_on_char '=' params) in
          let params = Str.global_replace leftp_regex "" params in
          let params = Str.global_replace rightp_regex "" params in
          let params = Str.global_replace whitespace_regex "" params in
          let params = String.split_on_char ',' params in
          
          let rec setup_fn_params inst_name params =
            match params with
            | [] -> "CPURISCVState *env)\\\n"
            | h :: t ->
              if str_contains h "vs2" then
                "void* vs2, " ^ setup_fn_params inst_name t
              else if str_contains h "vs1" then
                "void* vs1," ^ setup_fn_params inst_name t
              else if str_contains h "ms1" then
                "void* ms1," ^ setup_fn_params inst_name t
              else if str_contains h "ms2" then
                "void* ms2," ^ setup_fn_params inst_name t
              else if str_contains h "md" then
                "void * md," ^ setup_fn_params inst_name t
              else if str_contains h "ms3" then
                "void * vs3," ^ setup_fn_params inst_name t
              else if str_contains h "rs1" then
                "uint64_t base," ^ setup_fn_params inst_name t
              else
                setup_fn_params inst_name t
          in
          "#define GEN_" ^ String.uppercase(inst_name) ^ "(NAME) \\\n" ^
          "void HELPER(NAME)(" ^ setup_fn_params inst_name params ^ "{\\\n"

        else
          gen_def_params_setup inst_name t
    in

    let rec gen_def_body_setup inst_name funcl_string_list = 
      match funcl_string_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "execute" then
          let params = List.nth (Str.split mm_regex h) 1 in
          let params = List.hd (String.split_on_char '=' params) in
          let params = Str.global_replace leftp_regex "" params in
          let params = Str.global_replace rightp_regex "" params in
          let params = Str.global_replace whitespace_regex "" params in
          let params = String.split_on_char ',' params in
          
          let rec setup_fn_params inst_name params =
            match params with
            | [] -> "env, do_##NAME);\\\n"
            | h :: t ->
              if str_contains h "vs2" then
                "vs2, " ^ setup_fn_params inst_name t
              else if str_contains h "vs1" then
                "vs1," ^ setup_fn_params inst_name t
              else if str_contains h "ms1" then
                "ms1," ^ setup_fn_params inst_name t
              else if str_contains h "ms2" then
                "ms2," ^ setup_fn_params inst_name t
              else if str_contains h "md" then
                "md," ^ setup_fn_params inst_name t
              else if str_contains h "ms3" then
                "vs3," ^ setup_fn_params inst_name t
              else if str_contains h "rs1" then
                "base," ^ setup_fn_params inst_name t
              else
                setup_fn_params inst_name t
          in
          "do_" ^ inst_name ^ "_x(" ^ setup_fn_params inst_name params ^ "}\n"

        else
          gen_def_body_setup inst_name t
    in

    let gen_def = gen_def_params_setup inst_name funcl_string_list ^ gen_def_body_setup inst_name funcl_string_list in

    let gen = "GEN_" ^ String.uppercase_ascii(inst_name) ^ "(" ^ inst_name ^ "_w)\n\n" in

    fn_setup_def ^ do_x_byte ^ rvmmcall_def ^ do_x_x ^ gen_def ^ gen

let qemu_trans_string funcl_string_list = 
    let mm_regex = Str.regexp_string "_MM" in
    let leftp_regex = Str.regexp_string "(" in
    let rightp_regex = Str.regexp_string ")" in
    let whitespace_regex = Str.regexp_string " " in

    let rec gen_helper_def funcl_string_list = 
      match funcl_string_list with
      | [] -> "TCGv_env);"
      | h:: t->
        if str_contains h "execute" then
          let inst_name = String.lowercase_ascii(List.nth (String.split_on_char ' ' (List.hd (Str.split mm_regex h) ^ "_MM")) 1) in
          let params = List.nth (Str.split mm_regex h) 1 in
          let params = List.hd (String.split_on_char '=' params) in
          let params = Str.global_replace leftp_regex "" params in
          let params = Str.global_replace rightp_regex "" params in
          let params = Str.global_replace whitespace_regex "" params in
          let params = String.split_on_char ',' params in

          let rec setup_params params =
            match params with
            | [] -> ""
            | h :: t ->
              if str_contains h "vs2" then
                "TCGv_ptr, " ^ setup_params t
              else if str_contains h "vs1" then
                "TCGv_ptr, " ^ setup_params t
              else if str_contains h "ms1" then
                "TCGv_ptr, " ^ setup_params t
              else if str_contains h "ms2" then
                "TCGv_ptr, " ^ setup_params t
              else if str_contains h "md" then
                "TCGv_ptr, " ^ setup_params t
              else if str_contains h "ms3" then
                "TCGv_ptr, " ^ setup_params t
              else if str_contains h "rs1" then
                "TCGv, " ^ setup_params t
              else
                setup_params t
          in
          let gen_params = setup_params params in
        inst_name ^ "(" ^ gen_params ^ gen_helper_def t
        else
          gen_helper_def t

    in
    let gen_helper = "typedef void gen_helper_" ^ gen_helper_def funcl_string_list ^ "\n\n" in

    let rec execute_func_def funcl_string_list =
      match funcl_string_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "execute" then
          let inst_name = String.lowercase_ascii(List.nth (String.split_on_char ' ' (List.hd (Str.split mm_regex h) ^ "_MM")) 1) in
          let head = "static inline bool do_" in
          let params_start = "(DisasContext *ctx, arg_" in
          let pointer_a = " *a" in
          let pointer_fn = " *fn" in
          let gen_helper = ", gen_helper_" in
          let param_end = ") {\n" in
          head ^ inst_name ^ params_start ^ inst_name ^ pointer_a ^ gen_helper ^ inst_name ^ pointer_fn ^ param_end
        else
          execute_func_def t
    in
    let func_def = execute_func_def funcl_string_list in

    let rec execute_setup funcl_string_list = 
      match funcl_string_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "execute" then
          let inst_name = List.nth (String.split_on_char ' ' (List.hd (Str.split mm_regex h))) 1 in
          let params = List.nth (Str.split mm_regex h) 1 in
          let params = List.hd (String.split_on_char '=' params) in
          let params = Str.global_replace leftp_regex "" params in
          let params = Str.global_replace rightp_regex "" params in
          let params = Str.global_replace whitespace_regex "" params in
          let params = String.split_on_char ',' params in
          
          let rec setup_regs params inst_name =
            match params with
            | [] -> ""
            | h :: t ->
              if str_contains h "vs2" then
                "uint32_t vs2 = vreg_ofs(ctx, a->rs2);\n TCGv_ptr src2;\n" ^ setup_regs t inst_name
              else if str_contains h "vs1" then
                "uint32_t vs1 = vreg_ofs(ctx, a->rs1);\n TCGv_ptr src1;\n" ^ setup_regs t inst_name
              else if str_contains h "ms1" then
                "uint32_t ms1 = mregxy_ofs(ctx, a->rs1);\n TCGv_ptr src1;\n" ^ setup_regs t inst_name
              else if str_contains h "ms2" then
                "uint32_t ms2 = mregxy_ofs(ctx, a->rs2);\n TCGv_ptr src2;\n" ^ setup_regs t inst_name
              else if str_contains h "md" then
                if str_contains inst_name "XY" then
                  "uint32_t md = mregxy_ofs(ctx, a->rd);\n TCGv_ptr dest;\n" ^ setup_regs t inst_name
                else
                  "uint32_t md = mregz_ofs(ctx, a->rd);\n TCGv_ptr dest;\n" ^ setup_regs t inst_name
              else if str_contains h "ms3" then
                "uint32_t ms3 = mregz_ofs(ctx, a->rd);\n TCGv_ptr src3;\n" ^ setup_regs t inst_name
              else if str_contains h "rs1" then
                "uint32_t rs1 = a->rs1;\n TCGv base;\n" ^ setup_regs t inst_name
              else
                setup_regs t inst_name
          in
          setup_regs params inst_name

        else
          execute_setup t
    in
    let var_setup = execute_setup funcl_string_list in

    let rec ptr_setup_execute var_setup_list =
      match var_setup_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "md" then
          "dest = tcg_temp_new_ptr();\n" ^ "tcg_gen_addi_ptr(dest, cpu_env, md);\n" ^
           ptr_setup_execute t
        else if str_contains h "vs1" then
          "src1 = tcg_temp_new_ptr();\n" ^ "tcg_gen_addi_ptr(src1, cpu_env, vs1);\n" ^
           ptr_setup_execute t
        else if str_contains h "ms1" then
          "src1 = tcg_temp_new_ptr();\n" ^ "tcg_gen_addi_ptr(src1, cpu_env, ms1);\n" ^
           ptr_setup_execute t
        else if str_contains h "ms2" then
          "src2 = tcg_temp_new_ptr();\n" ^ "tcg_gen_addi_ptr(src2, cpu_env, ms2);\n" ^
           ptr_setup_execute t
        else if str_contains h "vs2" then
          "src2 = tcg_temp_new_ptr();\n" ^ "tcg_gen_addi_ptr(src2, cpu_env, vs2);\n" ^
          ptr_setup_execute t
        else if str_contains h "ms3" then
          "src3 = tcg_temp_new_ptr();\n" ^ "tcg_gen_addi_ptr(src3, cpu_env, ms3);\n" ^
           ptr_setup_execute t
        else if str_contains h "base" then
          "base = get_gpr(ctx, rs1, EXT_NONE);\n" ^
           ptr_setup_execute t
        else
          ptr_setup_execute t
    in
    let ptr_setup = ptr_setup_execute (String.split_on_char '\n' var_setup) in

    let rec free_ptr body_string_list = 
      match body_string_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "dest" then
          "tcg_temp_free_ptr(dest);\n" ^ free_ptr t
        else if str_contains h "src2" then
	  "tcg_temp_free_ptr(src2);\n" ^ free_ptr t
        else if str_contains h "src1" then
	  "tcg_temp_free_ptr(src1);\n" ^ free_ptr t
        else if str_contains h "src3" then
	  "tcg_temp_free_ptr(src3);\n" ^ free_ptr t
        else
          free_ptr t
    in 

    let rec fn_setup body_string_list = 
      match body_string_list with
      | [] -> "cpu_env);"
      | h :: t ->
        if str_contains h "dest" then
          "dest, " ^ fn_setup t
        else if str_contains h "src2" then
	  "src2, " ^ fn_setup t
        else if str_contains h "src1" then
	  "src1," ^ fn_setup t
        else if str_contains h "src3" then
	  "src3," ^ fn_setup t
        else if str_contains h "base" then
	  "base," ^ fn_setup t
        else
          fn_setup t
    in 
    let fn_call = "fn(" ^ fn_setup (String.split_on_char '\n' var_setup) ^ "\n" in
    let end_func = (free_ptr (String.split_on_char '\n' var_setup)) ^ "mark_vs_dirty(ctx);\n" ^
                   "gen_set_label(over);\n return true;\n}\n" in
    let label = "TCGLabel *over = gen_new_label();\n" in

    let do_x = func_def ^ var_setup ^ label ^  ptr_setup ^ fn_call ^ end_func in

    let rec do_x_gvec funcl_string_list =
      match funcl_string_list with
      | [] -> "\n"
      | h :: t ->
        if str_contains h "execute" then
          let inst_name = String.lowercase_ascii(List.nth (String.split_on_char ' ' (List.hd (Str.split mm_regex h) ^ "_MM")) 1) in
          let head = "static bool do_" in
          let params_start = "_gvec(DisasContext *ctx, arg_" in
          let pointer_a = " *a" in
          let pointer_fn = " *fn" in
          let gen_helper = ", gen_helper_" in
          let param_end = ") {\n" in
          let body = "return do_" in
          let body_params = "(ctx, a, fn);\n" in
          let body_end = "}\n" in
          head ^ inst_name ^ params_start ^ inst_name ^ pointer_a ^ gen_helper ^ inst_name ^ pointer_fn ^ param_end ^
          body ^ inst_name ^ body_params ^ body_end
        else
          do_x_gvec t
    in
    let do_x_gvec_def = do_x_gvec funcl_string_list in

    let rec do_gen_x funcl_string_list =
      match funcl_string_list with
      | [] -> "\n"
      | h :: t ->
        if str_contains h "execute" then
          let inst_name = String.lowercase_ascii(List.nth (String.split_on_char ' ' (List.hd (Str.split mm_regex h) ^ "_MM")) 1) in

          let upper_name = String.uppercase_ascii(inst_name) in
          let define_head = "#define GEN_" in
          let define_end = "_TRANS(NAME) \\\n" in
          let head = "static bool trans_##NAME(DisasContext *ctx, arg_" in
          let pointer_a = " *a" in
          let param_end = ") {\\\n" in
          let body_array = "static gen_helper_" in
          let body_array_end = " * const fns[1] = { gen_helper_##NAME##_w };\\\n" in
          let body = "return do_" in
          let body_params = "_gvec(ctx, a, fns[0]); \\\n" in
          let body_end = "}\n" in
          let gen = "GEN_" in
          let gen_mid = "_TRANS(" in
          let gen_end = ")\n\n" in
           
          define_head ^ upper_name ^ define_end ^
          head ^ inst_name ^ pointer_a ^ param_end ^
          body_array ^ inst_name ^ body_array_end ^
          body ^ inst_name ^ body_params ^ body_end ^
          gen ^ upper_name ^ gen_mid ^ inst_name ^ gen_end

        else
          do_gen_x t
    in
    let do_gen_x_def = do_gen_x funcl_string_list in

    gen_helper ^ do_x  ^ do_x_gvec_def ^ do_gen_x_def


let qemu_execute_string funcl_string = 
  if str_contains funcl_string "_MM" then
    let funcl_string_list = String.split_on_char '\n' funcl_string in
    qemu_execute_string_parse funcl_string_list
  else
    ""

let qemu_decode_string mapcl_string = 
  if str_contains mapcl_string "_MM" then
    let mm_regex = Str.regexp_string "_MM" in
    let bidirec_regex = Str.regexp_string "<->" in
    let alias_regex = Str.regexp_string "@" in
    let leftp_regex = Str.regexp_string "(" in
    let rightp_regex = Str.regexp_string ")" in
    let commaspace_regex = Str.regexp_string ", " in

    let inst_name = String.lowercase_ascii(List.hd (Str.split mm_regex mapcl_string) ^ "_MM") in

    let bit_defs = List.nth (Str.split bidirec_regex mapcl_string) 1 in
    let split_bit_defs = Str.split alias_regex bit_defs in

    let rec bit_matching split_bit_defs = 
      let whitespace_regex = Str.regexp_string " " in
      match split_bit_defs with
      | [] -> " "
      | h :: t ->
        if str_contains h "0b" then
          let bits = Str.string_after h 3 in
          " " ^ bits ^ bit_matching t

        else if str_contains h "bitvector" then
          " ....." ^ bit_matching t 
        else
          bit_matching t
    in

    let params = List.nth (Str.split mm_regex  (List.hd (Str.split bidirec_regex mapcl_string))) 1 in
    let inst_structure params =
      if str_contains params "vs2, vs1, md" then
        "@r\n"
      else if str_contains params "ms2, ms1, md" then
        "@r\n"
      else if str_contains params "rs1, md" then
        "@r2\n"
      else if str_contains params "rs1, ms3" then
        "@r2\n"
      else if str_contains params "vs2, md" then
        "@r2\n"
      else if str_contains params "vs1, md" then
        "@r2\n"
      else if str_contains params "ms2, md" then
        "@r2\n"
      else if str_contains params "ms1, md" then
        "@r2\n"
      else
        ""
    in

    let bit_body = bit_matching split_bit_defs in
    inst_name ^ "    " ^ bit_body ^ (inst_structure params)
  else
    ""
let qemu_thelper_string mapcl_string = 
  if str_contains mapcl_string "_MM" then
    let mm_regex = Str.regexp_string "_MM" in
    let bidirec_regex = Str.regexp_string "<->" in
    let alias_regex = Str.regexp_string "@" in
    let leftp_regex = Str.regexp_string "(" in
    let rightp_regex = Str.regexp_string ")" in
    let commaspace_regex = Str.regexp_string ", " in

    let inst_name = String.lowercase_ascii(List.hd (Str.split mm_regex mapcl_string) ^ "_mm_w") in

    let bit_defs = List.nth (Str.split bidirec_regex mapcl_string) 1 in
    let split_bit_defs = Str.split alias_regex bit_defs in

    let rec bit_matching split_bit_defs n = 
      let whitespace_regex = Str.regexp_string " " in
      match split_bit_defs with
      | [] -> ", env)", n+1
      | h :: t ->
        if str_contains h "bitvector" then
          if str_contains h "rs1" then
            let var, new_n =  bit_matching t (n + 1) in
            ", i64" ^ var, new_n
          else
            let var, new_n =  bit_matching t (n + 1) in
            ", ptr" ^ var, new_n 
        else
          bit_matching t n
    in

    let helper_body, n = bit_matching split_bit_defs 0 in
    "DEF_HELPER_" ^ string_of_int(n) ^ "(" ^ inst_name ^ ", void" ^ helper_body ^ "\n"
  else
    ""

let sail_to_qemu_execute clause outtype =
  let funcl_string = Pretty_print_sail.to_string(Pretty_print_sail.doc_funcl clause) in
  if (str_contains funcl_string "execute") && (str_contains funcl_string "_MM") then
    if outtype = "mm_helper" then
      qemu_execute_string funcl_string   
    else if outtype = "trans" then
      let funcl_string_list = String.split_on_char '\n' funcl_string in
      qemu_trans_string funcl_string_list 
    else
      ""
  else
    "" 

let sail_to_qemu_mapping id clause outtype = 
  let mapcl_string = Pretty_print_sail.to_string(Pretty_print_sail.doc_mapcl clause) in
  if string_of_id(id) = "encdec" then
    if outtype = "decode" then
      qemu_decode_string mapcl_string 
    else if outtype = "thelper" then
      qemu_thelper_string mapcl_string 
    else
      ""
  else
    "" 

let rec tablegen_funcl funcls outtype =
  match funcls with
  | [] -> ""
  | clause :: clauses -> sail_to_qemu_execute clause outtype ^ tablegen_funcl clauses outtype

let rec tablegen_mapcl id mapcls outtype  =
  match mapcls with
  | [] -> ""
  | clause :: clauses -> sail_to_qemu_mapping id clause outtype  ^ tablegen_mapcl id clauses outtype

let rec tablegen_fundef (FD_aux (FD_function (r, _, funcls), _)) outtype =
  match funcls with
  | [] -> failwith "No func clause"
  | _ -> tablegen_funcl funcls outtype

let rec tablegen_mapdef (MD_aux (MD_mapping (id, _, mapcls), _)) outtype =
  match mapcls with
  | [] -> failwith "No mapping clause"
  | _ -> tablegen_mapcl id mapcls outtype

let compile_ast env effect_info output_chan ast =

  let td_fun_def def outtype =
    match def with
    | DEF_fundef fundef -> tablegen_fundef fundef outtype
    | _ -> ""
  in

  let td_map_def def outtype =
    match def with
    | DEF_mapdef mapdef -> tablegen_mapdef mapdef outtype
    | _ -> ""
  in

  let rec process_defs outtype = function
    | [] -> ""
    | def :: defs ->
       if outtype = "mm_helper" || outtype = "trans" then
         let td  =  td_fun_def def outtype in
         td ^  process_defs outtype defs
       else if outtype = "decode" || outtype = "thelper" then
         let td  =  td_map_def def outtype in
         td ^  process_defs outtype defs
       else
         ""
  in

  (* FUNCTION BASED*)
  let ext = "MM" in
  let outtype = "trans" in
  let trans_header = "#include \"internals.h\"
static uint32_t mregxy_ofs(DisasContext *s, int reg)
{
    int32_t reg_length = 16;
    int32_t elem_size_bytes = 4;

    return offsetof(CPURISCVState, mregxy) + reg*reg_length*elem_size_bytes;
}\n
static uint32_t mregz_ofs(DisasContext *s, int reg)
{
    return offsetof(CPURISCVState, mregz) + reg;
}\n\n" in
  let qemu_trans = trans_header ^ process_defs outtype ast.defs in


  (* FUNCTION BASED*)
  let outtype = "mm_helper" in
  let mm_header ="#include \"qemu/osdep.h\"
#include \"qemu/host-utils.h\"
#include \"qemu/bitops.h\"
#include \"cpu.h\"
#include \"exec/memop.h\"
#include \"exec/exec-all.h\"
#include \"exec/helper-proto.h\"
#include \"fpu/softfloat.h\"
#include \"tcg/tcg-gvec-desc.h\"
#include \"internals.h\"
#include <math.h>
static inline target_ulong adjust_addrm(CPURISCVState *env, target_ulong addr)
{
    return (addr & env->cur_pmmask) | env->cur_pmbase;
}
#define RVMMCALL(macro, ...)  macro(__VA_ARGS__)\n" in

  let qemu_mmhelper = mm_header ^ process_defs outtype ast.defs in


  (* MAPPING BASED*)
  let outtype = "thelper" in
  let qemu_thelper = process_defs outtype ast.defs in

  let outtype = "decode" in
  let qemu_decode = process_defs outtype ast.defs in


  let fname0 = "generated_definitions/qemu/trans_rvmm.c.in" in
  let fname1 = "generated_definitions/qemu/matrix_helper.c" in
  let fname2 = "generated_definitions/qemu/helper.h" in
  let fname3 = "generated_definitions/qemu/insn32.decode" in


  let output_chan = open_out fname0 in
  Printf.fprintf output_chan "%s" qemu_trans;
  close_out output_chan;

  let output_chan = open_out fname1 in
  Printf.fprintf output_chan "%s" qemu_mmhelper;
  close_out output_chan;

  let output_chan = open_out fname2 in
  Printf.fprintf output_chan "%s" qemu_thelper;
  close_out output_chan;

  let output_chan = open_out fname3 in
  Printf.fprintf output_chan "%s" qemu_decode;
  close_out output_chan;

  Pretty_print_sail.pp_ast stdout ast;
  (*print_endline(qemu_trans);
  print_endline(qemu_mmhelper);
  print_endline(qemu_thelper);
  print_endline(qemu_decode)*)
