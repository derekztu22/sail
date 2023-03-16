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

    let rec execute_func_def funcl_string_list =
      match funcl_string_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "execute" then
          let inst_name = String.lowercase_ascii(List.hd (Str.split mm_regex h) ^ "_MM") in
          let head = "static bool trans_" in
          let params_start = "(DisasContext *ctx, arg_" in
          let params_end = " *a) {" in
          head ^ inst_name ^ params_start ^ inst_name ^ params_end ^ (execute_func_def t)
        else
          execute_func_def t
    in
    let func_def = execute_func_def funcl_string_list in

    let rec execute_setup funcl_string_list = 
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
          
          let rec setup_regs params =
            match params with
            | [] -> ""
            | h :: t ->
              if str_contains "vs2" then
                "uint32_t vs2 = a->rs2;\n TCGv_ptr src2;\n" ^ setup_regs t
              else if str_contains "vs1" then
                "uint32_t vs1 = a->rs1;\n TCGv_ptr src1;\n" ^ setup_regs t
              else if str_contains "md" then
                "uint32_t md = a->rd;\n TCGv_ptr dest;\n" ^ setup_regs t
              else if str_contains "ms3" then
                "uint32_t ms3 = a->rd;\n TCGv_ptr src3;\n" ^ setup_regs t
              else if str_contains "rs1" then
                "TCGv base;\n" ^ setup_regs t
              else
                setup_regs t
          in
          setup_regs params

        else
          execute_setup t
    in
    let var_setup = execute_setup funcl_string_list in

    let rec ptr_setup_execute var_setup_list in
      match var_setup_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "md" then
          "dest = tcg_temp_new_ptr();\n" ^ "tcg_gen_addi_ptr(dest, cpu_env, mreg_ofs(ctx, md));\n" ^
          ^ ptr_setup_execute t
        else if str_contains h "vs1" then
          "src1 = tcg_temp_new_ptr();\n" ^ "tcg_gen_addi_ptr(src1, cpu_env, vreg_ofs(ctx, vs1));\n" ^
          ^ ptr_setup_execute t
        else if str_contains h "vs2" then
          "src2 = tcg_temp_new_ptr();\n" ^ "tcg_gen_addi_ptr(src2, cpu_env, vreg_ofs(ctx, vs2));\n" ^
          ^ ptr_setup_execute t
        else if str_contains h "ms3" then
          "src3 = tcg_temp_new_ptr();\n" ^ "tcg_gen_addi_ptr(src3, cpu_env, mreg_ofs(ctx, ms3));\n" ^
          ^ ptr_setup_execute t
        else if str_contains h "base" then
          "base = get_gpr(ctx, rs1, EXT_NONE);\n" ^
          ^ ptr_setup_execute t
        else
          ptr_setup_execute t
    in
    let ptr_setup = ptr_setup_execute (String.split_on_char '\n' var_setup) in

    let rec body_func_execute funcl_string_list in
      match funcl_string_list with
      | [] -> ""
      | h :: t ->
        if str_contains h "foreach" then
          let foreach_regex = Str.regexp_string "foreach" in
          let from_regex = Str.regexp_string "from" in
          let to_regex = Str.regexp_string "to" in
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
          let for_loop = Str.replace_first to_regex ";" for_loop in
          let for_loop = Str.replace_first by_regex ";" for_loop in
          let for_loop = Str.replace_first leftp_regex "(uint32_t " for_loop in
          let for_loop = Str.replace_first one_in_inc_regex ("++" ^ idx) for_loop in
          let for_loop = Str.replace_first range_regex (idx ^ "< 32")  for_loop in
          for_loop ^ "\n" ^ body_func_execute t

        else if str_contains h "let" 
          let let_regex = Str.regexp_string "let" in
          let vector_regex = Str.regexp_string "plain_vector_access" in
          let comma_regex = Str.regexp_string "," in
          let rightp_regex = Str.regexp_string ")" in
          let leftp_regex = Str.regexp_string "(" in
          let semicolon_regex = Str.regexp_string ";" in
          let comma_whitespace_regex = Str.regexp_string ", " in
          let num_elem_regex = Str.regexp_string "num_elem" in

          let h = Str.global_replace num_elem_regex "32" h in 

          let get_idx idx = 
            (* Calcualted idx *)
            if str_contains "_atom" h then
              let atom_regex = Str.regexp_string "_atom" in
              let assignment = List.nth (Str.split_on_char '=' h) 1 in

              let rec idx_calc idx_str = 
                let lhs = List.hd (Str.bounded_split atom_regex h 1) in 
                let rhs = List.nth (Str.bounded_split atom_regex h 1) 1 in
                let rhs = Str.global_replace leftp_regex "" rhs in
                let rhs = Str.global_replace rightp_regex "" rhs in
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
                  right_var ^ op ^ idx_calc rhs
                else
                  let left_var = List.hd (String.split_on_char ',' rhs) in 
                  right_var ^ op ^ left_var
              in

              idx_calc assignment 
            (* Non-calculated idx *)
            else
              let idx = List.nth (Str.split comma_regex idx) 1 in
              let idx = Str.global_replace rightp_regex "" idx in
              let idx = Str.global_replace semicolon_regex "" idx in
              idx
          in

          (* Get base address *)
          if str_contains h "data_get_addr" then
            let to_bits_regex = Str.regexp_string "to_bits(" in
            let addr_idx = List.nth (Str.split to_bits_regex h) 1 in
            let addr_idx = List.hd (Str.split_on_char ')' addr_idx) in
            let addr_idx = List.nth (Str.split_on_char ',' addr_idx) 1 in
            let pc = "uintptr ra = GET_PC();\n"
            let addr = "uint64_t addr = base + " ^ addr_idx ^ ";\n" in
 
            if str_contains h "Read" then
              pc ^ addr ^ "int32_t * cur = ((int32_t*) dest  + i);\n" ^ body_func_execute t 
            else if str_contains h "Write" then
              pc ^ addr ^ "int32_t data = *((int32_t*) src3  + i);\n" ^ body_func_execute t 
            else
              body_func_execute t

          (* Load *)
          else if str_contains h "mem_read" then
            "*cur = cpu_ldl_data_ra(cpu_env, adjust_addr(cpu_env, addr), ra);\n"

          (* Store *)
          else if str_contains h "mem_write" then
            "*cur = cpu_stl_data_ra(cpu_env, adjust_addr(cpu_env, addr), ra);\n"

          else if str_contains h "plain_vector_access" then
            let let_str = List.hd (String.split_on_char '=' (Str.replace_first let_regex "int32_t" h)) in
            let idx = List.nth (Str.split vector_regex h) 1 in
            let idx = get_idx idx in
      
            if str_contains h "vs1" then
              let_str ^ "= *((int32_t*) src1 +" ^ idx ^ ";\n" ^ body_func_execute t
            else if str_contains h "vs2" then
              let_str ^ "= *((int32_t*) src2 +" ^ idx ^ ";\n" ^ body_func_execute t
            else if str_contains h "md" then
              let_str ^ "= *((int32_t*) dest +" ^ idx ^ ";\n" ^  body_func_execute t

          else if str_contains h "result[" then
            let idx = List.hd (String.split_on_char '=' h ) in
            let idx = get_idx id in
            let var = List.nth (String.split_on_char '=' h) 1 in
            "*((int32_t*) dest + " ^ idx ^ " = " ^ var ";\n" ^ body_func_execute t

          else if str_contains h "mult_atom" then
            let mult_atom_regex = Str.regexp_string "mult_atom" in
            let let_str = List.hd (String.split_on_char '=' (Str.replace_first let_regex "int32_t" h)) in
            let vars = List.nth (Str.split mult_atom_regex h) 1 in
            let vars = Str.global_replace rightp_regex "" vars in 
            let vars = Str.global_replace leftp_regex "" vars in 
            let vars = Str.global_replace semicolon_regex "" vars in 
            let vars = Str.split comma_whitespace_regex vars in
            let_str ^ List.hd vars ^ "*" ^ List.nth vars 1 ^ ";\n" ^ body_func_execute t 
            
          else if  str_contains h "add_bits_int" then
            let add_atom_regex = Str.regexp_string "add_bits_int" in
            let let_str = List.hd (String.split_on_char '=' (Str.replace_first let_regex "int32_t" h)) in
            let vars = List.nth (Str.split add_atom_regex h) 1 in
            let vars = Str.global_replace rightp_regex "" vars in 
            let vars = Str.global_replace leftp_regex "" vars in 
            let vars = Str.global_replace semicolon_regex "" vars in 
            let vars = Str.split comma_whitespace_regex vars in
            let_str ^ List.hd vars ^ "+" ^ List.nth vars 1 ^ ";\n" ^ body_func_execute t 

          else if  str_contains h "sub_vec_int" then
            let sub_atom_regex = Str.regexp_string "sub_vec_int" in
            let let_str = List.hd (String.split_on_char '=' (Str.replace_first let_regex "int32_t" h)) in
            let vars = List.nth (Str.split sub_atom_regex h) 1 in
            let vars = Str.global_replace rightp_regex "" vars in 
            let vars = Str.global_replace leftp_regex "" vars in 
            let vars = Str.global_replace semicolon_regex "" vars in 
            let vars = Str.split comma_whitespace_regex vars in
	    let_str ^ List.hd vars ^ "-" ^ List.nth vars 1 ^ ";\n" ^ body_func_execute t 


          else
            ""

        else if (Str.global_replace whitespace_regex "" h) = "}" then
          "}" ^ body_func_execute t
        else if (Str.global_replace whitespace_regex "" h) = "};" then
          "}" ^ body_func_execute t
        else if str_contains h "RETIRE_SUCCESS" then
          ""
        
        else
          body_func_execute t

    in
    let body_func = body_func_execute funcl_string_list in

    let rec free_ptr body_string_list = 
      match body_string_list
      | [] -> ""
      | h :: t ->
        if str_contains h "dest" then
          "tcg_temp_free_ptr(dest);\n" ^ free_ptr t
        else if str_contains h "src2" then
	  "tcg_temp_free_ptr(src2);\n" ^ free_ptr t
        else if str_contains h "src1" then
	  "tcg_temp_free_ptr(src1);\n" ^ free_ptr t
        else
          free_ptr t
    in 
   
    let end_func = (free_ptr (String.split_on_char '\n' body_func)) ^ "mark_vs_dirty(ctx);\n" ^
                   "gen_set_label(over);\n return true;\n}\n"
    let label = "TCGLabel *over = gen_new_label();"

    func_def ^ var_setup ^ label ^ ptr_setup ^ body_func ^ end_func


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
          let bits = Str.string_after h 2 in
          " " ^ bits ^ bit_matching t

        else if str_contains h "bitvector" then
          " ....." ^ bit_matching t 
        else
          bit_matching t
    in

    let params = List.nth (Str.split mm_regex  (List.hd (Str.split bidirec_regex mapcl_string))) 1 in
    let inst_structure params =
      if str_contains params "vs2, vs1, md" then
        "@r"
      else if str_contains params "rs1, md" then
        "@r2"
      else if str_contains params "rs1, ms3" then
        "@r2"
      else if str_contains params "vs2, md" then
        "@r2"
      else
        ""
    in

    let bit_body = bit_matching split_bit_defs in
    inst_name ^ "    " ^ bit_body ^ (inst_structure params)

  else
    ""

let sail_to_qemu_execute clause = 
  let funcl_string = Pretty_print_sail.to_string(Pretty_print_sail.doc_funcl clause) in
  if str_contains funcl_string "execute" then
    qemu_execute_string funcl_string   
  else
    "" 

let sail_to_qemu_decode id clause = 
  let mapcl_string = Pretty_print_sail.to_string(Pretty_print_sail.doc_mapcl clause) in
  if string_of_id(id) = "encdec" then
    qemu_decode_string mapcl_string   
  else
    "" 

let rec tablegen_funcl funcls =
  match funcls with
  | [] -> ""
  | clause :: clauses -> sail_to_qemu_execute clause ^ tablegen_funcl clauses

let rec tablegen_mapcl id mapcls  =
  match mapcls with
  | [] -> ""
  | clause :: clauses -> sail_to_qemu_decode id clause  ^ tablegen_mapcl id clauses

let rec tablegen_fundef (FD_aux (FD_function (r, _, funcls), _)) =
  match funcls with
  | [] -> failwith "No func clause"
  | _ -> tablegen_funcl funcls

let rec tablegen_mapdef (MD_aux (MD_mapping (id, _, mapcls), _)) =
  match mapcls with
  | [] -> failwith "No mapping clause"
  | _ -> tablegen_mapcl id mapcls

let compile_ast env effect_info output_chan ast =

  let td_fun_def def =
    match def with
    | DEF_fundef fundef -> tablegen_fundef fundef
    | _ -> ""
  in

  let td_map_def def =
    match def with
    | DEF_mapdef mapdef -> tablegen_mapdef mapdef
    | _ -> ""
  in

  let rec process_defs outtype = function
    | [] -> ""
    | def :: defs ->
       if outtype = "execute" then
         let td  =  td_fun_def def in
         td ^  process_defs outtype defs
       else if outtype = "decode" then
         let td  =  td_map_def def in
         td ^  process_defs outtype defs
       else
         ""
  in

  let ext = "MM" in
  let outtype = "execute" in
  let qemu_execute = process_defs outtype ast.defs in

  let outtype = "decode" in
  let qemu_decode = process_defs outtype ast.defs in

  print_endline(qemu_execute)
  print_endline(qemu_decode)
