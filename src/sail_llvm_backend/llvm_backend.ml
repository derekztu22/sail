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


let sizeof_reg reg =
  let whitespace_regex = Str.regexp_string " " in
  let reg =  Str.global_replace whitespace_regex "" reg in
  if reg = "vs2" then
    5
  else if reg = "vs1" then
    5
  else if reg = "ms1" then
    5
  else if reg = "ms2" then
    5
  else if reg = "rs1" then
    5
  else if reg = "ms3" then
    5
  else if reg = "md" then
    5
  else
    0

let str_contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false

let formats_string mapcl_string =
  if str_contains mapcl_string "_MM" then
    let mm_regex = Str.regexp_string "_MM" in
    let bidirec_regex = Str.regexp_string "<->" in
    let alias_regex = Str.regexp_string "@" in
    let leftp_regex = Str.regexp_string "(" in
    let rightp_regex = Str.regexp_string ")" in
    let commaspace_regex = Str.regexp_string ", " in

    let head = "class RVInst" in
    let tdparams = "<dag outs, dag ins, string opcodestr, string argstr>" in
    let class_def = "\n: RVInst<outs, ins, opcodestr, argstr, [], InstFormatR> {\n" in
    let end_parenth = "let Uses = [ML];\n}\n\n" in
    let mapcl_string = Str.global_replace leftp_regex "" mapcl_string in
    let mapcl_string = Str.global_replace rightp_regex "" mapcl_string in
    let inst_name = List.hd (Str.split mm_regex mapcl_string) ^ "_MM"in
    let params = List.nth (Str.split mm_regex  (List.hd (Str.split bidirec_regex mapcl_string))) 1 in
    let params = Str.split commaspace_regex params in

    let rec param_matching params = 
      match params with
       | [] -> ""
       | h :: t -> "bits<" ^ string_of_int(sizeof_reg h) ^ ">" ^ h ^ ";\n" ^ param_matching t
    in
    let params = param_matching params in

    let bit_defs = List.nth (Str.split bidirec_regex mapcl_string) 1 in
    let split_bit_defs = Str.split alias_regex bit_defs in
    let rec bit_matching split_bit_defs bits_left = 
      let whitespace_regex = Str.regexp_string " " in
      match split_bit_defs with
        | [] -> ""
        | h :: t ->
          let h =  Str.global_replace whitespace_regex "" h in
          if bits_left = 6 then
            "let Opcode = " ^ h ^ ";\n"

          else if str_contains h "vs2" then
            "let Inst{" ^ string_of_int(bits_left) ^ "-" ^ string_of_int(bits_left - (sizeof_reg "vs2") + 1) ^
            "} = vs2;\n" ^ bit_matching t (bits_left - (sizeof_reg "vs2"))

          else if str_contains h "rs1" then
            "let Inst{" ^ string_of_int(bits_left) ^ "-" ^ string_of_int(bits_left - (sizeof_reg "rs1") + 1) ^
            "} = rs1;\n" ^ bit_matching t (bits_left - (sizeof_reg "rs1"))

          else if str_contains h "vs1" then
            "let Inst{" ^ string_of_int(bits_left) ^ "-" ^ string_of_int(bits_left - (sizeof_reg "vs1") + 1) ^
            "} = vs1;\n" ^ bit_matching t (bits_left - (sizeof_reg "vs1"))

          else if str_contains h "ms1" then
            "let Inst{" ^ string_of_int(bits_left) ^ "-" ^ string_of_int(bits_left - (sizeof_reg "ms1") + 1) ^
            "} = ms1;\n" ^ bit_matching t (bits_left - (sizeof_reg "ms1"))

          else if str_contains h "ms2" then
            "let Inst{" ^ string_of_int(bits_left) ^ "-" ^ string_of_int(bits_left - (sizeof_reg "ms2") + 1) ^
            "} = ms2;\n" ^ bit_matching t (bits_left - (sizeof_reg "ms2"))

          else if str_contains h "ms3" then
            "let Inst{" ^ string_of_int(bits_left) ^ "-" ^ string_of_int(bits_left - (sizeof_reg "ms3") + 1) ^
            "} = ms3;\n" ^ bit_matching t (bits_left - (sizeof_reg "ms3"))

          else if str_contains h "md" then
            "let Inst{" ^ string_of_int(bits_left) ^ "-" ^ string_of_int(bits_left - (sizeof_reg "md") + 1) ^
            "} = md;\n" ^ bit_matching t (bits_left - (sizeof_reg "md"))

          (* it's a bit def *)
          else
            let bits = Str.string_after h 2 in
            let str_length = String.length bits in
            if str_length = 1 then
              "let Inst{" ^ string_of_int(bits_left) ^ "} = " ^ h ^ ";\n" ^ bit_matching t (bits_left -1)
            else
              "let Inst{" ^ string_of_int(bits_left) ^ "-" ^ string_of_int(bits_left - str_length + 1) ^
              "} = " ^ h ^ ";\n" ^ bit_matching t (bits_left - str_length)
    in
    let bit_body = bit_matching split_bit_defs 31 in

    head ^ inst_name ^ tdparams ^ class_def ^ params ^ bit_body ^ end_parenth

  else 
    ""
let is_read_type mapcl_string =
  false

let scheduler_string mapcl_string = 
  if str_contains mapcl_string "_MM" then
    let mm_regex = Str.regexp_string "_MM" in
    let inst_name = List.hd (Str.split mm_regex mapcl_string) ^"_MM" in
    "def Read" ^ inst_name ^ " : SchedRead;\n" ^
    "def Write" ^ inst_name ^ " : SchedWrite;\n"
  
  else
    ""
let u_scheduler_string mapcl_string = 
  if str_contains mapcl_string "_MM" then
    let mm_regex = Str.regexp_string "_MM" in
    let inst_name = List.hd (Str.split mm_regex mapcl_string) ^ "_MM" in
    "def : ReadAdvance<Read" ^ inst_name ^ ", 0>;\n" ^
    "def : WriteRes<Write" ^ inst_name ^ ", []>;\n"
  else
    ""

let instclass_string mapcl_string = 
  if str_contains mapcl_string "_MM" then
    let mm_regex = Str.regexp_string "_MM" in
    let bidirec_regex = Str.regexp_string "<->" in
    let carat_regex = Str.regexp_string "^" in
    let leftp_regex = Str.regexp_string "(" in
    let rightp_regex = Str.regexp_string ")" in
    let commaspace_regex = Str.regexp_string ", " in

    let mapcl_string = Str.global_replace leftp_regex "" mapcl_string in
    let mapcl_string = Str.global_replace rightp_regex "" mapcl_string in
    let inst_name = List.hd (Str.split mm_regex mapcl_string) ^ "_MM"in
    let params = List.nth (Str.split mm_regex  (List.hd (Str.split bidirec_regex mapcl_string))) 1 in
    let params = Str.split commaspace_regex params in
    let bidirect_right = (Str.split carat_regex (List.nth (Str.split bidirec_regex mapcl_string) 1)) in

    let rec find_outreg params =
      match params with
      | [] -> "" 
      | h :: t -> 
        if str_contains h "reg_name" then
          let reg_regex = Str.regexp_string "reg_name" in
          let reg = List.nth (Str.split reg_regex h) 1 in
          if str_contains h "mreg" then 
            if str_contains h "ms3" then
              ""
            else
              "MR:$" ^ reg
          else if str_contains h "vreg" then 
            "VR:$" ^ reg
          else
            "GPR:$" ^ reg
        else
          find_outreg t
    in
    let outreg = "(outs " ^ find_outreg bidirect_right  ^ " ),\n" in
     
    let rec find_inregs params n =
      let delimeter n =
        if n = 0 then "" else ","
      in
      match params with
      | [] -> ""
      | h :: t ->
        if str_contains h "vs2" then
          delimeter n ^ "VR:$vs2" ^ find_inregs t (n + 1)
        else if str_contains h "vs1" then
          delimeter n ^ "VR:$vs1" ^ find_inregs t (n + 1)
        else if str_contains h "ms3" then
          delimeter n ^ "MR:$ms3" ^ find_inregs t (n + 1)
        else if str_contains h "ms2" then
          delimeter n ^ "MR:$ms2" ^ find_inregs t (n + 1)
        else if str_contains h "ms1" then
          delimeter n ^ "MR:$ms1" ^ find_inregs t (n + 1)
        else if str_contains h "rs1" then
          delimeter n ^ "GPR:$rs1" ^ find_inregs t (n + 1)
        else
          find_inregs t n
    in
    let inreg = "(ins " ^ find_inregs params 0 ^ ")," in

    let rec find_order params n =
      let delimeter n =
        if n = 0 then "" else ","
      in
      match params with
      | [] -> ""
      | h :: t ->
        if str_contains h "md" then
          delimeter n ^ "$md" ^ find_order t (n+1)
        else if str_contains h "ms3" then
          delimeter n ^ "$ms3" ^ find_order t (n+1)
        else if str_contains h "vs2" then
          delimeter n ^ "$vs2" ^ find_order t (n+1)
        else if str_contains h "vs1" then
          delimeter n ^ "$vs1" ^ find_order t (n+1)
        else if str_contains h "ms1" then
          delimeter n ^ "$ms1" ^ find_order t (n+1)
        else if str_contains h "ms2" then
          delimeter n ^ "$ms2" ^ find_order t (n+1)
        else if str_contains h "rs1" then
          delimeter n ^ "(${rs1})" ^ find_order t (n+1)
        else
          find_order t n
    in
    let order = find_order bidirect_right 0 in
   
    let header = "let hasSideEffects = 0, mayLoad = 0, mayStore = 0 in {\n" in 
    header ^ "class M" ^ inst_name ^ "<string opcodestr>\n : RVInst" ^ inst_name ^ "<" ^ outreg ^ inreg ^
    "opcodestr,\n" ^ "\"" ^ order ^ "\">;\n}\n\n"
  else
    ""

let instdef_string mapcl_string = 
  if str_contains mapcl_string "_MM" then
    let mm_regex = Str.regexp_string "_MM" in
    let bidirec_regex = Str.regexp_string "<->" in
    let carat_regex = Str.regexp_string "^" in
    let leftp_regex = Str.regexp_string "(" in
    let rightp_regex = Str.regexp_string ")" in
    let commaspace_regex = Str.regexp_string ", " in
    let whitespace_regex = Str.regexp_string " " in
    let inst_name = List.hd (Str.split mm_regex mapcl_string) ^ "_MM"in

    let assembly_name = List.hd (Str.split carat_regex (List.nth (Str.split bidirec_regex mapcl_string) 1)) in
    let assembly_name = Str.global_replace whitespace_regex "" assembly_name in 

    let rec find_sched_order assembly_string inst_name n =
      let delimeter n =
        if n = 0 then "" else ","
      in
      match assembly_string with 
      | [] -> ""
      | h :: t ->
        if str_contains h "reg_name" then
          let reg_name = Str.global_replace rightp_regex "" (List.nth (Str.split leftp_regex h) 1) in
          if str_contains reg_name "md" then
            delimeter n ^ "Write" ^ inst_name  ^ (find_sched_order t inst_name (n+1))
          else if str_contains reg_name "ms3" then
            delimeter n ^ "Write" ^ inst_name  ^ (find_sched_order t inst_name (n+1))
          else if str_contains reg_name "vs2" then
            delimeter n ^ "Read" ^ inst_name  ^ (find_sched_order t inst_name (n+1))
          else if str_contains reg_name "vs1" then
            delimeter n ^ "Read" ^ inst_name  ^ (find_sched_order t inst_name (n+1))
          else if str_contains reg_name "ms1" then
            delimeter n ^ "Read" ^ inst_name  ^ (find_sched_order t inst_name (n+1))
          else if str_contains reg_name "ms2" then
            delimeter n ^ "Read" ^ inst_name  ^ (find_sched_order t inst_name (n+1))
          else if str_contains reg_name "rs1" then
            delimeter n ^ "Read" ^ inst_name  ^ (find_sched_order t inst_name (n+1))
          else
            find_sched_order t inst_name n
        else
          find_sched_order t inst_name n

    in
   
    let bidirect_right = (Str.split carat_regex (List.nth (Str.split bidirec_regex mapcl_string) 1)) in
    let schedule_order = find_sched_order bidirect_right inst_name 0 in

    "def " ^ inst_name ^ " : M" ^ inst_name ^ "<" ^ assembly_name ^ ">,\n" ^
    "Sched<[" ^ schedule_order ^ "]>;\n\n"

  else
    ""

let sail_to_td id clause outtype =
  let mapcl_string = Pretty_print_sail.to_string(Pretty_print_sail.doc_mapcl clause) in
  if string_of_id(id) = "encdec" then
    if outtype = "formats" then
      formats_string mapcl_string
    else if outtype = "scheduler" then
      scheduler_string mapcl_string
    else if outtype = "uscheduler" then
      u_scheduler_string mapcl_string
    else
      ""
  else if string_of_id(id) = "assembly" then
    if outtype = "instclass" then
      instclass_string mapcl_string
    else if outtype = "instdef" then
      instdef_string mapcl_string
    else
      ""
  else
    ""

let rec tablegen_mapcl id mapcls outtype  =
  match mapcls with
  | [] -> 
      ""
  | clause :: clauses -> sail_to_td id clause outtype ^ tablegen_mapcl id clauses outtype

let rec tablegen_mapdef (MD_aux (MD_mapping (id, _, mapcls), _)) outtype =
  match mapcls with
  | [] -> failwith "No mapping clause"
  | _ -> tablegen_mapcl id mapcls outtype

let compile_ast env effect_info output_chan ast =
  let td_def def outtype =
    match def with
    | DEF_mapdef mapdef -> tablegen_mapdef mapdef outtype
    | _ -> ""
  in

  let rec process_defs outtype = function
    | [] -> ""
    | def :: defs ->
       let td  =  td_def def outtype in
       td ^  process_defs outtype defs
  in

  let ext = "MM" in

  let outtype = "formats" in
  let formats_tablegen = process_defs outtype ast.defs in

  let outtype = "scheduler" in
  let scheduler_tablegen = process_defs outtype ast.defs in

  let outtype = "uscheduler" in
  let uscheduler_tablegen = process_defs outtype ast.defs in
  
  let scheduler = scheduler_tablegen ^ "\nmulticlass UnsupportedSched" ^ ext ^ " {\n" ^ 
                  "let Unsupported = true in {\n\n"  ^ uscheduler_tablegen ^ "}\n}" in

  let outtype = "instclass" in
  let instclass = process_defs outtype ast.defs  in

  let outtype = "instdef" in
  let instdef = process_defs outtype ast.defs  in
  
  let inst = "include \"RISCVInstrFormats" ^ ext ^ ".td\"" ^
             instclass ^ "\n///////Instructions//////////\n" ^ instdef in

  let fname0 = "generated_definitions/llvm/RISCVInstrFormats" ^ ext ^ ".td" in
  let fname1 = "generated_definitions/llvm/RISCVInstrInfo" ^ ext ^ ".td" in
  let fname2 = "generated_definitions/llvm/RISCVSchedule" ^ ext ^ ".td" in

  let output_chan = open_out fname0 in
  Printf.fprintf output_chan "%s" formats_tablegen;
  close_out output_chan;

  let output_chan = open_out fname1 in
  Printf.fprintf output_chan "%s" inst;
  close_out output_chan;

  let output_chan = open_out fname2 in
  Printf.fprintf output_chan "%s" scheduler;
  close_out output_chan;

  print_endline(inst)
