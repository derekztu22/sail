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

let rec get_mpat_annot (MP_aux(mp_aux, _) as mpat) =
  let underscore_regex = Str.regexp_string "_" in
  match mp_aux with
  | MP_app (id, pats) -> 
    if str_contains (string_of_id id) "_" then
      List.nth (Str.split underscore_regex (string_of_id id)) 1
    else
      ""
  | _ -> "" 

let get_mpexp_annot mpexp = 
  match mpexp with
  | MPat_pat mpat -> get_mpat_annot mpat
  | _ -> ""

let rec get_mpat_params (MP_aux(mp_aux, _) as mpat) =
  let commaspace_regex = Str.regexp_string ", " in
  match mp_aux with
  | MP_app (id, pats) ->
      Str.split commaspace_regex (Pretty_print_sail.to_string(separate_map (comma ^^ space) Pretty_print_sail.doc_mpat pats))
  | _ -> [""] 

let get_instr_params mpexp =
  match mpexp with
  | MPat_pat mpat -> get_mpat_params mpat
  | _ -> [""]

let rec get_mpat_name (MP_aux(mp_aux, _) as mpat) =
  let commaspace_regex = Str.regexp_string ", " in
  match mp_aux with
  | MP_app (id, pats) -> string_of_id id
  | _ -> ""

let get_instr_name mpexp =
  match mpexp with
  | MPat_pat mpat -> get_mpat_name mpat
  | _ -> ""


let get_bit (L_aux(l, _)) = 
  utf8string (match l with
  | L_bin n -> n
  | _ -> "")


let get_register_string mpat_string =
  let colon_regex = Str.regexp_string " : " in
  let lparen_regex = Str.regexp_string "(" in
  let reg_name = List.hd (Str.split colon_regex mpat_string) in
  Str.global_replace lparen_regex "" reg_name


let rec get_mpat_bit_format (MP_aux (mp_aux, _) as mpat)  bit_num = 
  match mp_aux with
  | MP_lit lit ->
            let bits = Pretty_print_sail.to_string(get_bit lit) in
            let str_length = String.length bits in

             if str_length = 1 then
              "let Inst{" ^ string_of_int(bit_num) ^ "} = 0b" ^ bits ^ ";\n", (bit_num - 1)
            else
              "let Inst{" ^ string_of_int(bit_num) ^ "-" ^ string_of_int(bit_num - str_length + 1) ^
              "} = 0b" ^ bits ^ ";\n", (bit_num - str_length)

  | MP_vector_concat pats -> 
    let rec create_bit_body patts bit_num = 
      match patts with 
      | [] -> "", 0
      | h :: t -> 
        if bit_num = 6 then
          "let Opcode = " ^ string_of_mpat h ^ ";\n", 0
        else
          let bit_def0, bits_left = get_mpat_bit_format h bit_num in
          let bit_def1, bits_left = create_bit_body t bits_left in
          bit_def0 ^ bit_def1, bits_left
    in
    create_bit_body pats bit_num
   | _ -> 
     let reg_name = get_register_string (string_of_mpat mpat) in
     "let Inst{" ^ string_of_int(bit_num) ^ "-" ^ string_of_int(bit_num - 5 + 1) ^
     "} = " ^ reg_name ^ ";\n", bit_num - 5

let create_bit_format mpexp bit_num = 
  match mpexp with
  | MPat_pat mpat -> get_mpat_bit_format mpat bit_num
  | _ -> "", 0

let matrix_format_string mpexp1 mpexp2 =
  let head = "class RVInst" in
  let tdparams = "<dag outs, dag ins, string opcodestr, string argstr>" in
  let class_def = "\n: RVInst<outs, ins, opcodestr, argstr, [], InstFormatR> {\n" in
  let end_parenth = "let Uses = [ML];\n}\n\n" in
  let params = get_instr_params mpexp1 in
  let inst_name = get_instr_name mpexp1 in
  let rec param_matching params = 
    match params with
     | [] -> ""
     | h :: t -> "bits<" ^ string_of_int(sizeof_reg h) ^ ">" ^ h ^ ";\n" ^ param_matching t
  in
  let params = param_matching params in
  let bit_body, _ = create_bit_format mpexp2 31 in 
  head ^ inst_name ^ tdparams ^ class_def ^ params ^ bit_body ^ end_parenth
  

let formats_string (MPat_aux(mpexp1, _)) (MPat_aux(mpexp2, _)) = 
  let annot = get_mpexp_annot mpexp1 in
  match annot with
    | "MM" -> matrix_format_string mpexp1 mpexp2
    | _ -> ""

let matrix_scheduler_string mpexp1 = 
  let inst_name = get_instr_name mpexp1 in
  "def Read" ^ inst_name ^ " : SchedRead;\n" ^
  "def Write" ^ inst_name ^ " : SchedWrite;\n"
  
let scheduler_string  (MPat_aux(mpexp1, _)) = 
  let annot = get_mpexp_annot mpexp1 in
  match annot with
    | "MM" -> matrix_scheduler_string mpexp1
    | _ -> ""

let matrix_uscheduler_string mpexp1 = 
  let inst_name = get_instr_name mpexp1 in
  "def : ReadAdvance<Read" ^ inst_name ^ ", 0>;\n" ^
  "def : WriteRes<Write" ^ inst_name ^ ", []>;\n"

let uscheduler_string  (MPat_aux(mpexp1, _)) = 
  let annot = get_mpexp_annot mpexp1 in
  match annot with
    | "MM" -> matrix_uscheduler_string mpexp1
    | _ -> ""

let get_func_param func = 
  let lparen_regex = Str.regexp_string "(" in
  let rparen_regex = Str.regexp_string ")" in
  List.hd (Str.split rparen_regex (List.nth (Str.split lparen_regex func) 1))


let get_mpat_outreg (MP_aux (mp_aux, _) as mpat) =
  match mp_aux with
  | MP_string_append pats ->
    let rec get_outreg_pat patts =
      match patts with 
      | [] -> ""
      | h :: t -> 
        if str_contains (string_of_mpat h) "reg_name" then
          let reg_name = get_func_param (string_of_mpat h)  in
          (match reg_name with
          | "md" -> "MR:$" ^  reg_name
          | _ -> get_outreg_pat t)
        else
          get_outreg_pat t
    in
    get_outreg_pat pats
  | _ -> ""

let get_instr_outreg mpexp = 
  match mpexp with
  | MPat_pat mpat -> get_mpat_outreg mpat
  | _ -> ""

let rec get_mpat_inregs (MP_aux (mp_aux, _) as mpat) =
  match mp_aux with
  | MP_string_append pats ->
    let rec get_inreg_pat patts n =
      let delimeter n =
        if n = 0 then "" else ","
      in
      match patts with 
      | [] -> ""
      | h :: t -> 
        if str_contains (string_of_mpat h) "reg_name" then
          let reg_name = get_func_param (string_of_mpat h)  in
          (match reg_name with
          | "ms3" -> delimeter n ^ "MR:$" ^ reg_name ^ get_inreg_pat t (n + 1) 
          | "ms2" -> delimeter n ^ "MR:$" ^ reg_name ^ get_inreg_pat t (n + 1) 
          | "ms1" -> delimeter n ^ "MR:$" ^ reg_name ^ get_inreg_pat t (n + 1)
          | "rs1" -> delimeter n ^ "GPR:$" ^ reg_name ^ get_inreg_pat t (n + 1)
          | _ -> "" ^ get_inreg_pat t n)
        else
          get_inreg_pat t n
    in
    get_inreg_pat pats 0
  | _ -> ""

let get_instr_inregs mpexp = 
  match mpexp with
  | MPat_pat mpat -> get_mpat_inregs mpat
  | _ -> ""

let rec get_mpat_argstr (MP_aux (mp_aux, _) as mpat) =
  match mp_aux with
  | MP_string_append pats ->
    let rec get_argstr patts n =
      let delimeter n =
        if n = 0 then "" else ","
      in
      match patts with 
      | [] -> ""
      | h :: t -> 
        if str_contains (string_of_mpat h) "reg_name" then
          let reg_name = get_func_param (string_of_mpat h)  in
          (match reg_name with
          | "rs1" -> delimeter n ^ "(${" ^ reg_name ^ "})" ^ get_argstr t (n+1)
          | _ -> delimeter n ^ "$" ^ reg_name ^  get_argstr t (n+1))
        else
          get_argstr t n
    in
    get_argstr pats 0
  | _ -> ""

let get_instr_argstr mpexp = 
  match mpexp with
  | MPat_pat mpat -> get_mpat_argstr mpat
  | _ -> ""

let matrix_instclass_string mpexp1 mpexp2 =
  let inst_name = get_instr_name mpexp1 in
  let outreg = "(outs " ^ get_instr_outreg mpexp2  ^ " ),\n" in
  let inreg = "(ins " ^ get_instr_inregs mpexp2 ^ ")," in
  let argstr = get_instr_argstr mpexp2 in

  let header = "\nlet hasSideEffects = 0, mayLoad = 0, mayStore = 0 in {\n" in 
  header ^ "class M" ^ inst_name ^ "<string opcodestr>\n : RVInst" ^ inst_name ^ "<" ^ outreg ^ inreg ^
  "opcodestr,\n" ^ "\"" ^ argstr ^ "\">;\n}\n\n"

let instclass_string  (MPat_aux(mpexp1, _)) (MPat_aux(mpexp2, _))= 
  let annot = get_mpexp_annot mpexp1 in
  match annot with
    | "MM" -> matrix_instclass_string mpexp1 mpexp2
    | _ -> ""

let rec get_mpat_mnemonic (MP_aux (mp_aux, _) as mpat) = 
  match mp_aux with
  | MP_string_append pats ->
    let get_first_assembly_pat patts = 
      match patts with 
      | [] -> ""
      | h :: t -> 
        string_of_mpat h
    in
    get_first_assembly_pat pats
  | _ -> ""

let get_instr_mnemonic mpexp = 
  match mpexp with
  | MPat_pat mpat -> get_mpat_mnemonic mpat
  | _ -> ""


let rec get_mpat_sched_order (MP_aux (mp_aux, _) as mpat) inst_name = 
  match mp_aux with
  | MP_string_append pats ->
    let rec get_sched_order patts inst_name n =
      let delimeter n =
        if n = 0 then "" else ","
      in
      match patts with 
      | [] -> ""
      | h :: t -> 
        if str_contains (string_of_mpat h) "reg_name" then
          let reg_name = get_func_param (string_of_mpat h)  in
          (match reg_name with
          | "md" -> delimeter n ^ "Write" ^ inst_name ^ (get_sched_order t inst_name (n+1))
          | "ms3" -> delimeter n ^ "Write"  ^ inst_name ^ (get_sched_order t inst_name (n+1))
          | "ms2" -> delimeter n ^ "Read"  ^ inst_name ^ (get_sched_order t inst_name (n+1))
          | "ms1" -> delimeter n ^ "Read"  ^ inst_name ^ (get_sched_order t inst_name (n+1))
          | "rs1" -> delimeter n ^ "Read"  ^ inst_name ^ (get_sched_order t inst_name (n+1))
          | _ -> "")
        else
          get_sched_order t inst_name n
    in
    get_sched_order pats inst_name 0
  | _ -> ""

let get_instr_sched_order mpexp inst_name = 
  match mpexp with
  | MPat_pat mpat -> get_mpat_sched_order mpat inst_name
  | _ -> ""

let matrix_instdef_string mpexp1 mpexp2 =
  let inst_name = get_instr_name mpexp1 in
  let inst_mnemonic = get_instr_mnemonic mpexp2 in
  let sched_order = get_instr_sched_order mpexp2 inst_name in

  "def " ^ inst_name ^ " : M" ^ inst_name ^ "<" ^ inst_mnemonic ^ ">,\n" ^
  "Sched<[" ^ sched_order ^"]>;\n\n"

let instdef_string (MPat_aux(mpexp1, _)) (MPat_aux(mpexp2, _)) = 
  let annot = get_mpexp_annot mpexp1 in
  match annot with
    | "MM" -> matrix_instdef_string mpexp1 mpexp2
    | _ -> ""

let sail_to_td id (MCL_aux(cl,_)) outtype =
  match string_of_id(id) with
    | "encdec" ->
      (match cl with 
      | MCL_bidir (mpexp1, mpexp2) ->
        (match outtype with
          | "formats" -> formats_string mpexp1 mpexp2
          | "scheduler" -> scheduler_string mpexp1
          | "uscheduler" ->  uscheduler_string mpexp1
          | _ -> "")
      | _ -> "")
    | "assembly" ->
      (match cl with 
      | MCL_bidir (mpexp1, mpexp2) ->
         (match outtype with
           | "instclass" -> instclass_string mpexp1 mpexp2
           | "instdef" -> instdef_string mpexp1 mpexp2
           | _ -> "")
      | _ -> "")
    | _ -> ""

let rec tablegen_mapcl id mapcls outtype  =
  match mapcls with
  | [] -> ""
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

  let outtype = "instdef" in
  let instdef = process_defs outtype ast.defs  in

  let outtype = "instclass" in
  let instclass = process_defs outtype ast.defs  in

  
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
  Pretty_print_sail.pp_ast stdout ast
