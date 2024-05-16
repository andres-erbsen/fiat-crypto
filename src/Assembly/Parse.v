Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Equality.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.Strings.Parse.Common.
Require Import Crypto.Util.Strings.ParseArithmetic.
Require Import Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Strings.Show.Enum.
Require Import Crypto.Util.Listable.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sum.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope parse_scope.

Derive REG_Listable SuchThat (@FinitelyListable REG REG_Listable) As REG_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances REG_Listable REG_FinitelyListable.

Global Instance show_REG : Show REG.
Proof. prove_Show_enum (). Defined.
Global Instance show_lvl_REG : ShowLevel REG := show_REG.

Derive FLAG_Listable SuchThat (@FinitelyListable FLAG FLAG_Listable) As FLAG_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances FLAG_Listable FLAG_FinitelyListable.

Global Instance show_FLAG : Show FLAG.
Proof. prove_Show_enum (). Defined.
Global Instance show_lvl_FLAG : ShowLevel FLAG := show_FLAG.

Derive OpCode_Listable SuchThat (@FinitelyListable OpCode OpCode_Listable) As OpCode_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances OpCode_Listable OpCode_FinitelyListable.

Global Instance show_OpCode : Show OpCode.
Proof. prove_Show_enum (). Defined.
Global Instance show_lvl_OpCode : ShowLevel OpCode := show_OpCode.

Derive OpPrefix_Listable SuchThat (@FinitelyListable OpPrefix OpPrefix_Listable) As OpPrefix_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances OpPrefix_Listable OpPrefix_FinitelyListable.

Global Instance show_OpPrefix : Show OpPrefix.
Proof. prove_Show_enum (). Defined.
Global Instance show_lvl_OpPrefix : ShowLevel OpPrefix := show_OpPrefix.

Definition parse_REG_list : list (string * REG)
  := Eval vm_compute in
      List.map
        (fun r => (show r, r))
        (list_all REG).

Definition parse_REG : ParserAction REG
  := parse_strs parse_REG_list.

Definition parse_FLAG_list : list (string * FLAG)
  := Eval vm_compute in
      List.map
        (fun r => (show r, r))
        (list_all FLAG).

Definition parse_FLAG : ParserAction FLAG
  := parse_strs parse_FLAG_list.

Derive AccessSize_Listable SuchThat (@FinitelyListable AccessSize AccessSize_Listable) As AccessSize_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances AccessSize_Listable AccessSize_FinitelyListable.

Global Instance show_AccessSize : Show AccessSize.
Proof. prove_Show_enum (). Defined.
Global Instance show_lvl_AccessSize : ShowLevel AccessSize := show_AccessSize.

Definition parse_AccessSize_list : list (string * AccessSize)
  := Eval vm_compute in
      List.map
        (fun r => (show r, r))
        (list_all AccessSize).

Definition parse_AccessSize : ParserAction AccessSize
  := (parse_strs_casefold parse_AccessSize_list ;;L (casefold " ptr")?).


(* Do we want to support anything else from the printable characters?
!""#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~ *)
(* According to https://www.nasm.us/xdoc/2.15.05/html/nasmdoc3.html:
Valid characters in labels are letters, numbers, _, $, #, @, ~, ., and ?. The only characters which may be used as the first character of an identifier are letters, . (with special meaning: see section 3.9), _ and ?. An identifier may also be prefixed with a $ to indicate that it is intended to be read as an identifier and not a reserved word; thus, if some other module you are linking with defines a symbol called eax, you can refer to $eax in NASM code to distinguish the symbol from the register. Maximum length of an identifier is 4095 characters. *)
Definition parse_label : ParserAction string
  := let parse_any_ascii s := parse_alt_list (List.map parse_ascii (list_ascii_of_string s)) in
     parse_map
       (fun '(char, ls) => string_of_list_ascii (char :: ls))
       (([a-zA-Z] || parse_any_ascii "._?$") ;;
        (([a-zA-Z] || parse_any_ascii "0123456789_$#@~.?")* )).

Definition parse_MEM : ParserAction MEM
  := parse_map
       (fun '(access_size, (br (*base reg*), sr (*scale reg, including z *), offset, base_label))
        => {| mem_bits_access_size := access_size:option AccessSize
           ; mem_base_reg := br:option REG
           ; mem_base_label := base_label
           ; mem_scale_reg := sr:option (Z * REG)
           ; mem_offset := offset:option Z |})
       (((strip_whitespace_after parse_AccessSize)?) ;;
        (parse_option_list_map
           (fun '(offset, vars)
            => (vars <-- List.map (fun '(c, (v, e), vs) => match vs, e with [], 1%Z => Some (c, v) | _, _ => None end) vars;
                let regs : list (Z * REG) := Option.List.map (fun '(c, v) => match v with inl v => Some (c, v) | inr _ => None end) vars in
                let labels : list (Z * string) := Option.List.map (fun '(c, v) => match v with inr v => Some (c, v) | inl _ => None end) vars in
                base_label <- match labels with
                              | [] => Some None
                              | [(1%Z, lbl)] => Some (Some lbl)
                              | _ => None
                              end;
                let offset := if (0 =? offset)%Z then None else Some offset in
                base_scale_reg <- match regs with
                                  | [] => Some (None, None)
                                  | [(1%Z, r)] => Some (Some r, None)
                                  | [(s, r)] => Some (None, Some (s, r))
                                  | [(1%Z, r1); (s, r2)]
                                  | [(s, r2); (1%Z, r1)]
                                    => Some (Some r1, Some (s, r2))
                                  | _ => None
                                  end;
                let '(br, sr) := base_scale_reg in
                Some (br (*base reg*), sr (*scale reg, including z *), offset, base_label))%option)
           ("[" ;;R parse_Z_poly_strict (sum_beq _ _ REG_beq String.eqb) (parse_or_else_gen (fun x => x) parse_REG parse_label) ;;L "]"))).

Definition parse_CONST (const_keyword : bool) : ParserAction CONST
  := if const_keyword
     then "CONST " ;;R parse_Z_arith_strict ;;L parse_lookahead_not parse_one_whitespace
     else parse_lookahead_not parse_one_whitespace ;;R parse_Z_arith_strict ;;L parse_lookahead_not parse_one_whitespace.

Definition parse_JUMP_LABEL : ParserAction JUMP_LABEL
  := parse_map
       (fun '(near, lbl)
        => {| jump_near := if near:option _ then true else false
           ; label_name := lbl : string
           |})
       ((strip_whitespace_after "NEAR ")? ;; parse_label).

(* we only parse something as a label if it cannot possibly be anything else, because asm is terrible and has ambiguous parses otherwise :-( *)
Definition parse_ARG (const_keyword : bool) : ParserAction ARG
  := parse_or_else
       (parse_alt_list
          [parse_map reg parse_REG
           ; parse_map mem parse_MEM
           ; parse_map const (parse_CONST const_keyword)])
       (parse_map label parse_JUMP_LABEL).

Definition parse_OpCode_list : list (string * OpCode)
  := Eval vm_compute in
      List.map
        (fun r => (show r, r))
        (list_all OpCode).

Definition parse_OpCode : ParserAction OpCode
  := parse_strs_case_insensitive parse_OpCode_list.

Definition parse_OpPrefix_list : list (string * OpPrefix)
  := Eval vm_compute in
      List.map
        (fun r => (show r, r))
        (list_all OpPrefix).

Definition parse_OpPrefix : ParserAction OpPrefix
  := parse_strs parse_OpPrefix_list.

(** assumes no leading nor trailing whitespace and no comment *)
Definition parse_RawLine : ParserAction RawLine
  := fun s
     => let s := String.trim s in
        (* get the first space-separated opcode *)
        let '(mnemonic, args) := String.take_while_drop_while (fun ch => negb (Ascii.is_whitespace ch)) s in
        let args := String.trim args in
        if (String.to_upper mnemonic =? "SECTION")
        then [(SECTION args, "")]
        else if (String.to_upper mnemonic =? "GLOBAL")
        then [(GLOBAL args, "")]
        else if (String.to_upper mnemonic =? "ALIGN")
        then [(ALIGN args, "")]
        else if (String.to_upper mnemonic =? "DEFAULT") && (String.to_upper args =? "REL")
        then [(DEFAULT_REL, "")]
        else if String.endswith ":" s
        then [(LABEL (substring 0 (pred (String.length s)) s), "")]
        else if (s =? "")
        then [(EMPTY, "")]
        else let parsed_prefix := (parse_OpPrefix ;;L ε) mnemonic in
             List.flat_map
               (fun '(parsed_prefix, mnemonic, args)
                => let parsed_mnemonic := (parse_OpCode ;;L ε) mnemonic in
                   let parsed_args := (parse_list_gen "" "," "" (parse_ARG false) ;;L ε) args in
                   List.flat_map
                     (fun '(opc, _)
                      => List.map
                           (fun '(argsv, _) => (INSTR {| prefix := parsed_prefix ; op := opc ; args := argsv |}, ""))
                           parsed_args)
                     parsed_mnemonic)
               match parsed_prefix with
               | []
                 => [(None, mnemonic, args)]
               | _
                 => List.map
                      (fun '(parsed_prefix, _)
                       => let '(mnemonic, args) := String.take_while_drop_while (fun ch => negb (Ascii.is_whitespace ch)) args in
                          let args := String.trim args in
                          (Some parsed_prefix, mnemonic, args))
                      parsed_prefix
               end.

Definition parse_Line (line_num : N) : ParserAction Line
  := fun s
     => let '(indentv, rest_linev) := take_while_drop_while Ascii.is_whitespace s in
        let '(precommentv, commentv)
            := match String.split ";" rest_linev with
               | [] => ("", None)
               | [precommentv] => (String.rtrim precommentv, None)
               | precommentv::commentv => (precommentv, Some (String.concat ";" commentv))
               end in
        let '(rev_trailing_whitespacev, rev_rawlinev) := take_while_drop_while Ascii.is_whitespace (String.rev precommentv) in
        let rawlinev := String.rev rev_rawlinev in
        let trailing_whitespacev := String.rev rev_trailing_whitespacev in
        List.map
          (fun '(r, rem) => ({| indent := indentv ; rawline := r ; pre_comment_whitespace := trailing_whitespacev ; comment := commentv ; line_number := line_num |}, rem))
          (parse_RawLine rawlinev).

(* the error is the unparsable lines *)
Fixpoint parse_Lines' (l : list string) (line_num : N) : ErrorT (list string) Lines
  := match l with
     | [] => Success []
     | l :: ls
       => match finalize (parse_Line line_num) l, parse_Lines' ls (line_num + 1) with
          | None, Error ls => Error (("Line " ++ show line_num ++ ": " ++ l) :: ls)
          | None, Success _ => Error (("Line " ++ show line_num ++ ": " ++ l) :: nil)
          | Some _, Error ls => Error ls
          | Some l, Success ls => Success (l :: ls)
          end
     end.

Definition parse_Lines (l : list string) : ErrorT (list string) Lines
  := parse_Lines' (String.split_newlines l) 1.

Notation parse := parse_Lines (only parsing).

Global Instance show_lvl_MEM : ShowLevel MEM
  := fun m
     => (match m.(mem_bits_access_size) with
         | Some n
           => show_lvl_app (fun 'tt => if n =? 8 then "byte" else if n =? 64 then "QWORD PTR" else "BAD SIZE")%N (* TODO: Fix casing and stuff *)
         | None => show_lvl
         end)
          (fun 'tt
           =>       match m.(mem_offset) with Some o => Hex.show_Z o | _ => "" end ++
                    "(" ++ 
                    match m.(mem_base_reg) with Some r => "%"++show r | _ => "" end ++ (
                    if is_None m.(mem_scale_reg) && is_None m.(mem_bits_access_size) then "" else
                    "," ++
                    match m.(mem_scale_reg) with Some r => "%"++show r | _ => "" end ++ "," ++
                    match m.(mem_bits_access_size) with Some s => show (bits_of_AccessSize s) | _ => "" end)
                             ++ ")").
Global Instance show_MEM : Show MEM := show_lvl_MEM.

Global Instance show_lvl_JUMP_LABEL : ShowLevel JUMP_LABEL
  := fun l _
     => ((if l.(jump_near) then "NEAR " else "")
           ++ l.(label_name)).
Global Instance show_JUMP_LABEL : Show JUMP_LABEL := show_lvl_JUMP_LABEL.

Global Instance show_lvl_ARG : ShowLevel ARG
  := fun a
     => match a with
        | reg r => fun l => "%"++show_lvl r l
        | mem m => show_lvl m
        | const c => fun l => "$"++Hex.show_Z c
        | label l => show_lvl l
        end.
Global Instance show_ARG : Show ARG := show_lvl_ARG.

Definition att_operand_order (instr : NormalInstruction) : list ARG :=
  match instr.(op), instr.(args) with
  | (mov | movzx), [dst; src] => [src; dst]
  | xchg, [a; b] => [a; b]
  | (setc | seto) as opc, [dst] => [dst]
  | clc, [] => []
  | cmovc, [dst; src] (* CMOVcc: Flags Affected: None *)
  | cmovb, [dst; src]
  | cmovo, [dst; src]
  | cmovnz, [dst; src] => [src; dst]
  | lea, [reg dst; mem src] => [mem src; reg dst]
  | (add | adc) as opc, [dst; src] => [src; dst]
  | (adcx | adox) as opc, [dst; src] => [src; dst]
  | (sbb | sub) as opc, [dst; src] => [src; dst]
  | dec, [dst] => [dst]
  | inc, [dst] => [dst]
  | mulx, [hi; lo; src2] => [src2; lo; hi]
  | (Syntax.mul | imul), [src2] => [src2]
  | imul, [src1; src2] => [src1; src2]
  | imul, [dst; src1; src2] => [src1; src2; dst]
  | sar, [dst; cnt] => [cnt; dst]
  | shl, [dst; cnt] => [cnt; dst]
  | shlx, [dst; src; cnt] => [src; cnt; dst]
  | shr, [dst; cnt] => [cnt; dst]
  | rcr, [dst; cnt] => [cnt; dst]
  | shrd, [dst as lo; hi; cnt] => [label (Build_JUMP_LABEL false "#error TODO_shrd"%string); hi; cnt; dst]
  | (and | xor | or) as opc, [dst; src] => [src; dst]
  | bzhi, [dst; src1; src2] => [src1; src2; dst]
  | test, [src1; src2] => [src1; src2]
  | push, [src] => [src]
  | pop, [dst] => [dst]
  | _, _ => [label (Build_JUMP_LABEL false "#error unimplemented att_operand_order")]
  end.

Global Instance show_NormalInstruction : Show NormalInstruction
  := fun i
     => match i.(prefix) with
        | None => ""
        | Some prefix => show prefix ++ " "
        end
          ++ (show i.(op))
          ++ match operation_size i with (* integer operations only *)
             | Some 8 => "b" | Some 16 => "w" | Some 32 => "l" | Some 64 => "q"
             | _ => "#error"
             end%N
          ++ match att_operand_order i with
             | [] => ""
             | args => " " ++ String.concat ", " (List.map show args)
             end.

Global Instance show_RawLine : Show RawLine
  := fun l
     => match l with
        | SECTION name => "SECTION " ++ name
        | GLOBAL name => "GLOBAL " ++ name
        | ALIGN args => "ALIGN " ++ args
        | DEFAULT_REL => "DEFAULT REL"
        | LABEL name => name ++ ":"
        | EMPTY => ""
        | INSTR instr => show instr
        end.

Global Instance show_Line : Show Line
  := fun l
     => l.(indent) ++ show l.(rawline) ++ l.(pre_comment_whitespace) ++ match l.(comment) with
                                                                        | Some c => ";" ++ c
                                                                        | None => ""
                                                                        end.

Definition show_Line_with_line_number : Show Line
  := fun l => show l ++ "; (line " ++ show l.(line_number) ++ ")".

Global Instance show_lines_Lines : ShowLines Lines
  := fun ls => List.map show ls.

Definition parse_correct_on (v : list string)
  := forall res, parse v = Success res -> parse v = parse (show_lines res).

Inductive ParseError :=
| Parse_error (msgs : list string)
.

Inductive ParseValidatedError :=
| Initial_parse_error (err : ParseError)
| Reparse_error (new_asm : list string) (err : ParseError)
| Lengths_not_equal (old_asm : Lines) (new_asm : Lines)
| Lines_not_equal (mismatched_lines : list (Line * Line))
| Duplicate_labels (name_counts : list (string * nat))
.
Global Coercion Initial_parse_error : ParseError >-> ParseValidatedError.

Global Instance show_lines_ParseError : ShowLines ParseError
  := fun err => match err with
                | Parse_error err => err
                end.
Global Instance show_ParseError : Show ParseError := _.
Global Instance show_lines_ParseValidatedError : ShowLines ParseValidatedError
  := fun err => match err with
                | Initial_parse_error err
                  => match show_lines err with
                     | [] => ["Unknown error while parsing assembly"]
                     | [err] => ["Error while parsing assembly: " ++ err]%string
                     | lines => "Error while parsing assembly:" :: lines
                     end
                | Reparse_error new_asm err
                  => match show_lines err with
                     | [] => ["Unknown error while reparsing assembly:"] ++ new_asm
                     | [err] => (["Error while reparsing assembly: " ++ err
                                  ; "New assembly being parsed:"]%string)
                                  ++ new_asm
                     | lines => ["Error while parsing assembly:"]
                                  ++ lines
                                  ++ [""]
                                  ++ ["New assembly being parsed:"]
                                  ++ new_asm
                     end
                | Lengths_not_equal old_asm new_asm
                  => ["Reparsing the assembly:"]
                       ++ show_lines old_asm
                       ++ [""]
                       ++ ["Yielded non-equal assembly:"]
                       ++ show_lines new_asm
                       ++ [""]
                       ++ (["The number of lines was not equal (" ++ show (List.length old_asm) ++ " ≠ " ++ show (List.length new_asm) ++ ")"]%string)
                | Lines_not_equal mismatched_lines
                  => ["When reparsing assembly for validation, the following lines were not equal:"]
                       ++ (List.flat_map (fun '(old, new) => ["- " ++ show old; "+ " ++ show new; ""]%string)
                                         mismatched_lines)
                | Duplicate_labels nil
                  => ["Internal error: Duplicate_labels []"]
                | Duplicate_labels [(name, count)]
                  => ["Label occurs multiple times: " ++ name ++ " occurs " ++ show count ++ " times"]%string
                | Duplicate_labels name_counts
                  => ["Labels occurs multiple times:"]
                       ++ List.map (fun '(name, count) => name ++ " occurs " ++ show count ++ " times")%string name_counts
                end%list.
Global Instance show_ParseValidatedError : Show ParseValidatedError := _.

Definition parse_validated (v : list string) : ErrorT ParseValidatedError Lines
  := match parse v with
     | Success v
       => let new_asm := show_lines v in
          match parse new_asm with
          | Success v'
            => let labels := Option.List.map (fun l => match l.(rawline) with
                                                       | LABEL n => Some n
                                                       | _ => None
                                                       end) v' in
               let counts := List.map (fun l => (l, List.count_occ string_dec labels l)) labels in
               let big_counts := List.filter (fun '(l, n) => (1 <? n)%nat) counts in
               match big_counts with
               | nil
                 => if (List.length v =? List.length v')%nat
                    then match List.filter (fun '(x, y) => negb (Line_beq x y)) (List.combine v v') with
                         | nil => Success v
                         | mismatched_lines => Error (Lines_not_equal mismatched_lines)
                         end
                    else Error (Lengths_not_equal v v')
               | _ => Error (Duplicate_labels big_counts)
               end
          | Error e
            => Error (Reparse_error new_asm (Parse_error e))
          end
     | Error e => Error (Initial_parse_error (Parse_error e))
     end.

Definition parse_correct_on_bool (v : list string) : bool
  := match parse v, parse_validated v with
     | Success _, Success _ => true
     | Error _, _ => true
     | Success _, Error _ => false
     end.

Definition parse_validated_correct_on v
  := forall res, parse_validated v = Success res <-> parse v = Success res.

Lemma parse_validated_correct_on_iff v : parse_validated_correct_on v <-> parse_correct_on v.
Proof.
  cbv [parse_validated_correct_on parse_correct_on parse_validated].
  destruct (parse_Lines v) eqn:Hp; [ | split; [ congruence | split; congruence ] ].
  destruct (parse_Lines (show_lines _)) eqn:Hp2; (split; [ intros H res Hres; inversion Hres; subst | intro H; specialize (H _ eq_refl); rewrite <- H in Hp2; inversion Hp2; subst ]); rewrite ?Nat.eqb_refl, ?combine_same; try congruence.
  all: repeat first [ progress destruct_head' iff
                    | congruence
                    | progress subst
                    | progress rewrite ?Nat.eqb_eq in *
                    | match goal with
                      | [ H : forall x, _ <-> Success ?y = Success x |- _ ] => specialize (H y)
                      | [ H : ?x = ?x |- _ ] => clear H
                      | [ H : Success ?x = Success ?y |- _ ] => inversion H; clear H
                      | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
                      end
                    | break_innermost_match_hyps_step
                    | progress break_match_hyps
                    | progress break_match
                    | progress intros
                    | apply conj ].
Abort.

Lemma parse_correct_on_bool_iff v : parse_correct_on_bool v = true <-> parse_correct_on v.
Proof.
  assert (parse_validated_correct_on_iff : forall v, parse_validated_correct_on v <-> parse_correct_on v) by admit.
  rewrite <- parse_validated_correct_on_iff.
  cbv [parse_correct_on_bool parse_validated_correct_on].
  destruct (parse_Lines v) eqn:Heq1, (parse_validated v) eqn:Heq2; split; try split; try congruence.
Abort.

(* This version allows for easier debugging because it highlights the differences *)
Definition parse_correct_on_debug (v : list string)
  := match parse v with
     | Success v => match parse (show_lines v) with
                    | Success v'
                      => if (List.length v =? List.length v')%nat
                         then List.filter (fun '(x, y) => negb (Line_beq x y)) (List.combine v v') = nil
                         else List.length v = List.length v'
                    | Error e => forall x, e = x -> False
                    end
     | Error e => forall x, e = x -> False
     end.
Theorem parse_correct : forall v, parse_correct_on v.
Proof. Abort.

(** Some extra utility functions for processing assembly files *)
(** We assume that the asm file contains GLOBAL declarations for each
    function.  The function name must match the name which would be
    generated by fiat-crypto.  The function names declare the labels
    that break up instructions into functions.  We currently associate
    lines (including blank and comment lines) before a label to the
    previous label, though plausibly there should be some other
    heuristic for dealing with comments. *)

Definition find_globals (ls : Lines) : list string
  := Option.List.map
       (fun l => match l.(rawline) with
                 | GLOBAL name => Some name
                 | _ => None
                 end)
       ls.

Fixpoint split_code_to_functions' (globals : list string) (ls : Lines) : Lines (* prefix *) * list (string (* global name *) * Lines)
  := match ls with
     | [] => ([], [])
     | l :: ls
       => let '(prefix, rest) := split_code_to_functions' globals ls in
          let default := (l :: prefix, rest) in
          match l.(rawline) with
          | LABEL name => if List.existsb (fun n => name =? n)%string globals
                          then ([], (name, l::prefix) :: rest)
                          else default
          | _ => default
          end
     end.

Definition split_code_to_functions (ls : Lines) : Lines (* prefix *) * list (string (* global name *) * Lines)
  := let globals := find_globals ls in
     split_code_to_functions' globals ls.

Definition ex := [
";#include <openssl/asm_base.h>";
"";
";;#if !defined(OPENSSL_NO_ASM) && defined(OPENSSL_X86_64) && \";
" ;   (defined(__APPLE__) || defined(__ELF__))";
"";
";.text";
";#if defined(__APPLE__)";
";.private_extern _fiat_p256_adx_mul";
";.global _fiat_p256_adx_mul";
"_fiat_p256_adx_mul:";
";#else";
";.type fiat_p256_adx_mul, @function";
";.hidden fiat_p256_adx_mul";
";.global fiat_p256_adx_mul";
"fiat_p256_adx_mul:";
";#endif";
"";
";.cfi_startproc";
";_CET_ENDBR";
"push rbp";
";;.cfi_adjust_cfa_offset 8";
";.cfi_offset rbp, -16";
"mov rbp, rsp";
"mov rax, rdx";
"mov rdx, [ rsi + 0x0 ]";
"test al, al";
"mulx r8, rcx, [ rax + 0x0 ]";
"mov [ rsp - 0x80 ], rbx";
";.cfi_offset rbx, -16-0x80";
"mulx rbx, r9, [ rax + 0x8 ]";
"mov [ rsp - 0x68 ], r14";
";.cfi_offset r14, -16-0x68";
"adc r9, r8";
"mov [ rsp - 0x60 ], r15";
";.cfi_offset r15, -16-0x60";
"mulx r15, r14, [ rax + 0x10 ]";
"mov [ rsp - 0x78 ], r12";
";.cfi_offset r12, -16-0x78";
"adc r14, rbx";
"mulx r11, r10, [ rax + 0x18 ]";
"mov [ rsp - 0x70 ], r13";
";.cfi_offset r13, -16-0x70";
"adc r10, r15";
"mov rdx, [ rsi + 0x8 ]";
"mulx rbx, r8, [ rax + 0x0 ]";
"adc r11, 0x0";
"xor r15, r15";
"adcx r8, r9";
"adox rbx, r14";
"mov [ rsp - 0x58 ], rdi";
"mulx rdi, r9, [ rax + 0x8 ]";
"adcx r9, rbx";
"adox rdi, r10";
"mulx rbx, r14, [ rax + 0x10 ]";
"adcx r14, rdi";
"adox rbx, r11";
"mulx r13, r12, [ rax + 0x18 ]";
"adcx r12, rbx";
"mov rdx, 0x100000000";
"mulx r11, r10, rcx";
"adox r13, r15";
"adcx r13, r15";
"xor rdi, rdi";
"adox r10, r8";
"mulx r8, rbx, r10";
"adox r11, r9";
"adcx rbx, r11";
"adox r8, r14";
"mov rdx, 0xffffffff00000001";
"mulx r9, r15, rcx";
"adcx r15, r8";
"adox r9, r12";
"mulx r14, rcx, r10";
"mov rdx, [ rsi + 0x10 ]";
"mulx r10, r12, [ rax + 0x8 ]";
"adcx rcx, r9";
"adox r14, r13";
"mulx r11, r13, [ rax + 0x0 ]";
"mov r9, rdi";
"adcx r14, r9";
"adox rdi, rdi";
"adc rdi, 0x0";
"xor r9, r9";
"adcx r13, rbx";
"adox r11, r15";
"mov rdx, [ rsi + 0x10 ]";
"mulx r15, r8, [ rax + 0x10 ]";
"adox r10, rcx";
"mulx rcx, rbx, [ rax + 0x18 ]";
"mov rdx, [ rsi + 0x18 ]";
"adcx r12, r11";
"mulx rsi, r11, [ rax + 0x8 ]";
"adcx r8, r10";
"adox r15, r14";
"adcx rbx, r15";
"adox rcx, r9";
"adcx rcx, r9";
"mulx r15, r10, [ rax + 0x0 ]";
"add rcx, rdi";
"mov r14, r9";
"adc r14, 0";
"xor r9, r9";
"adcx r10, r12";
"adox r15, r8";
"adcx r11, r15";
"adox rsi, rbx";
"mulx r8, r12, [ rax + 0x10 ]";
"adox r8, rcx";
"mulx rcx, rbx, [ rax + 0x18 ]";
"adcx r12, rsi";
"adox rcx, r9";
"mov rdx, 0x100000000";
"adcx rbx, r8";
"adc rcx, 0";
"mulx rdi, r15, r13";
"xor rax, rax";
"adcx rcx, r14";
"adc rax, 0";
"xor r9, r9";
"adox r15, r10";
"mulx r14, r10, r15";
"adox rdi, r11";
"mov rdx, 0xffffffff00000001";
"adox r14, r12";
"adcx r10, rdi";
"mulx r12, r11, r13";
"adcx r11, r14";
"adox r12, rbx";
"mulx rbx, r13, r15";
"adcx r13, r12";
"adox rbx, rcx";
"mov r8, r9";
"adox rax, r9";
"adcx r8, rbx";
"adc rax, 0x0";
"mov rcx, rax";
"mov r15, 0xffffffffffffffff";
"mov rdi, r10";
"sub rdi, r15";
"mov r14, 0xffffffff";
"mov r12, r11";
"sbb r12, r14";
"mov rbx, r13";
"sbb rbx, r9";
"mov rax, rax";
"mov rax, r8";
"sbb rax, rdx";
"sbb rcx, r9";
"cmovc rdi, r10";
"mov r10, [ rsp - 0x58 ]";
"cmovc rbx, r13";
"mov r13, [ rsp - 0x70 ]";
";.cfi_restore r13";
"cmovc r12, r11";
"cmovc rax, r8";
"mov [ r10 + 0x10 ], rbx";
"mov rbx, [ rsp - 0x80 ]";
";.cfi_restore rbx";
"mov [ r10 + 0x0 ], rdi";
"mov [ r10 + 0x8 ], r12";
"mov [ r10 + 0x18 ], rax";
"mov r12, [ rsp - 0x78 ]";
";.cfi_restore r12";
"mov r14, [ rsp - 0x68 ]";
";.cfi_restore r14";
"mov r15, [ rsp - 0x60 ]";
";.cfi_restore r15";
"pop rbp";
";.cfi_restore rbp";
";.cfi_adjust_cfa_offset -8";
"ret";
";.cfi_endproc";
";#if defined(__ELF__)";
";.size fiat_p256_adx_mul, .-fiat_p256_adx_mul";
";#endif";
"";
";#endif"].

Definition exs := [
";#include <openssl/asm_base.h>";
"";
";#if !defined(OPENSSL_NO_ASM) && defined(OPENSSL_X86_64) && \";
";    (defined(__APPLE__) || defined(__ELF__))";
"";
";.text";
";#if defined(__APPLE__)";
";.private_extern _fiat_p256_adx_sqr";
";.global _fiat_p256_adx_sqr";
"_fiat_p256_adx_sqr:";
";#else";
";.type fiat_p256_adx_sqr, @function";
";.hidden fiat_p256_adx_sqr";
";.global fiat_p256_adx_sqr";
"fiat_p256_adx_sqr:";
";#endif";
"";
";.cfi_startproc";
";_CET_ENDBR";
"push rbp";
";.cfi_adjust_cfa_offset 8";
";.cfi_offset rbp, -16";
"mov rbp, rsp";
"mov rdx, [ rsi + 0x0 ]";
"mulx r10, rax, [ rsi + 0x18 ]";
"mulx rcx, r11, rdx";
"mulx r9, r8, [ rsi + 0x8 ]";
"mov [ rsp - 0x80 ], rbx";
";.cfi_offset rbx, -16-0x80";
"xor rbx, rbx";
"adox r8, r8";
"mov [ rsp - 0x78 ], r12";
";.cfi_offset r12, -16-0x78";
"mulx r12, rbx, [ rsi + 0x10 ]";
"mov rdx, [ rsi + 0x8 ]";
"mov [ rsp - 0x70 ], r13";
";.cfi_offset r13, -16-0x70";
"mov [ rsp - 0x68 ], r14";
";.cfi_offset r14, -16-0x68";
"mulx r14, r13, rdx";
"mov [ rsp - 0x60 ], r15";
";.cfi_offset r15, -16-0x60";
"mov [ rsp - 0x58 ], rdi";
"mulx rdi, r15, [ rsi + 0x10 ]";
"adcx r12, r15";
"mov [ rsp - 0x50 ], r11";
"mulx r11, r15, [ rsi + 0x18 ]";
"adcx r10, rdi";
"mov rdi, 0x0";
"adcx r11, rdi";
"clc";
"adcx rbx, r9";
"adox rbx, rbx";
"adcx rax, r12";
"adox rax, rax";
"adcx r15, r10";
"adox r15, r15";
"mov rdx, [ rsi + 0x10 ]";
"mulx r12, r9, [ rsi + 0x18 ]";
"adcx r9, r11";
"adcx r12, rdi";
"mulx r11, r10, rdx";
"clc";
"adcx rcx, r8";
"adcx r13, rbx";
"adcx r14, rax";
"adox r9, r9";
"adcx r10, r15";
"mov rdx, [ rsi + 0x18 ]";
"mulx rbx, r8, rdx";
"adox r12, r12";
"adcx r11, r9";
"mov rsi, [ rsp - 0x50 ]";
"adcx r8, r12";
"mov rax, 0x100000000";
"mov rdx, rax";
"mulx r15, rax, rsi";
"adcx rbx, rdi";
"adox rbx, rdi";
"xor r9, r9";
"adox rax, rcx";
"adox r15, r13";
"mulx rcx, rdi, rax";
"adcx rdi, r15";
"adox rcx, r14";
"mov rdx, 0xffffffff00000001";
"mulx r14, r13, rsi";
"adox r14, r10";
"adcx r13, rcx";
"mulx r12, r10, rax";
"adox r12, r11";
"mov r11, r9";
"adox r11, r8";
"adcx r10, r14";
"mov r8, r9";
"adcx r8, r12";
"mov rax, r9";
"adcx rax, r11";
"mov r15, r9";
"adox r15, rbx";
"mov rdx, 0x100000000";
"mulx rcx, rbx, rdi";
"mov r14, r9";
"adcx r14, r15";
"mov r12, r9";
"adox r12, r12";
"adcx r12, r9";
"adox rbx, r13";
"mulx r11, r13, rbx";
"mov r15, 0xffffffff00000001";
"mov rdx, r15";
"mulx rsi, r15, rbx";
"adox rcx, r10";
"adox r11, r8";
"mulx r8, r10, rdi";
"adcx r13, rcx";
"adox r8, rax";
"adcx r10, r11";
"adox rsi, r14";
"mov rdi, r12";
"mov rax, r9";
"adox rdi, rax";
"adcx r15, r8";
"mov r14, rax";
"adcx r14, rsi";
"adcx rdi, r9";
"dec r9";
"mov rbx, r13";
"sub rbx, r9";
"mov rcx, 0xffffffff";
"mov r11, r10";
"sbb r11, rcx";
"mov r8, r15";
"sbb r8, rax";
"mov rsi, r14";
"sbb rsi, rdx";
"sbb rdi, rax";
"cmovc rbx, r13";
"cmovc r8, r15";
"cmovc r11, r10";
"cmovc rsi, r14";
"mov rdi, [ rsp - 0x58 ]";
"mov [ rdi + 0x18 ], rsi";
"mov [ rdi + 0x0 ], rbx";
"mov [ rdi + 0x8 ], r11";
"mov [ rdi + 0x10 ], r8";
"mov rbx, [ rsp - 0x80 ]";
";.cfi_restore rbx";
"mov r12, [ rsp - 0x78 ]";
";.cfi_restore r12";
"mov r13, [ rsp - 0x70 ]";
";.cfi_restore r13";
"mov r14, [ rsp - 0x68 ]";
";.cfi_restore r14";
"mov r15, [ rsp - 0x60 ]";
";.cfi_restore r15";
"pop rbp";
";.cfi_restore rbp";
";.cfi_adjust_cfa_offset -8";
"ret";
";.cfi_endproc";
";#if defined(__ELF__)";
";.size fiat_p256_adx_sqr, .-fiat_p256_adx_sqr";
";#endif";
"";
";#endif"].

Compute
String.concat "
"
match parse exs
with Success l => show_lines l
        | x => show_lines x end.
