

(* ========================================================================= *)
(* Very basic set theory (using predicates as sets).                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2016                       *)
(*              (c) Copyright, Marco Maggesi 2012-2017                       *)
(*             (c) Copyright, Andrea Gabrielli 2012-2017                     *)
(* ========================================================================= *)

needs "int.ml";;

(* ------------------------------------------------------------------------- *)
(* Infix symbols for set operations.                                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("IN",(11,"right"));;
parse_as_infix("SUBSET",(12,"right"));;
parse_as_infix("PSUBSET",(12,"right"));;
parse_as_infix("INTER",(20,"right"));;
parse_as_infix("UNION",(16,"right"));;
parse_as_infix("DIFF",(18,"left"));;
parse_as_infix("INSERT",(21,"right"));;
parse_as_infix("DELETE",(21,"left"));;

parse_as_infix("HAS_SIZE",(12,"right"));;
parse_as_infix("<=_c",(12,"right"));;
parse_as_infix("<_c",(12,"right"));;
parse_as_infix(">=_c",(12,"right"));;
parse_as_infix(">_c",(12,"right"));;
parse_as_infix("=_c",(12,"right"));;

(* ------------------------------------------------------------------------- *)
(* Set membership.                                                           *)
(* ------------------------------------------------------------------------- *)

export_theory "set-mem-def";;

let IN = new_definition 
  `!P:A->bool. !x. x IN P <=> P x`;;

export_namedthm IN "IN";;

(* ------------------------------------------------------------------------- *)
(* Axiom of extensionality in this framework.                                *)
(* ------------------------------------------------------------------------- *)

export_theory "set-extensionality";;

let EXTENSION = prove 
 (`!s t. (s = t) <=> !x:A. x IN s <=> x IN t`,
  REWRITE_TAC[IN; FUN_EQ_THM]);;

export_namedthm EXTENSION "EXTENSION";;

(* ------------------------------------------------------------------------- *)
(* General specification.                                                    *)
(* ------------------------------------------------------------------------- *)

export_theory "set-spec";;

let GSPEC = new_definition 
  `GSPEC (p:A->bool) = p`;;

export_namedthm GSPEC "GSPEC";;

let SETSPEC = new_definition 
  `SETSPEC v P t <=> P /\ (v = t)`;;

export_namedthm SETSPEC "SETSPEC";;

(* ------------------------------------------------------------------------- *)
(* Rewrite rule for eliminating set-comprehension membership assertions.     *)
(* ------------------------------------------------------------------------- *)

export_theory "set-mem-elim";;

let IN_ELIM_THM = prove 
 (`(!P x. x IN GSPEC (\v. P (SETSPEC v)) <=> P (\p t. p /\ (x = t))) /\
   (!p x. x IN GSPEC (\v. ?y. SETSPEC v (p y) y) <=> p x) /\
   (!P x. GSPEC (\v. P (SETSPEC v)) x <=> P (\p t. p /\ (x = t))) /\
   (!p x. GSPEC (\v. ?y. SETSPEC v (p y) y) x <=> p x) /\
   (!p x. x IN (\y. p y) <=> p x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN; GSPEC] THEN
  TRY(AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM]) THEN
  REWRITE_TAC[SETSPEC] THEN MESON_TAC[]);;

export_namedthm IN_ELIM_THM "IN_ELIM_THM";;

(* ------------------------------------------------------------------------- *)
(* These two definitions are needed first, for the parsing of enumerations.  *)
(* ------------------------------------------------------------------------- *)

export_theory "set-def";;

let EMPTY = new_definition 
  `EMPTY = (\x:A. F)`;;

export_namedthm EMPTY "EMPTY";;

let INSERT_DEF = new_definition 
  `x INSERT s = \y:A. y IN s \/ (y = x)`;;

export_namedthm INSERT_DEF "INSERT_DEF";;

(* ------------------------------------------------------------------------- *)
(* The other basic operations.                                               *)
(* ------------------------------------------------------------------------- *)

export_theory "set-op-def";;

let UNIV = new_definition 
  `UNIV = (\x:A. T)`;;

export_namedthm UNIV "UNIV";;

let UNION = new_definition 
  `s UNION t = {x:A | x IN s \/ x IN t}`;;

export_namedthm UNION "UNION";;

let UNIONS = new_definition 
  `UNIONS s = {x:A | ?u. u IN s /\ x IN u}`;;

export_namedthm UNIONS "UNIONS";;

let INTER = new_definition 
  `s INTER t = {x:A | x IN s /\ x IN t}`;;

export_namedthm INTER "INTER";;

let INTERS = new_definition 
  `INTERS s = {x:A | !u. u IN s ==> x IN u}`;;

export_namedthm INTERS "INTERS";;

let DIFF = new_definition 
  `s DIFF t =  {x:A | x IN s /\ ~(x IN t)}`;;

export_namedthm DIFF "DIFF";;

let INSERT = prove 
 (`x INSERT s = {y:A | y IN s \/ (y = x)}`,
  REWRITE_TAC[EXTENSION; INSERT_DEF; IN_ELIM_THM]);;

export_namedthm INSERT "INSERT";;

let DELETE = new_definition 
  `s DELETE x = {y:A | y IN s /\ ~(y = x)}`;;

export_namedthm DELETE "DELETE";;

(* ------------------------------------------------------------------------- *)
(* Other basic predicates.                                                   *)
(* ------------------------------------------------------------------------- *)

export_theory "set-predicates";;

let SUBSET = new_definition 
  `s SUBSET t <=> !x:A. x IN s ==> x IN t`;;

export_namedthm SUBSET "SUBSET";;

let PSUBSET = new_definition 
  `(s:A->bool) PSUBSET t <=> s SUBSET t /\ ~(s = t)`;;

export_namedthm PSUBSET "PSUBSET";;

let DISJOINT = new_definition 
  `DISJOINT (s:A->bool) t <=> (s INTER t = EMPTY)`;;

export_namedthm DISJOINT "DISJOINT";;

let SING = new_definition 
  `SING s = ?x:A. s = {x}`;;

export_namedthm SING "SING";;

(* ------------------------------------------------------------------------- *)
(* Finiteness.                                                               *)
(* ------------------------------------------------------------------------- *)

export_theory "set-finite";;

let FINITE_RULES,FINITE_INDUCT,FINITE_CASES =
  new_inductive_definition
    `FINITE (EMPTY:A->bool) /\
     !(x:A) s. FINITE s ==> FINITE (x INSERT s)`;;

export_namedthm FINITE_RULES "FINITE_RULES";;
export_namedthm FINITE_INDUCT "FINITE_INDUCT";;
export_namedthm FINITE_CASES "FINITE_CASES";;

let INFINITE = new_definition 
  `INFINITE (s:A->bool) <=> ~(FINITE s)`;;

export_namedthm INFINITE "INFINITE";;

(* ------------------------------------------------------------------------- *)
(* Stuff concerned with functions.                                           *)
(* ------------------------------------------------------------------------- *)

export_theory "set-function";;

let IMAGE = new_definition 
  `IMAGE (f:A->B) s = { y | ?x. x IN s /\ (y = f x)}`;;

export_namedthm IMAGE "IMAGE";;

let INJ = new_definition 
  `INJ (f:A->B) s t <=>
     (!x. x IN s ==> (f x) IN t) /\
     (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))`;;

export_namedthm INJ "INJ";;

let SURJ = new_definition 
  `SURJ (f:A->B) s t <=>
     (!x. x IN s ==> (f x) IN t) /\
     (!x. (x IN t) ==> ?y. y IN s /\ (f y = x))`;;

export_namedthm SURJ "SURJ";;

let BIJ = new_definition 
  `BIJ (f:A->B) s t <=> INJ f s t /\ SURJ f s t`;;

export_namedthm BIJ "BIJ";;

(* ------------------------------------------------------------------------- *)
(* Another funny thing.                                                      *)
(* ------------------------------------------------------------------------- *)

export_theory "set-def";;

let CHOICE = new_definition 
  `CHOICE s = @x:A. x IN s`;;

export_namedthm CHOICE "CHOICE";;

let REST = new_definition 
  `REST (s:A->bool) = s DELETE (CHOICE s)`;;

export_namedthm REST "REST";;

(* ------------------------------------------------------------------------- *)
(* Basic membership properties.                                              *)
(* ------------------------------------------------------------------------- *)

export_theory "set-mem-thm";;

let NOT_IN_EMPTY = prove 
 (`!x:A. ~(x IN EMPTY)`,
  REWRITE_TAC[IN; EMPTY]);;

export_namedthm NOT_IN_EMPTY "NOT_IN_EMPTY";;

let IN_UNIV = prove 
 (`!x:A. x IN UNIV`,
  REWRITE_TAC[UNIV; IN]);;

export_namedthm IN_UNIV "IN_UNIV";;

let IN_UNION = prove 
 (`!s t (x:A). x IN (s UNION t) <=> x IN s \/ x IN t`,
  REWRITE_TAC[IN_ELIM_THM; UNION]);;

export_namedthm IN_UNION "IN_UNION";;

let IN_UNIONS = prove 
 (`!s (x:A). x IN (UNIONS s) <=> ?t. t IN s /\ x IN t`,
  REWRITE_TAC[IN_ELIM_THM; UNIONS]);;

export_namedthm IN_UNIONS "IN_UNIONS";;

let IN_INTER = prove 
 (`!s t (x:A). x IN (s INTER t) <=> x IN s /\ x IN t`,
  REWRITE_TAC[IN_ELIM_THM; INTER]);;

export_namedthm IN_INTER "IN_INTER";;

let IN_INTERS = prove 
 (`!s (x:A). x IN (INTERS s) <=> !t. t IN s ==> x IN t`,
  REWRITE_TAC[IN_ELIM_THM; INTERS]);;

export_namedthm IN_INTERS "IN_INTERS";;

let IN_DIFF = prove 
 (`!(s:A->bool) t x. x IN (s DIFF t) <=> x IN s /\ ~(x IN t)`,
  REWRITE_TAC[IN_ELIM_THM; DIFF]);;

export_namedthm IN_DIFF "IN_DIFF";;

let IN_INSERT = prove 
 (`!x:A. !y s. x IN (y INSERT s) <=> (x = y) \/ x IN s`,
  ONCE_REWRITE_TAC[DISJ_SYM] THEN REWRITE_TAC[IN_ELIM_THM; INSERT]);;

export_namedthm IN_INSERT "IN_INSERT";;

let IN_DELETE = prove 
 (`!s. !x:A. !y. x IN (s DELETE y) <=> x IN s /\ ~(x = y)`,
  REWRITE_TAC[IN_ELIM_THM; DELETE]);;

export_namedthm IN_DELETE "IN_DELETE";;

let IN_SING = prove 
 (`!x y. x IN {y:A} <=> (x = y)`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]);;

export_namedthm IN_SING "IN_SING";;

let IN_IMAGE = prove 
 (`!y:B. !s f. (y IN (IMAGE f s)) <=> ?x:A. (y = f x) /\ x IN s`,
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[IN_ELIM_THM; IMAGE]);;

export_namedthm IN_IMAGE "IN_IMAGE";;

let IN_REST = prove 
 (`!x:A. !s. x IN (REST s) <=> x IN s /\ ~(x = CHOICE s)`,
  REWRITE_TAC[REST; IN_DELETE]);;

export_namedthm IN_REST "IN_REST";;

let FORALL_IN_INSERT = prove 
 (`!P a s. (!x. x IN (a INSERT s) ==> P x) <=> P a /\ (!x. x IN s ==> P x)`,
  REWRITE_TAC[IN_INSERT] THEN MESON_TAC[]);;

export_namedthm FORALL_IN_INSERT "FORALL_IN_INSERT";;

let EXISTS_IN_INSERT = prove 
 (`!P a s. (?x. x IN (a INSERT s) /\ P x) <=> P a \/ ?x. x IN s /\ P x`,
  REWRITE_TAC[IN_INSERT] THEN MESON_TAC[]);;

export_namedthm EXISTS_IN_INSERT "EXISTS_IN_INSERT";;

let FORALL_IN_UNION = prove 
 (`!P s t:A->bool.
        (!x. x IN s UNION t ==> P x) <=>
        (!x. x IN s ==> P x) /\ (!x. x IN t ==> P x)`,
  REWRITE_TAC[IN_UNION] THEN MESON_TAC[]);;

export_namedthm FORALL_IN_UNION "FORALL_IN_UNION";;

let EXISTS_IN_UNION = prove 
 (`!P s t:A->bool.
        (?x. x IN s UNION t /\ P x) <=>
        (?x. x IN s /\ P x) \/ (?x. x IN t /\ P x)`,
  REWRITE_TAC[IN_UNION] THEN MESON_TAC[]);;

export_namedthm EXISTS_IN_UNION "EXISTS_IN_UNION";;

(* ------------------------------------------------------------------------- *)
(* Basic property of the choice function.                                    *)
(* ------------------------------------------------------------------------- *)

let CHOICE_DEF = prove 
 (`!s:A->bool. ~(s = EMPTY) ==> (CHOICE s) IN s`,
  REWRITE_TAC[CHOICE; EXTENSION; NOT_IN_EMPTY; NOT_FORALL_THM; EXISTS_THM]);;

export_namedthm CHOICE_DEF "CHOICE_DEF";;

(* ------------------------------------------------------------------------- *)
(* Tactic to automate some routine set theory by reduction to FOL.           *)
(* ------------------------------------------------------------------------- *)

let SET_TAC =
  let PRESET_TAC =
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[EXTENSION; SUBSET; PSUBSET; DISJOINT; SING] THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_UNIV; IN_UNION; IN_INTER; IN_DIFF; IN_INSERT;
                IN_DELETE; IN_REST; IN_INTERS; IN_UNIONS; IN_IMAGE;
                IN_ELIM_THM; IN] in
  fun ths ->
    (if ths = [] then ALL_TAC else MP_TAC(end_itlist CONJ ths)) THEN
    PRESET_TAC THEN
    MESON_TAC[];;

let SET_RULE tm = prove (tm,SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Misc. theorems.                                                           *)
(* ------------------------------------------------------------------------- *)

export_theory "set-misc";;

let NOT_EQUAL_SETS = prove 
 (`!s:A->bool. !t. ~(s = t) <=> ?x. x IN t <=> ~(x IN s)`,
  SET_TAC[]);;

export_namedthm NOT_EQUAL_SETS "NOT_EQUAL_SETS";;

(* ------------------------------------------------------------------------- *)
(* The empty set.                                                            *)
(* ------------------------------------------------------------------------- *)

let MEMBER_NOT_EMPTY = prove 
 (`!s:A->bool. (?x. x IN s) <=> ~(s = EMPTY)`,
  SET_TAC[]);;

export_namedthm MEMBER_NOT_EMPTY "MEMBER_NOT_EMPTY";;

(* ------------------------------------------------------------------------- *)
(* The universal set.                                                        *)
(* ------------------------------------------------------------------------- *)

let UNIV_NOT_EMPTY = prove 
 (`~(UNIV:A->bool = EMPTY)`,
  SET_TAC[]);;

export_namedthm UNIV_NOT_EMPTY "UNIV_NOT_EMPTY";;

let EMPTY_NOT_UNIV = prove 
 (`~(EMPTY:A->bool = UNIV)`,
  SET_TAC[]);;

export_namedthm EMPTY_NOT_UNIV "EMPTY_NOT_UNIV";;

let EQ_UNIV = prove 
 (`(!x:A. x IN s) <=> (s = UNIV)`,
  SET_TAC[]);;

export_namedthm EQ_UNIV "EQ_UNIV";;

(* ------------------------------------------------------------------------- *)
(* Set inclusion.                                                            *)
(* ------------------------------------------------------------------------- *)

export_theory "set-inclusion";;

let SUBSET_TRANS = prove 
 (`!(s:A->bool) t u. s SUBSET t /\ t SUBSET u ==> s SUBSET u`,
  SET_TAC[]);;

export_namedthm SUBSET_TRANS "SUBSET_TRANS";;

let SUBSET_REFL = prove 
 (`!s:A->bool. s SUBSET s`,
  SET_TAC[]);;

export_namedthm SUBSET_REFL "SUBSET_REFL";;

let SUBSET_ANTISYM = prove 
 (`!(s:A->bool) t. s SUBSET t /\ t SUBSET s ==> s = t`,
  SET_TAC[]);;

export_namedthm SUBSET_ANTISYM "SUBSET_ANTISYM";;

let SUBSET_ANTISYM_EQ = prove 
 (`!(s:A->bool) t. s SUBSET t /\ t SUBSET s <=> s = t`,
  SET_TAC[]);;

export_namedthm SUBSET_ANTISYM_EQ "SUBSET_ANTISYM_EQ";;

let EMPTY_SUBSET = prove 
 (`!s:A->bool. EMPTY SUBSET s`,
  SET_TAC[]);;

export_namedthm EMPTY_SUBSET "EMPTY_SUBSET";;

let SUBSET_EMPTY = prove 
 (`!s:A->bool. s SUBSET EMPTY <=> (s = EMPTY)`,
  SET_TAC[]);;

export_namedthm SUBSET_EMPTY "SUBSET_EMPTY";;

let SUBSET_UNIV = prove 
 (`!s:A->bool. s SUBSET UNIV`,
  SET_TAC[]);;

export_namedthm SUBSET_UNIV "SUBSET_UNIV";;

let UNIV_SUBSET = prove 
 (`!s:A->bool. UNIV SUBSET s <=> (s = UNIV)`,
  SET_TAC[]);;

export_namedthm UNIV_SUBSET "UNIV_SUBSET";;

let SING_SUBSET = prove 
 (`!s x. {x} SUBSET s <=> x IN s`,
  SET_TAC[]);;

export_namedthm SING_SUBSET "SING_SUBSET";;

let SUBSET_RESTRICT = prove 
 (`!s P. {x | x IN s /\ P x} SUBSET s`,
  SIMP_TAC[SUBSET; IN_ELIM_THM]);;

export_namedthm SUBSET_RESTRICT "SUBSET_RESTRICT";;

(* ------------------------------------------------------------------------- *)
(* Proper subset.                                                            *)
(* ------------------------------------------------------------------------- *)

export_theory "set-psubset";;

let PSUBSET_TRANS = prove 
 (`!(s:A->bool) t u. s PSUBSET t /\ t PSUBSET u ==> s PSUBSET u`,
  SET_TAC[]);;

export_namedthm PSUBSET_TRANS "PSUBSET_TRANS";;

let PSUBSET_SUBSET_TRANS = prove 
 (`!(s:A->bool) t u. s PSUBSET t /\ t SUBSET u ==> s PSUBSET u`,
  SET_TAC[]);;

export_namedthm PSUBSET_SUBSET_TRANS "PSUBSET_SUBSET_TRANS";;

let SUBSET_PSUBSET_TRANS = prove 
 (`!(s:A->bool) t u. s SUBSET t /\ t PSUBSET u ==> s PSUBSET u`,
  SET_TAC[]);;

export_namedthm SUBSET_PSUBSET_TRANS "SUBSET_PSUBSET_TRANS";;

let PSUBSET_IRREFL = prove 
 (`!s:A->bool. ~(s PSUBSET s)`,
  SET_TAC[]);;

export_namedthm PSUBSET_IRREFL "PSUBSET_IRREFL";;

let NOT_PSUBSET_EMPTY = prove 
 (`!s:A->bool. ~(s PSUBSET EMPTY)`,
  SET_TAC[]);;

export_namedthm NOT_PSUBSET_EMPTY "NOT_PSUBSET_EMPTY";;

let NOT_UNIV_PSUBSET = prove 
 (`!s:A->bool. ~(UNIV PSUBSET s)`,
  SET_TAC[]);;

export_namedthm NOT_UNIV_PSUBSET "NOT_UNIV_PSUBSET";;

let PSUBSET_UNIV = prove 
 (`!s:A->bool. s PSUBSET UNIV <=> ?x. ~(x IN s)`,
  SET_TAC[]);;

export_namedthm PSUBSET_UNIV "PSUBSET_UNIV";;

let PSUBSET_ALT = prove 
 (`!s t:A->bool. s PSUBSET t <=> s SUBSET t /\ (?a. a IN t /\ ~(a IN s))`,
  REWRITE_TAC[PSUBSET] THEN SET_TAC[]);;

export_namedthm PSUBSET_ALT "PSUBSET_ALT";;

(* ------------------------------------------------------------------------- *)
(* Union.                                                                    *)
(* ------------------------------------------------------------------------- *)

export_theory "set-union";;

let UNION_ASSOC = prove 
 (`!(s:A->bool) t u. (s UNION t) UNION u = s UNION (t UNION u)`,
  SET_TAC[]);;

export_namedthm UNION_ASSOC "UNION_ASSOC";;

let UNION_IDEMPOT = prove 
 (`!s:A->bool. s UNION s = s`,
  SET_TAC[]);;

export_namedthm UNION_IDEMPOT "UNION_IDEMPOT";;

let UNION_COMM = prove 
 (`!(s:A->bool) t. s UNION t = t UNION s`,
  SET_TAC[]);;

export_namedthm UNION_COMM "UNION_COMM";;

let SUBSET_UNION = prove 
 (`(!s:A->bool. !t. s SUBSET (s UNION t)) /\
   (!s:A->bool. !t. s SUBSET (t UNION s))`,
  SET_TAC[]);;

export_namedthm SUBSET_UNION "SUBSET_UNION";;

let SUBSET_UNION_ABSORPTION = prove 
 (`!s:A->bool. !t. s SUBSET t <=> (s UNION t = t)`,
  SET_TAC[]);;

export_namedthm SUBSET_UNION_ABSORPTION "SUBSET_UNION_ABSORPTION";;

let UNION_EMPTY = prove 
 (`(!s:A->bool. EMPTY UNION s = s) /\
   (!s:A->bool. s UNION EMPTY = s)`,
  SET_TAC[]);;

export_namedthm UNION_EMPTY "UNION_EMPTY";;

let UNION_UNIV = prove 
 (`(!s:A->bool. UNIV UNION s = UNIV) /\
   (!s:A->bool. s UNION UNIV = UNIV)`,
  SET_TAC[]);;

export_namedthm UNION_UNIV "UNION_UNIV";;

let EMPTY_UNION = prove 
 (`!s:A->bool. !t. (s UNION t = EMPTY) <=> (s = EMPTY) /\ (t = EMPTY)`,
  SET_TAC[]);;

export_namedthm EMPTY_UNION "EMPTY_UNION";;

let UNION_SUBSET = prove 
 (`!s t u. (s UNION t) SUBSET u <=> s SUBSET u /\ t SUBSET u`,
  SET_TAC[]);;

export_namedthm UNION_SUBSET "UNION_SUBSET";;

let FORALL_SUBSET_UNION = prove 
 (`!t u:A->bool.
        (!s. s SUBSET t UNION u ==> P s) <=>
        (!t' u'. t' SUBSET t /\ u' SUBSET u ==> P(t' UNION u'))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    DISCH_TAC THEN X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`s INTER t:A->bool`; `s INTER u:A->bool`]) THEN
    ANTS_TAC THENL [ALL_TAC; MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC] THEN
    ASM SET_TAC[]]);;

export_namedthm FORALL_SUBSET_UNION "FORALL_SUBSET_UNION";;

let EXISTS_SUBSET_UNION = prove 
 (`!t u:A->bool.
        (?s. s SUBSET t UNION u /\ P s) <=>
        (?t' u'. t' SUBSET t /\ u' SUBSET u /\ P(t' UNION u'))`,
  REWRITE_TAC[MESON[] `(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)`] THEN
  REWRITE_TAC[FORALL_SUBSET_UNION] THEN MESON_TAC[]);;

export_namedthm EXISTS_SUBSET_UNION "EXISTS_SUBSET_UNION";;

let FORALL_SUBSET_INSERT = prove 
 (`!a:A t. (!s. s SUBSET a INSERT t ==> P s) <=>
           (!s. s SUBSET t ==> P s /\ P (a INSERT s))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  REWRITE_TAC[FORALL_SUBSET_UNION; SET_RULE
   `s SUBSET {a} <=> s = {} \/ s = {a}`] THEN
  MESON_TAC[UNION_EMPTY]);;

export_namedthm FORALL_SUBSET_INSERT "FORALL_SUBSET_INSERT";;

let EXISTS_SUBSET_INSERT = prove 
 (`!a:A t. (?s. s SUBSET a INSERT t /\ P s) <=>
           (?s. s SUBSET t /\ (P s \/ P (a INSERT s)))`,
  REWRITE_TAC[MESON[] `(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)`] THEN
  REWRITE_TAC[FORALL_SUBSET_INSERT] THEN MESON_TAC[]);;

export_namedthm EXISTS_SUBSET_INSERT "EXISTS_SUBSET_INSERT";;

(* ------------------------------------------------------------------------- *)
(* Intersection.                                                             *)
(* ------------------------------------------------------------------------- *)

export_theory "set-intersection";;

let INTER_ASSOC = prove 
 (`!(s:A->bool) t u. (s INTER t) INTER u = s INTER (t INTER u)`,
  SET_TAC[]);;

export_namedthm INTER_ASSOC "INTER_ASSOC";;

let INTER_IDEMPOT = prove 
 (`!s:A->bool. s INTER s = s`,
  SET_TAC[]);;

export_namedthm INTER_IDEMPOT "INTER_IDEMPOT";;

let INTER_COMM = prove 
 (`!(s:A->bool) t. s INTER t = t INTER s`,
  SET_TAC[]);;

export_namedthm INTER_COMM "INTER_COMM";;

let INTER_SUBSET = prove 
 (`(!s:A->bool. !t. (s INTER t) SUBSET s) /\
   (!s:A->bool. !t. (t INTER s) SUBSET s)`,
  SET_TAC[]);;

export_namedthm INTER_SUBSET "INTER_SUBSET";;

let SUBSET_INTER_ABSORPTION = prove 
 (`!s:A->bool. !t. s SUBSET t <=> (s INTER t = s)`,
  SET_TAC[]);;

export_namedthm SUBSET_INTER_ABSORPTION "SUBSET_INTER_ABSORPTION";;

let INTER_EMPTY = prove 
 (`(!s:A->bool. EMPTY INTER s = EMPTY) /\
   (!s:A->bool. s INTER EMPTY = EMPTY)`,
  SET_TAC[]);;

export_namedthm INTER_EMPTY "INTER_EMPTY";;

let INTER_UNIV = prove 
 (`(!s:A->bool. UNIV INTER s = s) /\
   (!s:A->bool. s INTER UNIV = s)`,
  SET_TAC[]);;

export_namedthm INTER_UNIV "INTER_UNIV";;

let SUBSET_INTER = prove 
 (`!s t u. s SUBSET (t INTER u) <=> s SUBSET t /\ s SUBSET u`,
  SET_TAC[]);;

export_namedthm SUBSET_INTER "SUBSET_INTER";;

(* ------------------------------------------------------------------------- *)
(* Distributivity.                                                           *)
(* ------------------------------------------------------------------------- *)

export_theory "set-distrib";;

let UNION_OVER_INTER = prove 
 (`!s:A->bool. !t u. s INTER (t UNION u) = (s INTER t) UNION (s INTER u)`,
  SET_TAC[]);;

export_namedthm UNION_OVER_INTER "UNION_OVER_INTER";;

let INTER_OVER_UNION = prove 
 (`!s:A->bool. !t u. s UNION (t INTER u) = (s UNION t) INTER (s UNION u)`,
  SET_TAC[]);;

export_namedthm INTER_OVER_UNION "INTER_OVER_UNION";;

(* ------------------------------------------------------------------------- *)
(* Disjoint sets.                                                            *)
(* ------------------------------------------------------------------------- *)

export_theory "set-disjoint";;

let IN_DISJOINT = prove 
 (`!s:A->bool. !t. DISJOINT s t <=> ~(?x. x IN s /\ x IN t)`,
  SET_TAC[]);;

export_namedthm IN_DISJOINT "IN_DISJOINT";;

let DISJOINT_SYM = prove 
 (`!s:A->bool. !t. DISJOINT s t <=> DISJOINT t s`,
  SET_TAC[]);;

export_namedthm DISJOINT_SYM "DISJOINT_SYM";;

let DISJOINT_EMPTY = prove 
 (`!s:A->bool. DISJOINT EMPTY s /\ DISJOINT s EMPTY`,
  SET_TAC[]);;

export_namedthm DISJOINT_EMPTY "DISJOINT_EMPTY";;

let DISJOINT_EMPTY_REFL = prove 
 (`!s:A->bool. (s = EMPTY) <=> (DISJOINT s s)`,
  SET_TAC[]);;

export_namedthm DISJOINT_EMPTY_REFL "DISJOINT_EMPTY_REFL";;

let DISJOINT_UNION = prove 
 (`!s:A->bool. !t u. DISJOINT (s UNION t) u <=> DISJOINT s u /\ DISJOINT t u`,
  SET_TAC[]);;

export_namedthm DISJOINT_UNION "DISJOINT_UNION";;

(* ------------------------------------------------------------------------- *)
(* Set difference.                                                           *)
(* ------------------------------------------------------------------------- *)

export_theory "set-difference";;

let DIFF_EMPTY = prove 
 (`!s:A->bool. s DIFF EMPTY = s`,
  SET_TAC[]);;

export_namedthm DIFF_EMPTY "DIFF_EMPTY";;

let EMPTY_DIFF = prove 
 (`!s:A->bool. EMPTY DIFF s = EMPTY`,
  SET_TAC[]);;

export_namedthm EMPTY_DIFF "EMPTY_DIFF";;

let DIFF_UNIV = prove 
 (`!s:A->bool. s DIFF UNIV = EMPTY`,
  SET_TAC[]);;

export_namedthm DIFF_UNIV "DIFF_UNIV";;

let DIFF_DIFF = prove 
 (`!s:A->bool. !t. (s DIFF t) DIFF t = s DIFF t`,
  SET_TAC[]);;

export_namedthm DIFF_DIFF "DIFF_DIFF";;

let DIFF_EQ_EMPTY = prove 
 (`!s:A->bool. s DIFF s = EMPTY`,
  SET_TAC[]);;

export_namedthm DIFF_EQ_EMPTY "DIFF_EQ_EMPTY";;

let SUBSET_DIFF = prove 
 (`!s t. (s DIFF t) SUBSET s`,
  SET_TAC[]);;

export_namedthm SUBSET_DIFF "SUBSET_DIFF";;

let COMPL_COMPL = prove 
 (`!s. (:A) DIFF ((:A) DIFF s) = s`,
  SET_TAC[]);;

export_namedthm COMPL_COMPL "COMPL_COMPL";;

(* ------------------------------------------------------------------------- *)
(* Insertion and deletion.                                                   *)
(* ------------------------------------------------------------------------- *)

export_theory "set-insert-delete";;

let COMPONENT = prove 
 (`!x:A. !s. x IN (x INSERT s)`,
  SET_TAC[]);;

export_namedthm COMPONENT "COMPONENT";;

let DECOMPOSITION = prove 
 (`!s:A->bool. !x. x IN s <=> ?t. (s = x INSERT t) /\ ~(x IN t)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN EXISTS_TAC `s DELETE x:A` THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

export_namedthm DECOMPOSITION "DECOMPOSITION";;

let SET_CASES = prove 
 (`!s:A->bool. (s = EMPTY) \/ ?x:A. ?t. (s = x INSERT t) /\ ~(x IN t)`,
  MESON_TAC[MEMBER_NOT_EMPTY; DECOMPOSITION]);;

export_namedthm SET_CASES "SET_CASES";;

let ABSORPTION = prove 
 (`!x:A. !s. x IN s <=> (x INSERT s = s)`,
  SET_TAC[]);;

export_namedthm ABSORPTION "ABSORPTION";;

let INSERT_INSERT = prove 
 (`!x:A. !s. x INSERT (x INSERT s) = x INSERT s`,
  SET_TAC[]);;

export_namedthm INSERT_INSERT "INSERT_INSERT";;

let INSERT_COMM = prove 
 (`!x:A. !y s. x INSERT (y INSERT s) = y INSERT (x INSERT s)`,
  SET_TAC[]);;

export_namedthm INSERT_COMM "INSERT_COMM";;

let INSERT_UNIV = prove 
 (`!x:A. x INSERT UNIV = UNIV`,
  SET_TAC[]);;

export_namedthm INSERT_UNIV "INSERT_UNIV";;

let NOT_INSERT_EMPTY = prove 
 (`!x:A. !s. ~(x INSERT s = EMPTY)`,
  SET_TAC[]);;

export_namedthm NOT_INSERT_EMPTY "NOT_INSERT_EMPTY";;

let NOT_EMPTY_INSERT = prove 
 (`!x:A. !s. ~(EMPTY = x INSERT s)`,
  SET_TAC[]);;

export_namedthm NOT_EMPTY_INSERT "NOT_EMPTY_INSERT";;

let INSERT_UNION = prove 
 (`!x:A. !s t. (x INSERT s) UNION t =
               if x IN t then s UNION t else x INSERT (s UNION t)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

export_namedthm INSERT_UNION "INSERT_UNION";;

let INSERT_UNION_EQ = prove 
 (`!x:A. !s t. (x INSERT s) UNION t = x INSERT (s UNION t)`,
  SET_TAC[]);;

export_namedthm INSERT_UNION_EQ "INSERT_UNION_EQ";;

let INSERT_INTER = prove 
 (`!x:A. !s t. (x INSERT s) INTER t =
               if x IN t then x INSERT (s INTER t) else s INTER t`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

export_namedthm INSERT_INTER "INSERT_INTER";;

let DISJOINT_INSERT = prove 
 (`!(x:A) s t. DISJOINT (x INSERT s) t <=> (DISJOINT s t) /\ ~(x IN t)`,
  SET_TAC[]);;

export_namedthm DISJOINT_INSERT "DISJOINT_INSERT";;

let INSERT_SUBSET = prove 
 (`!x:A. !s t. (x INSERT s) SUBSET t <=> (x IN t /\ s SUBSET t)`,
  SET_TAC[]);;

export_namedthm INSERT_SUBSET "INSERT_SUBSET";;

let SUBSET_INSERT = prove 
 (`!x:A. !s. ~(x IN s) ==> !t. s SUBSET (x INSERT t) <=> s SUBSET t`,
  SET_TAC[]);;

export_namedthm SUBSET_INSERT "SUBSET_INSERT";;

let INSERT_DIFF = prove 
 (`!s t. !x:A. (x INSERT s) DIFF t =
               if x IN t then s DIFF t else x INSERT (s DIFF t)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

export_namedthm INSERT_DIFF "INSERT_DIFF";;

let INSERT_AC = prove 
 (`(x INSERT (y INSERT s) = y INSERT (x INSERT s)) /\
   (x INSERT (x INSERT s) = x INSERT s)`,
  REWRITE_TAC[INSERT_COMM; INSERT_INSERT]);;

export_namedthm INSERT_AC "INSERT_AC";;

let INTER_ACI = prove 
 (`(p INTER q = q INTER p) /\
   ((p INTER q) INTER r = p INTER q INTER r) /\
   (p INTER q INTER r = q INTER p INTER r) /\
   (p INTER p = p) /\
   (p INTER p INTER q = p INTER q)`,
  SET_TAC[]);;

export_namedthm INTER_ACI "INTER_ACI";;

let UNION_ACI = prove 
 (`(p UNION q = q UNION p) /\
   ((p UNION q) UNION r = p UNION q UNION r) /\
   (p UNION q UNION r = q UNION p UNION r) /\
   (p UNION p = p) /\
   (p UNION p UNION q = p UNION q)`,
  SET_TAC[]);;

export_namedthm UNION_ACI "UNION_ACI";;

let DELETE_NON_ELEMENT = prove 
 (`!x:A. !s. ~(x IN s) <=> (s DELETE x = s)`,
  SET_TAC[]);;

export_namedthm DELETE_NON_ELEMENT "DELETE_NON_ELEMENT";;

let IN_DELETE_EQ = prove 
 (`!s x. !x':A.
     (x IN s <=> x' IN s) <=> (x IN (s DELETE x') <=> x' IN (s DELETE x))`,
  SET_TAC[]);;

export_namedthm IN_DELETE_EQ "IN_DELETE_EQ";;

let EMPTY_DELETE = prove 
 (`!x:A. EMPTY DELETE x = EMPTY`,
  SET_TAC[]);;

export_namedthm EMPTY_DELETE "EMPTY_DELETE";;

let DELETE_DELETE = prove 
 (`!x:A. !s. (s DELETE x) DELETE x = s DELETE x`,
  SET_TAC[]);;

export_namedthm DELETE_DELETE "DELETE_DELETE";;

let DELETE_COMM = prove 
 (`!x:A. !y. !s. (s DELETE x) DELETE y = (s DELETE y) DELETE x`,
  SET_TAC[]);;

export_namedthm DELETE_COMM "DELETE_COMM";;

let DELETE_SUBSET = prove 
 (`!x:A. !s. (s DELETE x) SUBSET s`,
  SET_TAC[]);;

export_namedthm DELETE_SUBSET "DELETE_SUBSET";;

let SUBSET_DELETE = prove 
 (`!x:A. !s t. s SUBSET (t DELETE x) <=> ~(x IN s) /\ (s SUBSET t)`,
  SET_TAC[]);;

export_namedthm SUBSET_DELETE "SUBSET_DELETE";;

let SUBSET_INSERT_DELETE = prove 
 (`!x:A. !s t. s SUBSET (x INSERT t) <=> ((s DELETE x) SUBSET t)`,
  SET_TAC[]);;

export_namedthm SUBSET_INSERT_DELETE "SUBSET_INSERT_DELETE";;

let DIFF_INSERT = prove 
 (`!s t. !x:A. s DIFF (x INSERT t) = (s DELETE x) DIFF t`,
  SET_TAC[]);;

export_namedthm DIFF_INSERT "DIFF_INSERT";;

let PSUBSET_INSERT_SUBSET = prove 
 (`!s t. s PSUBSET t <=> ?x:A. ~(x IN s) /\ (x INSERT s) SUBSET t`,
  SET_TAC[]);;

export_namedthm PSUBSET_INSERT_SUBSET "PSUBSET_INSERT_SUBSET";;

let DELETE_INSERT = prove 
 (`!x:A. !y s.
      (x INSERT s) DELETE y =
        if x = y then s DELETE y else x INSERT (s DELETE y)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

export_namedthm DELETE_INSERT "DELETE_INSERT";;

let INSERT_DELETE = prove 
 (`!x:A. !s. x IN s ==> (x INSERT (s DELETE x) = s)`,
  SET_TAC[]);;

export_namedthm INSERT_DELETE "INSERT_DELETE";;

let DELETE_INTER = prove 
 (`!s t. !x:A. (s DELETE x) INTER t = (s INTER t) DELETE x`,
  SET_TAC[]);;

export_namedthm DELETE_INTER "DELETE_INTER";;

let DISJOINT_DELETE_SYM = prove 
 (`!s t. !x:A. DISJOINT (s DELETE x) t = DISJOINT (t DELETE x) s`,
  SET_TAC[]);;

export_namedthm DISJOINT_DELETE_SYM "DISJOINT_DELETE_SYM";;

(* ------------------------------------------------------------------------- *)
(* Multiple union.                                                           *)
(* ------------------------------------------------------------------------- *)

export_theory "set-unions";;

let UNIONS_0 = prove 
 (`UNIONS {} = {}`,
  SET_TAC[]);;

export_namedthm UNIONS_0 "UNIONS_0";;

let UNIONS_1 = prove 
 (`UNIONS {s} = s`,
  SET_TAC[]);;

export_namedthm UNIONS_1 "UNIONS_1";;

let UNIONS_2 = prove 
 (`UNIONS {s,t} = s UNION t`,
  SET_TAC[]);;

export_namedthm UNIONS_2 "UNIONS_2";;

let UNIONS_INSERT = prove 
 (`UNIONS (s INSERT u) = s UNION (UNIONS u)`,
  SET_TAC[]);;

export_namedthm UNIONS_INSERT "UNIONS_INSERT";;

let FORALL_IN_UNIONS = prove 
 (`!P s. (!x. x IN UNIONS s ==> P x) <=> !t x. t IN s /\ x IN t ==> P x`,
  SET_TAC[]);;

export_namedthm FORALL_IN_UNIONS "FORALL_IN_UNIONS";;

let EXISTS_IN_UNIONS = prove 
 (`!P s. (?x. x IN UNIONS s /\ P x) <=> (?t x. t IN s /\ x IN t /\ P x)`,
  SET_TAC[]);;

export_namedthm EXISTS_IN_UNIONS "EXISTS_IN_UNIONS";;

let EMPTY_UNIONS = prove 
 (`!s. (UNIONS s = {}) <=> !t. t IN s ==> t = {}`,
  SET_TAC[]);;

export_namedthm EMPTY_UNIONS "EMPTY_UNIONS";;

let INTER_UNIONS = prove 
 (`(!s t. UNIONS s INTER t = UNIONS {x INTER t | x IN s}) /\
   (!s t. t INTER UNIONS s = UNIONS {t INTER x | x IN s})`,
  ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN
  MESON_TAC[IN_INTER]);;

export_namedthm INTER_UNIONS "INTER_UNIONS";;

let UNIONS_SUBSET = prove 
 (`!f t. UNIONS f SUBSET t <=> !s. s IN f ==> s SUBSET t`,
  SET_TAC[]);;

export_namedthm UNIONS_SUBSET "UNIONS_SUBSET";;

let SUBSET_UNIONS = prove 
 (`!f g. f SUBSET g ==> UNIONS f SUBSET UNIONS g`,
  SET_TAC[]);;

export_namedthm SUBSET_UNIONS "SUBSET_UNIONS";;

let UNIONS_UNION = prove 
 (`!s t. UNIONS(s UNION t) = (UNIONS s) UNION (UNIONS t)`,
  SET_TAC[]);;

export_namedthm UNIONS_UNION "UNIONS_UNION";;

let INTERS_UNION = prove 
 (`!s t. INTERS (s UNION t) = INTERS s INTER INTERS t`,
  SET_TAC[]);;

export_namedthm INTERS_UNION "INTERS_UNION";;

let UNIONS_MONO = prove 
 (`(!x. x IN s ==> ?y. y IN t /\ x SUBSET y) ==> UNIONS s SUBSET UNIONS t`,
  SET_TAC[]);;

export_namedthm UNIONS_MONO "UNIONS_MONO";;

let UNIONS_MONO_IMAGE = prove 
 (`(!x. x IN s ==> f x SUBSET g x)
   ==> UNIONS(IMAGE f s) SUBSET UNIONS(IMAGE g s)`,
  SET_TAC[]);;

export_namedthm UNIONS_MONO_IMAGE "UNIONS_MONO_IMAGE";;

let UNIONS_UNIV = prove 
 (`UNIONS (:A->bool) = (:A)`,
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNIV] THEN
  MESON_TAC[IN_SING]);;

export_namedthm UNIONS_UNIV "UNIONS_UNIV";;

let UNIONS_INSERT_EMPTY = prove 
 (`!s. UNIONS({} INSERT s) = UNIONS s`,
  ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_INSERT] THEN MESON_TAC[NOT_IN_EMPTY]);;

export_namedthm UNIONS_INSERT_EMPTY "UNIONS_INSERT_EMPTY";;

let UNIONS_DELETE_EMPTY = prove 
 (`!s. UNIONS(s DELETE {}) = UNIONS s`,
  ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN MESON_TAC[NOT_IN_EMPTY]);;

export_namedthm UNIONS_DELETE_EMPTY "UNIONS_DELETE_EMPTY";;

(* ------------------------------------------------------------------------- *)
(* Multiple intersection.                                                    *)
(* ------------------------------------------------------------------------- *)

export_theory "set-inters";;

let INTERS_0 = prove 
 (`INTERS {} = (:A)`,
  SET_TAC[]);;

export_namedthm INTERS_0 "INTERS_0";;

let INTERS_1 = prove 
 (`INTERS {s} = s`,
  SET_TAC[]);;

export_namedthm INTERS_1 "INTERS_1";;

let INTERS_2 = prove 
 (`INTERS {s,t} = s INTER t`,
  SET_TAC[]);;

export_namedthm INTERS_2 "INTERS_2";;

let INTERS_INSERT = prove 
 (`INTERS (s INSERT u) = s INTER (INTERS u)`,
  SET_TAC[]);;

export_namedthm INTERS_INSERT "INTERS_INSERT";;

let SUBSET_INTERS = prove 
 (`!s f. s SUBSET INTERS f <=> (!t. t IN f ==> s SUBSET t)`,
  SET_TAC[]);;

export_namedthm SUBSET_INTERS "SUBSET_INTERS";;

let INTERS_SUBSET = prove 
 (`!u s:A->bool.
    ~(u = {}) /\ (!t. t IN u ==> t SUBSET s) ==> INTERS u SUBSET s`,
  SET_TAC[]);;

export_namedthm INTERS_SUBSET "INTERS_SUBSET";;

let INTERS_SUBSET_STRONG = prove 
 (`!u s:A->bool. (?t. t IN u /\ t SUBSET s) ==> INTERS u SUBSET s`,
  SET_TAC[]);;

export_namedthm INTERS_SUBSET_STRONG "INTERS_SUBSET_STRONG";;

let INTERS_ANTIMONO = prove 
 (`!f g. g SUBSET f ==> INTERS f SUBSET INTERS g`,
  SET_TAC[]);;

export_namedthm INTERS_ANTIMONO "INTERS_ANTIMONO";;

let INTERS_EQ_UNIV = prove 
 (`!f. INTERS f = (:A) <=> !s. s IN f ==> s = (:A)`,
  SET_TAC[]);;

export_namedthm INTERS_EQ_UNIV "INTERS_EQ_UNIV";;

let INTERS_ANTIMONO_GEN = prove 
 (`!s t. (!y. y IN t ==> ?x. x IN s /\ x SUBSET y)
         ==> INTERS s SUBSET INTERS t`,
  SET_TAC[]);;

export_namedthm INTERS_ANTIMONO_GEN "INTERS_ANTIMONO_GEN";;

(* ------------------------------------------------------------------------- *)
(* Image.                                                                    *)
(* ------------------------------------------------------------------------- *)

export_theory "set-image";;

let IMAGE_CLAUSES = prove 
 (`(IMAGE f {} = {}) /\
   (IMAGE f (x INSERT s) = (f x) INSERT (IMAGE f s))`,
  REWRITE_TAC[IMAGE; IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT; EXTENSION] THEN
  MESON_TAC[]);;

export_namedthm IMAGE_CLAUSES "IMAGE_CLAUSES";;

let IMAGE_UNION = prove 
 (`!f s t. IMAGE f (s UNION t) = (IMAGE f s) UNION (IMAGE f t)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNION] THEN MESON_TAC[]);;

export_namedthm IMAGE_UNION "IMAGE_UNION";;

let IMAGE_ID = prove 
 (`!s. IMAGE (\x. x) s = s`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; UNWIND_THM1]);;

export_namedthm IMAGE_ID "IMAGE_ID";;

let IMAGE_I = prove 
 (`!s. IMAGE I s = s`,
  REWRITE_TAC[I_DEF; IMAGE_ID]);;

export_namedthm IMAGE_I "IMAGE_I";;

let IMAGE_o = prove 
 (`!f g s. IMAGE (f o g) s = IMAGE f (IMAGE g s)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN MESON_TAC[]);;

export_namedthm IMAGE_o "IMAGE_o";;

let IMAGE_SUBSET = prove 
 (`!f s t. s SUBSET t ==> (IMAGE f s) SUBSET (IMAGE f t)`,
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[]);;

export_namedthm IMAGE_SUBSET "IMAGE_SUBSET";;

let IMAGE_INTER_INJ = prove 
 (`!f s t. (!x y. (f(x) = f(y)) ==> (x = y))
           ==> (IMAGE f (s INTER t) = (IMAGE f s) INTER (IMAGE f t))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN MESON_TAC[]);;

export_namedthm IMAGE_INTER_INJ "IMAGE_INTER_INJ";;

let IMAGE_DIFF_INJ = prove 
 (`!f:A->B s t.
        (!x y. x IN s /\ y IN t /\ f x = f y ==> x = y)
        ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t`,
  SET_TAC[]);;

export_namedthm IMAGE_DIFF_INJ "IMAGE_DIFF_INJ";;

let IMAGE_DIFF_INJ_ALT = prove 
 (`!f:A->B s t.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\ t SUBSET s
        ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t`,
  SET_TAC[]);;

export_namedthm IMAGE_DIFF_INJ_ALT "IMAGE_DIFF_INJ_ALT";;

let IMAGE_DELETE_INJ = prove 
 (`!f:A->B s a.
        (!x. x IN s /\ f x = f a ==> x = a)
        ==> IMAGE f (s DELETE a) = IMAGE f s DELETE f a`,
  SET_TAC[]);;

export_namedthm IMAGE_DELETE_INJ "IMAGE_DELETE_INJ";;

let IMAGE_DELETE_INJ_ALT = prove 
 (`!f:A->B s a.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\ a IN s
        ==> IMAGE f (s DELETE a) = IMAGE f s DELETE f a`,
  SET_TAC[]);;

export_namedthm IMAGE_DELETE_INJ_ALT "IMAGE_DELETE_INJ_ALT";;

let IMAGE_EQ_EMPTY = prove 
 (`!f s. (IMAGE f s = {}) <=> (s = {})`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_IMAGE] THEN MESON_TAC[]);;

export_namedthm IMAGE_EQ_EMPTY "IMAGE_EQ_EMPTY";;

let FORALL_IN_IMAGE = prove 
 (`!f s. (!y. y IN IMAGE f s ==> P y) <=> (!x. x IN s ==> P(f x))`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

export_namedthm FORALL_IN_IMAGE "FORALL_IN_IMAGE";;

let EXISTS_IN_IMAGE = prove 
 (`!f s. (?y. y IN IMAGE f s /\ P y) <=> ?x. x IN s /\ P(f x)`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

export_namedthm EXISTS_IN_IMAGE "EXISTS_IN_IMAGE";;

let FORALL_IN_IMAGE_2 = prove 
 (`!f P s. (!x y. x IN IMAGE f s /\ y IN IMAGE f s ==> P x y) <=>
           (!x y. x IN s /\ y IN s ==> P (f x) (f y))`,
  SET_TAC[]);;

export_namedthm FORALL_IN_IMAGE_2 "FORALL_IN_IMAGE_2";;

let IMAGE_CONST = prove 
 (`!s c. IMAGE (\x. c) s = if s = {} then {} else {c}`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SING] THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY]);;

export_namedthm IMAGE_CONST "IMAGE_CONST";;

let SIMPLE_IMAGE = prove 
 (`!f s. {f x | x IN s} = IMAGE f s`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[]);;

export_namedthm SIMPLE_IMAGE "SIMPLE_IMAGE";;

let SIMPLE_IMAGE_GEN = prove 
 (`!f P. {f x | P x} = IMAGE f {x | P x}`,
  SET_TAC[]);;

export_namedthm SIMPLE_IMAGE_GEN "SIMPLE_IMAGE_GEN";;

let IMAGE_UNIONS = prove 
 (`!f s. IMAGE f (UNIONS s) = UNIONS (IMAGE (IMAGE f) s)`,
  ONCE_REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2; IN_IMAGE] THEN
  MESON_TAC[]);;

export_namedthm IMAGE_UNIONS "IMAGE_UNIONS";;

let FUN_IN_IMAGE = prove 
 (`!f s x. x IN s ==> f(x) IN IMAGE f s`,
  SET_TAC[]);;

export_namedthm FUN_IN_IMAGE "FUN_IN_IMAGE";;

let SURJECTIVE_IMAGE_EQ = prove 
 (`!s t. (!y. y IN t ==> ?x. f x = y) /\ (!x. (f x) IN t <=> x IN s)
         ==> IMAGE f s = t`,
  SET_TAC[]);;

export_namedthm SURJECTIVE_IMAGE_EQ "SURJECTIVE_IMAGE_EQ";;

(* ------------------------------------------------------------------------- *)
(* Misc lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

export_theory "set-misc";;

let EMPTY_GSPEC = prove 
 (`{x | F} = {}`,
  SET_TAC[]);;

export_namedthm EMPTY_GSPEC "EMPTY_GSPEC";;

let UNIV_GSPEC = prove 
 (`{x | T} = UNIV`,
  SET_TAC[]);;

export_namedthm UNIV_GSPEC "UNIV_GSPEC";;

let SING_GSPEC = prove 
 (`(!a. {x | x = a} = {a}) /\
   (!a. {x | a = x} = {a})`,
  SET_TAC[]);;

export_namedthm SING_GSPEC "SING_GSPEC";;

let IN_GSPEC = prove 
 (`!s:A->bool. {x | x IN s} = s`,
  SET_TAC[]);;

export_namedthm IN_GSPEC "IN_GSPEC";;

let IN_ELIM_PAIR_THM = prove 
 (`!P a b. (a,b) IN {(x,y) | P x y} <=> P a b`,
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[PAIR_EQ]);;

export_namedthm IN_ELIM_PAIR_THM "IN_ELIM_PAIR_THM";;

let SET_PAIR_THM = prove 
 (`!P. {p | P p} = {(a,b) | P(a,b)}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM; IN_ELIM_PAIR_THM]);;

export_namedthm SET_PAIR_THM "SET_PAIR_THM";;

let FORALL_IN_GSPEC = prove 
 (`(!P f. (!z. z IN {f x | P x} ==> Q z) <=> (!x. P x ==> Q(f x))) /\
   (!P f. (!z. z IN {f x y | P x y} ==> Q z) <=>
          (!x y. P x y ==> Q(f x y))) /\
   (!P f. (!z. z IN {f w x y | P w x y} ==> Q z) <=>
          (!w x y. P w x y ==> Q(f w x y))) /\
   (!P f. (!z. z IN {f v w x y | P v w x y} ==> Q z) <=>
          (!v w x y. P v w x y ==> Q(f v w x y)))`,
  SET_TAC[]);;

export_namedthm FORALL_IN_GSPEC "FORALL_IN_GSPEC";;

let EXISTS_IN_GSPEC = prove 
 (`(!P f. (?z. z IN {f x | P x} /\ Q z) <=> (?x. P x /\ Q(f x))) /\
   (!P f. (?z. z IN {f x y | P x y} /\ Q z) <=>
          (?x y. P x y /\ Q(f x y))) /\
   (!P f. (?z. z IN {f w x y | P w x y} /\ Q z) <=>
          (?w x y. P w x y /\ Q(f w x y))) /\
   (!P f. (?z. z IN {f v w x y | P v w x y} /\ Q z) <=>
          (?v w x y. P v w x y /\ Q(f v w x y)))`,
  SET_TAC[]);;

export_namedthm EXISTS_IN_GSPEC "EXISTS_IN_GSPEC";;

let SET_PROVE_CASES = prove 
 (`!P:(A->bool)->bool.
       P {} /\ (!a s. ~(a IN s) ==> P(a INSERT s))
       ==> !s. P s`,
  MESON_TAC[SET_CASES]);;

export_namedthm SET_PROVE_CASES "SET_PROVE_CASES";;

let UNIONS_IMAGE = prove 
 (`!f s. UNIONS (IMAGE f s) = {y | ?x. x IN s /\ y IN f x}`,
  REPEAT GEN_TAC THEN  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

export_namedthm UNIONS_IMAGE "UNIONS_IMAGE";;

let INTERS_IMAGE = prove 
 (`!f s. INTERS (IMAGE f s) = {y | !x. x IN s ==> y IN f x}`,
  REPEAT GEN_TAC THEN  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_INTERS; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

export_namedthm INTERS_IMAGE "INTERS_IMAGE";;

let UNIONS_GSPEC = prove 
 (`(!P f. UNIONS {f x | P x} = {a | ?x. P x /\ a IN (f x)}) /\
   (!P f. UNIONS {f x y | P x y} = {a | ?x y. P x y /\ a IN (f x y)}) /\
   (!P f. UNIONS {f x y z | P x y z} =
            {a | ?x y z. P x y z /\ a IN (f x y z)})`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

export_namedthm UNIONS_GSPEC "UNIONS_GSPEC";;

let INTERS_GSPEC = prove 
 (`(!P f. INTERS {f x | P x} = {a | !x. P x ==> a IN (f x)}) /\
   (!P f. INTERS {f x y | P x y} = {a | !x y. P x y ==> a IN (f x y)}) /\
   (!P f. INTERS {f x y z | P x y z} =
                {a | !x y z. P x y z ==> a IN (f x y z)})`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN MESON_TAC[]);;

export_namedthm INTERS_GSPEC "INTERS_GSPEC";;

let UNIONS_SINGS_GEN = prove 
 (`!P:A->bool. UNIONS {{x} | P x} = {x | P x}`,
  REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]);;

export_namedthm UNIONS_SINGS_GEN "UNIONS_SINGS_GEN";;

let UNIONS_SINGS = prove 
 (`!s:A->bool. UNIONS {{x} | x IN s} = s`,
  REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]);;

export_namedthm UNIONS_SINGS "UNIONS_SINGS";;

let IMAGE_INTERS = prove 
 (`!f s. ~(s = {}) /\
         (!x y. x IN UNIONS s /\ y IN UNIONS s /\ f x = f y ==> x = y)
         ==> IMAGE f (INTERS s) = INTERS(IMAGE (IMAGE f) s)`,
  REWRITE_TAC[INTERS_IMAGE] THEN SET_TAC[]);;

export_namedthm IMAGE_INTERS "IMAGE_INTERS";;

let DIFF_INTERS = prove 
 (`!u s. u DIFF INTERS s = UNIONS {u DIFF t | t IN s}`,
  REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]);;

export_namedthm DIFF_INTERS "DIFF_INTERS";;

let INTERS_UNIONS = prove 
 (`!s. INTERS s = UNIV DIFF (UNIONS {UNIV DIFF t | t IN s})`,
  REWRITE_TAC[GSYM DIFF_INTERS] THEN SET_TAC[]);;

export_namedthm INTERS_UNIONS "INTERS_UNIONS";;

let UNIONS_INTERS = prove 
 (`!s. UNIONS s = UNIV DIFF (INTERS {UNIV DIFF t | t IN s})`,
  GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_UNIV; IN_DIFF; INTERS_GSPEC; IN_ELIM_THM] THEN
  MESON_TAC[]);;

export_namedthm UNIONS_INTERS "UNIONS_INTERS";;

let UNIONS_DIFF = prove 
 (`!s t. UNIONS s DIFF t = UNIONS {x DIFF t | x IN s}`,
  REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]);;

export_namedthm UNIONS_DIFF "UNIONS_DIFF";;

let DIFF_UNIONS = prove 
 (`!u s. u DIFF UNIONS s = u INTER INTERS {u DIFF t | t IN s}`,
  REWRITE_TAC[INTERS_GSPEC] THEN SET_TAC[]);;

export_namedthm DIFF_UNIONS "DIFF_UNIONS";;

let DIFF_UNIONS_NONEMPTY = prove 
 (`!u s. ~(s = {}) ==> u DIFF UNIONS s = INTERS {u DIFF t | t IN s}`,
  REWRITE_TAC[INTERS_GSPEC] THEN SET_TAC[]);;

export_namedthm DIFF_UNIONS_NONEMPTY "DIFF_UNIONS_NONEMPTY";;

let INTERS_OVER_UNIONS = prove 
 (`!f:A->(B->bool)->bool s.
        INTERS { UNIONS(f x) | x IN s} =
        UNIONS { INTERS {g x | x IN s} |g| !x. x IN s ==> g x IN f x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[SIMPLE_IMAGE; INTERS_IMAGE; UNIONS_IMAGE; UNIONS_GSPEC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `b:B` THEN REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  MESON_TAC[]);;

export_namedthm INTERS_OVER_UNIONS "INTERS_OVER_UNIONS";;

let INTER_INTERS = prove 
 (`(!f s:A->bool. s INTER INTERS f =
           if f = {} then s else INTERS {s INTER t | t IN f}) /\
   (!f s:A->bool. INTERS f INTER s =
           if f = {} then s else INTERS {t INTER s | t IN f})`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INTERS_0; INTER_UNIV; INTERS_GSPEC] THEN
  ASM SET_TAC[]);;

export_namedthm INTER_INTERS "INTER_INTERS";;

let UNIONS_OVER_INTERS = prove 
 (`!f:A->(B->bool)->bool s.
        UNIONS { INTERS(f x) | x IN s} =
        INTERS { UNIONS {g x | x IN s} |g| !x. x IN s ==> g x IN f x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[SIMPLE_IMAGE; INTERS_IMAGE; UNIONS_IMAGE; INTERS_GSPEC] THEN
  REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `(p <=> q) <=> (~p <=> ~q)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  REWRITE_TAC[AND_FORALL_THM; GSYM SKOLEM_THM] THEN MESON_TAC[]);;

export_namedthm UNIONS_OVER_INTERS "UNIONS_OVER_INTERS";;

let IMAGE_INTERS_SUBSET = prove 
 (`!(f:A->B) g. IMAGE f (INTERS g) SUBSET INTERS (IMAGE (IMAGE f) g)`,
  REWRITE_TAC[INTERS_IMAGE] THEN SET_TAC[]);;

export_namedthm IMAGE_INTERS_SUBSET "IMAGE_INTERS_SUBSET";;

let IMAGE_INTER_SUBSET = prove 
 (`!f s t. IMAGE f (s INTER t) SUBSET IMAGE f s INTER IMAGE f t`,
  SET_TAC[]);;

export_namedthm IMAGE_INTER_SUBSET "IMAGE_INTER_SUBSET";;

let IMAGE_INTER_SATURATED_GEN = prove 
 (`!f:A->B s t u.
        {x | x IN u /\ f(x) IN IMAGE f s} SUBSET s /\ t SUBSET u \/
        {x | x IN u /\ f(x) IN IMAGE f t} SUBSET t /\ s SUBSET u
        ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t`,
  SET_TAC[]);;

export_namedthm IMAGE_INTER_SATURATED_GEN "IMAGE_INTER_SATURATED_GEN";;

let IMAGE_INTERS_SATURATED_GEN = prove 
 (`!f:A->B g s u.
        ~(g = {}) /\
        (!t. t IN g ==> t SUBSET u) /\
        (!t. t IN g DELETE s ==> {x | x IN u /\ f(x) IN IMAGE f t} SUBSET t)
        ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)`,
  let lemma = prove
   (`~(g = {}) /\
     (!t. t IN g ==> t SUBSET u /\ {x | x IN u /\ f(x) IN IMAGE f t} SUBSET t)
     ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)`,
    ONCE_REWRITE_TAC[EXTENSION] THEN
    REWRITE_TAC[INTERS_IMAGE; IN_INTERS; IN_IMAGE] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_UNWIND_THM2] THEN SET_TAC[]) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(s:A->bool) IN g` THEN
  ASM_SIMP_TAC[SET_RULE `~(s IN g) ==> g DELETE s = g`] THENL
   [ALL_TAC; MESON_TAC[lemma]] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_INSERT_EMPTY] THEN
  STRIP_TAC THEN ASM_CASES_TAC `g DELETE (s:A->bool) = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; INTERS_0; INTERS_1] THEN
  REWRITE_TAC[IMAGE_CLAUSES; INTERS_INSERT] THEN
  MATCH_MP_TAC(SET_RULE
   `IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t /\
    IMAGE f t = u ==> IMAGE f (s INTER t) = IMAGE f s INTER u`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_INTER_SATURATED_GEN THEN
    EXISTS_TAC `u:A->bool` THEN ASM SET_TAC[];
    MATCH_MP_TAC lemma THEN ASM SET_TAC[]]);;

export_namedthm IMAGE_INTERS_SATURATED_GEN "IMAGE_INTERS_SATURATED_GEN";;

let IMAGE_INTER_SATURATED = prove 
 (`!f:A->B s t.
        {x | f(x) IN IMAGE f s} SUBSET s \/ {x | f(x) IN IMAGE f t} SUBSET t
         ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t`,
  SET_TAC[]);;

export_namedthm IMAGE_INTER_SATURATED "IMAGE_INTER_SATURATED";;

let IMAGE_INTERS_SATURATED = prove 
 (`!f:A->B g s.
        ~(g = {}) /\ (!t. t IN g DELETE s ==> {x | f(x) IN IMAGE f t} SUBSET t)
        ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_INTERS_SATURATED_GEN THEN
  MAP_EVERY EXISTS_TAC [`s:A->bool`; `(:A)`] THEN
  ASM_REWRITE_TAC[IN_UNIV; SUBSET_UNIV]);;

export_namedthm IMAGE_INTERS_SATURATED "IMAGE_INTERS_SATURATED";;

(* ------------------------------------------------------------------------- *)
(* Stronger form of induction is sometimes handy.                            *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDUCT_STRONG = prove 
 (`!P:(A->bool)->bool.
        P {} /\ (!x s. P s /\ ~(x IN s) /\ FINITE s ==> P(x INSERT s))
        ==> !s. FINITE s ==> P s`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:A->bool. FINITE s ==> FINITE s /\ P s` MP_TAC THENL
   [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN ASM_SIMP_TAC[FINITE_RULES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `x:A IN s` THENL
   [SUBGOAL_THEN `x:A INSERT s = s` (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `x:A IN s` THEN SET_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

export_namedthm FINITE_INDUCT_STRONG "FINITE_INDUCT_STRONG";;

(* ------------------------------------------------------------------------- *)
(* Useful general properties of functions.                                   *)
(* ------------------------------------------------------------------------- *)

export_theory "set-function-thm";;

let INJECTIVE_ON_ALT = prove 
 (`!P f. (!x y. P x /\ P y /\ f x = f y ==> x = y) <=>
         (!x y. P x /\ P y ==> (f x = f y <=> x = y))`,
  MESON_TAC[]);;

export_namedthm INJECTIVE_ON_ALT "INJECTIVE_ON_ALT";;

let INJECTIVE_ALT = prove 
 (`!f. (!x y. f x = f y ==> x = y) <=> (!x y. f x = f y <=> x = y)`,
  MESON_TAC[]);;

export_namedthm INJECTIVE_ALT "INJECTIVE_ALT";;

let SURJECTIVE_ON_RIGHT_INVERSE = prove 
 (`!f t. (!y. y IN t ==> ?x. x IN s /\ (f(x) = y)) <=>
         (?g. !y. y IN t ==> g(y) IN s /\ (f(g(y)) = y))`,
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]);;

export_namedthm SURJECTIVE_ON_RIGHT_INVERSE "SURJECTIVE_ON_RIGHT_INVERSE";;

let INJECTIVE_ON_LEFT_INVERSE = prove 
 (`!f s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)) <=>
         (?g. !x. x IN s ==> (g(f(x)) = x))`,
  let lemma = MESON[]
   `(!x. x IN s ==> (g(f(x)) = x)) <=>
    (!y x. x IN s /\ (y = f x) ==> (g y = x))` in
  REWRITE_TAC[lemma; GSYM SKOLEM_THM] THEN MESON_TAC[]);;

export_namedthm INJECTIVE_ON_LEFT_INVERSE "INJECTIVE_ON_LEFT_INVERSE";;

let BIJECTIVE_ON_LEFT_RIGHT_INVERSE = prove 
 (`!f s t.
        (!x. x IN s ==> f(x) IN t)
        ==> ((!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y) /\
             (!y. y IN t ==> ?x. x IN s /\ f x = y) <=>
            ?g. (!y. y IN t ==> g(y) IN s) /\
                (!y. y IN t ==> (f(g(y)) = y)) /\
                (!x. x IN s ==> (g(f(x)) = x)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; SURJECTIVE_ON_RIGHT_INVERSE] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  EQ_TAC THEN ASM_MESON_TAC[]);;

export_namedthm BIJECTIVE_ON_LEFT_RIGHT_INVERSE "BIJECTIVE_ON_LEFT_RIGHT_INVERSE";;

let SURJECTIVE_RIGHT_INVERSE = prove 
 (`(!y. ?x. f(x) = y) <=> (?g. !y. f(g(y)) = y)`,
  MESON_TAC[SURJECTIVE_ON_RIGHT_INVERSE; IN_UNIV]);;

export_namedthm SURJECTIVE_RIGHT_INVERSE "SURJECTIVE_RIGHT_INVERSE";;

let INJECTIVE_LEFT_INVERSE = prove 
 (`(!x y. (f x = f y) ==> (x = y)) <=> (?g. !x. g(f(x)) = x)`,
  let th = REWRITE_RULE[IN_UNIV]
   (ISPECL [`f:A->B`; `UNIV:A->bool`] INJECTIVE_ON_LEFT_INVERSE) in
  REWRITE_TAC[th]);;

export_namedthm INJECTIVE_LEFT_INVERSE "INJECTIVE_LEFT_INVERSE";;

let BIJECTIVE_LEFT_RIGHT_INVERSE = prove 
 (`!f:A->B.
       (!x y. f(x) = f(y) ==> x = y) /\ (!y. ?x. f x = y) <=>
       ?g. (!y. f(g(y)) = y) /\ (!x. g(f(x)) = x)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `(:A)`; `(:B)`] BIJECTIVE_ON_LEFT_RIGHT_INVERSE) THEN
  REWRITE_TAC[IN_UNIV]);;

export_namedthm BIJECTIVE_LEFT_RIGHT_INVERSE "BIJECTIVE_LEFT_RIGHT_INVERSE";;

let FUNCTION_FACTORS_LEFT_GEN = prove 
 (`!P f g. (!x y. P x /\ P y /\ g x = g y ==> f x = f y) <=>
           (?h. !x. P x ==> f(x) = h(g x))`,
  ONCE_REWRITE_TAC[MESON[]
   `(!x. P x ==> f(x) = g(k x)) <=> (!z x. P x /\ z = k x ==> f x = g z)`] THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]);;

export_namedthm FUNCTION_FACTORS_LEFT_GEN "FUNCTION_FACTORS_LEFT_GEN";;

let FUNCTION_FACTORS_LEFT = prove 
 (`!f g. (!x y. (g x = g y) ==> (f x = f y)) <=> ?h. f = h o g`,
  REWRITE_TAC[FUN_EQ_THM; o_THM;
   GSYM(REWRITE_RULE[] (ISPEC `\x. T` FUNCTION_FACTORS_LEFT_GEN))]);;

export_namedthm FUNCTION_FACTORS_LEFT "FUNCTION_FACTORS_LEFT";;

let FUNCTION_FACTORS_RIGHT_GEN = prove 
 (`!P f g. (!x. P x ==> ?y. g(y) = f(x)) <=>
           (?h. !x. P x ==> f(x) = g(h x))`,
  REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]);;

export_namedthm FUNCTION_FACTORS_RIGHT_GEN "FUNCTION_FACTORS_RIGHT_GEN";;

let FUNCTION_FACTORS_RIGHT = prove 
 (`!f g. (!x. ?y. g(y) = f(x)) <=> ?h. f = g o h`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM SKOLEM_THM] THEN MESON_TAC[]);;

export_namedthm FUNCTION_FACTORS_RIGHT "FUNCTION_FACTORS_RIGHT";;

let SURJECTIVE_FORALL_THM = prove 
 (`!f:A->B. (!y. ?x. f x = y) <=> (!P. (!x. P(f x)) <=> (!y. P y))`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN MESON_TAC[]);;

export_namedthm SURJECTIVE_FORALL_THM "SURJECTIVE_FORALL_THM";;

let SURJECTIVE_EXISTS_THM = prove 
 (`!f:A->B. (!y. ?x. f x = y) <=> (!P. (?x. P(f x)) <=> (?y. P y))`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\y:B. !x:A. ~(f x = y)`) THEN MESON_TAC[]);;

export_namedthm SURJECTIVE_EXISTS_THM "SURJECTIVE_EXISTS_THM";;

let SURJECTIVE_IMAGE_THM = prove 
 (`!f:A->B. (!y. ?x. f x = y) <=> (!P. IMAGE f {x | P(f x)} = {x | P x})`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN(MP_TAC o SPEC `\y:B. T`)] THEN
  MESON_TAC[]);;

export_namedthm SURJECTIVE_IMAGE_THM "SURJECTIVE_IMAGE_THM";;

let IMAGE_INJECTIVE_IMAGE_OF_SUBSET = prove 
 (`!f:A->B s.
     ?t. t SUBSET s /\
         IMAGE f s = IMAGE f t /\
         (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `?g. !y. y IN IMAGE (f:A->B) s ==> g(y) IN s /\ f(g(y)) = y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SURJECTIVE_ON_RIGHT_INVERSE] THEN SET_TAC[];
    EXISTS_TAC `IMAGE (g:B->A) (IMAGE (f:A->B) s)` THEN ASM SET_TAC[]]);;

export_namedthm IMAGE_INJECTIVE_IMAGE_OF_SUBSET "IMAGE_INJECTIVE_IMAGE_OF_SUBSET";;

(* ------------------------------------------------------------------------- *)
(* Basic combining theorems for finite sets.                                 *)
(* ------------------------------------------------------------------------- *)

export_theory "set-finite-thm";;

let FINITE_EMPTY = prove 
 (`FINITE {}`,
  REWRITE_TAC[FINITE_RULES]);;

export_namedthm FINITE_EMPTY "FINITE_EMPTY";;

let FINITE_SUBSET = prove 
 (`!(s:A->bool) t. FINITE t /\ s SUBSET t ==> FINITE s`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [MESON_TAC[SUBSET_EMPTY; FINITE_RULES]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
  X_GEN_TAC `t:A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE((x:A) INSERT (t DELETE x))` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT2 FINITE_RULES) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `t SUBSET (x:A INSERT u)` THEN SET_TAC[];
    ASM_CASES_TAC `x:A IN t` THENL
     [SUBGOAL_THEN `x:A INSERT (t DELETE x) = t` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `x:A IN t` THEN SET_TAC[]; ASM_REWRITE_TAC[]];
      FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `t SUBSET x:A INSERT u` THEN
      UNDISCH_TAC `~(x:A IN t)` THEN SET_TAC[]]]);;

export_namedthm FINITE_SUBSET "FINITE_SUBSET";;

let FINITE_RESTRICT = prove 
 (`!s:A->bool P. FINITE s ==> FINITE {x | x IN s /\ P x}`,
  MESON_TAC[SUBSET_RESTRICT; FINITE_SUBSET]);;

export_namedthm FINITE_RESTRICT "FINITE_RESTRICT";;

let FINITE_UNION_IMP = prove 
 (`!(s:A->bool) t. FINITE s /\ FINITE t ==> FINITE (s UNION t)`,
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN REWRITE_TAC[UNION_EMPTY] THEN
  SUBGOAL_THEN `!x s t. (x:A INSERT s) UNION t = x INSERT (s UNION t)`
  (fun th -> REWRITE_TAC[th]) THENL
   [SET_TAC[];
    MESON_TAC[FINITE_RULES]]);;

export_namedthm FINITE_UNION_IMP "FINITE_UNION_IMP";;

let FINITE_UNION = prove 
 (`!(s:A->bool) t. FINITE(s UNION t) <=> FINITE(s) /\ FINITE(t)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `(s:A->bool) UNION t` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_ACCEPT_TAC FINITE_UNION_IMP]);;

export_namedthm FINITE_UNION "FINITE_UNION";;

let FINITE_INTER = prove 
 (`!(s:A->bool) t. FINITE s \/ FINITE t ==> FINITE (s INTER t)`,
  MESON_TAC[INTER_SUBSET; FINITE_SUBSET]);;

export_namedthm FINITE_INTER "FINITE_INTER";;

let FINITE_INSERT = prove 
 (`!(s:A->bool) x. FINITE (x INSERT s) <=> FINITE s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `x:A INSERT s` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC(CONJUNCT2 FINITE_RULES) THEN
    ASM_REWRITE_TAC[]]);;

export_namedthm FINITE_INSERT "FINITE_INSERT";;

let FINITE_SING = prove 
 (`!a. FINITE {a}`,
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES]);;

export_namedthm FINITE_SING "FINITE_SING";;

let FINITE_DELETE_IMP = prove 
 (`!(s:A->bool) x. FINITE s ==> FINITE (s DELETE x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

export_namedthm FINITE_DELETE_IMP "FINITE_DELETE_IMP";;

let FINITE_DELETE = prove 
 (`!(s:A->bool) x. FINITE (s DELETE x) <=> FINITE s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[FINITE_DELETE_IMP] THEN
  ASM_CASES_TAC `x:A IN s` THENL
   [SUBGOAL_THEN `s = x INSERT (s DELETE x:A)`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[FINITE_INSERT] THEN POP_ASSUM MP_TAC THEN SET_TAC[];
    SUBGOAL_THEN `s DELETE x:A = s` (fun th -> REWRITE_TAC[th]) THEN
    POP_ASSUM MP_TAC THEN SET_TAC[]]);;

export_namedthm FINITE_DELETE "FINITE_DELETE";;

let FINITE_FINITE_UNIONS = prove 
 (`!s. FINITE(s) ==> (FINITE(UNIONS s) <=> (!t. t IN s ==> FINITE(t)))`,
  MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; UNIONS_0; UNIONS_INSERT] THEN
  REWRITE_TAC[FINITE_UNION; FINITE_RULES] THEN MESON_TAC[]);;

export_namedthm FINITE_FINITE_UNIONS "FINITE_FINITE_UNIONS";;

let FINITE_IMAGE_EXPAND = prove 
 (`!(f:A->B) s. FINITE s ==> FINITE {y | ?x. x IN s /\ (y = f x)}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[NOT_IN_EMPTY; REWRITE_RULE[] EMPTY_GSPEC; FINITE_RULES] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{y | ?z. z IN (x INSERT s) /\ (y = (f:A->B) z)} =
                {y | ?z. z IN s /\ (y = f z)} UNION {(f x)}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; IN_UNION; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    REWRITE_TAC[FINITE_UNION; FINITE_INSERT; FINITE_RULES]]);;

export_namedthm FINITE_IMAGE_EXPAND "FINITE_IMAGE_EXPAND";;

let FINITE_IMAGE = prove 
 (`!(f:A->B) s. FINITE s ==> FINITE (IMAGE f s)`,
  REWRITE_TAC[IMAGE; FINITE_IMAGE_EXPAND]);;

export_namedthm FINITE_IMAGE "FINITE_IMAGE";;

let FINITE_IMAGE_INJ_GENERAL = prove 
 (`!(f:A->B) A s.
        (!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y) /\
        FINITE A
        ==> FINITE {x | x IN s /\ f(x) IN A}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->A`) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `IMAGE (g:B->A) A` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN ASM SET_TAC[]);;

export_namedthm FINITE_IMAGE_INJ_GENERAL "FINITE_IMAGE_INJ_GENERAL";;

let FINITE_FINITE_PREIMAGE_GENERAL = prove 
 (`!f:A->B s t.
        FINITE t /\
        (!y. y IN t ==> FINITE {x | x IN s /\ f(x) = y})
        ==> FINITE {x | x IN s /\ f(x) IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN s /\ (f:A->B)(x) IN t} =
    UNIONS (IMAGE (\a. {x | x IN s /\ f x = a}) t)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE] THEN SET_TAC[];
    ASM_SIMP_TAC[FINITE_FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE]]);;

export_namedthm FINITE_FINITE_PREIMAGE_GENERAL "FINITE_FINITE_PREIMAGE_GENERAL";;

let FINITE_FINITE_PREIMAGE = prove 
 (`!f:A->B t.
        FINITE t /\
        (!y. y IN t ==> FINITE {x | f(x) = y})
        ==> FINITE {x | f(x) IN t}`,
  REPEAT GEN_TAC THEN MP_TAC
   (ISPECL [`f:A->B`; `(:A)`; `t:B->bool`] FINITE_FINITE_PREIMAGE_GENERAL) THEN
  REWRITE_TAC[IN_UNIV]);;

export_namedthm FINITE_FINITE_PREIMAGE "FINITE_FINITE_PREIMAGE";;

let FINITE_IMAGE_INJ_EQ = prove 
 (`!(f:A->B) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y))
                ==> (FINITE(IMAGE f s) <=> FINITE s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMAGE_INJ_GENERAL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]);;

export_namedthm FINITE_IMAGE_INJ_EQ "FINITE_IMAGE_INJ_EQ";;

let FINITE_IMAGE_INJ = prove 
 (`!(f:A->B) A. (!x y. (f(x) = f(y)) ==> (x = y)) /\
                FINITE A ==> FINITE {x | f(x) IN A}`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`f:A->B`; `A:B->bool`; `UNIV:A->bool`]
    FINITE_IMAGE_INJ_GENERAL) THEN REWRITE_TAC[IN_UNIV]);;

export_namedthm FINITE_IMAGE_INJ "FINITE_IMAGE_INJ";;

let INFINITE_IMAGE = prove 
 (`!f:A->B s.
        INFINITE s /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> INFINITE (IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ_ALT; INJECTIVE_ON_LEFT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->A`) THEN
  REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `s = IMAGE (g:B->A) (IMAGE f s)` SUBST1_TAC THENL
   [ASM SET_TAC[]; MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[]]);;

export_namedthm INFINITE_IMAGE "INFINITE_IMAGE";;

let INFINITE_IMAGE_INJ = prove 
 (`!f:A->B. (!x y. (f x = f y) ==> (x = y))
            ==> !s. INFINITE s ==> INFINITE(IMAGE f s)`,
  MESON_TAC[INFINITE_IMAGE]);;

export_namedthm INFINITE_IMAGE_INJ "INFINITE_IMAGE_INJ";;

let INFINITE_NONEMPTY = prove 
 (`!s. INFINITE(s) ==> ~(s = EMPTY)`,
  MESON_TAC[INFINITE; FINITE_RULES]);;

export_namedthm INFINITE_NONEMPTY "INFINITE_NONEMPTY";;

let INFINITE_DIFF_FINITE = prove 
 (`!s:A->bool t. INFINITE(s) /\ FINITE(t) ==> INFINITE(s DIFF t)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(b /\ ~c ==> ~a) ==> a /\ b ==> c`) THEN
  REWRITE_TAC[INFINITE] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(t:A->bool) UNION (s DIFF t)` THEN
  ASM_REWRITE_TAC[FINITE_UNION] THEN SET_TAC[]);;

export_namedthm INFINITE_DIFF_FINITE "INFINITE_DIFF_FINITE";;

let SUBSET_IMAGE_INJ = prove 
 (`!f:A->B s t.
        s SUBSET (IMAGE f t) <=>
        ?u. u SUBSET t /\
            (!x y. x IN u /\ y IN u ==> (f x = f y <=> x = y)) /\
            s = IMAGE f u`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[IMAGE_SUBSET]] THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `s SUBSET IMAGE f t ==> !x. x IN s ==> ?y. y IN t /\ f y = x`)) THEN
  REWRITE_TAC[SURJECTIVE_ON_RIGHT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->A`) THEN
  EXISTS_TAC `IMAGE (g:B->A) s` THEN ASM SET_TAC[]);;

export_namedthm SUBSET_IMAGE_INJ "SUBSET_IMAGE_INJ";;

let SUBSET_IMAGE = prove 
 (`!f:A->B s t. s SUBSET (IMAGE f t) <=> ?u. u SUBSET t /\ (s = IMAGE f u)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[IMAGE_SUBSET]] THEN
  REWRITE_TAC[SUBSET_IMAGE_INJ] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

export_namedthm SUBSET_IMAGE "SUBSET_IMAGE";;

let EXISTS_SUBSET_IMAGE = prove 
 (`!P f s.
    (?t. t SUBSET IMAGE f s /\ P t) <=> (?t. t SUBSET s /\ P (IMAGE f t))`,
  REWRITE_TAC[SUBSET_IMAGE] THEN MESON_TAC[]);;

export_namedthm EXISTS_SUBSET_IMAGE "EXISTS_SUBSET_IMAGE";;

let FORALL_SUBSET_IMAGE = prove 
 (`!P f s. (!t. t SUBSET IMAGE f s ==> P t) <=>
           (!t. t SUBSET s ==> P(IMAGE f t))`,
  REWRITE_TAC[SUBSET_IMAGE] THEN MESON_TAC[]);;

export_namedthm FORALL_SUBSET_IMAGE "FORALL_SUBSET_IMAGE";;

let EXISTS_SUBSET_IMAGE_INJ = prove 
 (`!P f s.
    (?t. t SUBSET IMAGE f s /\ P t) <=>
    (?t. t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))`,
  REWRITE_TAC[SUBSET_IMAGE_INJ] THEN MESON_TAC[]);;

export_namedthm EXISTS_SUBSET_IMAGE_INJ "EXISTS_SUBSET_IMAGE_INJ";;

let FORALL_SUBSET_IMAGE_INJ = prove 
 (`!P f s. (!t. t SUBSET IMAGE f s ==> P t) <=>
           (!t. t SUBSET s /\
                (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
                 ==> P(IMAGE f t))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(!t. p t) <=> ~(?t. ~p t)`] THEN
  REWRITE_TAC[NOT_IMP; EXISTS_SUBSET_IMAGE_INJ; GSYM CONJ_ASSOC]);;

export_namedthm FORALL_SUBSET_IMAGE_INJ "FORALL_SUBSET_IMAGE_INJ";;

let EXISTS_FINITE_SUBSET_IMAGE_INJ = prove 
 (`!P f s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))`,
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[EXISTS_SUBSET_IMAGE_INJ] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MESON_TAC[FINITE_IMAGE_INJ_EQ]);;

export_namedthm EXISTS_FINITE_SUBSET_IMAGE_INJ "EXISTS_FINITE_SUBSET_IMAGE_INJ";;

let FORALL_FINITE_SUBSET_IMAGE_INJ = prove 
 (`!P f s. (!t. FINITE t /\ t SUBSET IMAGE f s ==> P t) <=>
           (!t. FINITE t /\ t SUBSET s /\
                (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
                 ==> P(IMAGE f t))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(!t. p t) <=> ~(?t. ~p t)`] THEN
  REWRITE_TAC[NOT_IMP; EXISTS_FINITE_SUBSET_IMAGE_INJ; GSYM CONJ_ASSOC]);;

export_namedthm FORALL_FINITE_SUBSET_IMAGE_INJ "FORALL_FINITE_SUBSET_IMAGE_INJ";;

let EXISTS_FINITE_SUBSET_IMAGE = prove 
 (`!P f s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ t SUBSET s /\ P (IMAGE f t))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE_INJ] THEN MESON_TAC[];
    MESON_TAC[FINITE_IMAGE; IMAGE_SUBSET]]);;

export_namedthm EXISTS_FINITE_SUBSET_IMAGE "EXISTS_FINITE_SUBSET_IMAGE";;

let FORALL_FINITE_SUBSET_IMAGE = prove 
 (`!P f s. (!t. FINITE t /\ t SUBSET IMAGE f s ==> P t) <=>
           (!t. FINITE t /\ t SUBSET s ==> P(IMAGE f t))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(!x. P x) <=> ~(?x. ~P x)`] THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC; EXISTS_FINITE_SUBSET_IMAGE]);;

export_namedthm FORALL_FINITE_SUBSET_IMAGE "FORALL_FINITE_SUBSET_IMAGE";;

let FINITE_SUBSET_IMAGE = prove 
 (`!f:A->B s t.
        FINITE(t) /\ t SUBSET (IMAGE f s) <=>
        ?s'. FINITE s' /\ s' SUBSET s /\ (t = IMAGE f s')`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[FINITE_IMAGE; IMAGE_SUBSET]] THEN
  SPEC_TAC(`t:B->bool`,`t:B->bool`) THEN
  REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN MESON_TAC[]);;

export_namedthm FINITE_SUBSET_IMAGE "FINITE_SUBSET_IMAGE";;

let FINITE_SUBSET_IMAGE_IMP = prove 
 (`!f:A->B s t.
        FINITE(t) /\ t SUBSET (IMAGE f s)
        ==> ?s'. FINITE s' /\ s' SUBSET s /\ t SUBSET (IMAGE f s')`,
  MESON_TAC[SUBSET_REFL; FINITE_SUBSET_IMAGE]);;

export_namedthm FINITE_SUBSET_IMAGE_IMP "FINITE_SUBSET_IMAGE_IMP";;

let FINITE_IMAGE_EQ = prove 
 (`!(f:A->B) s. FINITE(IMAGE f s) <=>
                ?t. FINITE t /\ t SUBSET s /\ IMAGE f s = IMAGE f t`,
  MESON_TAC[FINITE_SUBSET_IMAGE; FINITE_IMAGE; SUBSET_REFL]);;

export_namedthm FINITE_IMAGE_EQ "FINITE_IMAGE_EQ";;

let FINITE_IMAGE_EQ_INJ = prove 
 (`!(f:A->B) s. FINITE(IMAGE f s) <=>
                ?t. FINITE t /\ t SUBSET s /\ IMAGE f s = IMAGE f t /\
                    (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[FINITE_IMAGE]] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `IMAGE (f:A->B) s`; `s:A->bool`]
        SUBSET_IMAGE_INJ) THEN
  REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_METIS_TAC[FINITE_IMAGE_INJ_EQ]);;

export_namedthm FINITE_IMAGE_EQ_INJ "FINITE_IMAGE_EQ_INJ";;

let FINITE_DIFF = prove 
 (`!s t. FINITE s ==> FINITE(s DIFF t)`,
  MESON_TAC[FINITE_SUBSET; SUBSET_DIFF]);;

export_namedthm FINITE_DIFF "FINITE_DIFF";;

let INFINITE_SUPERSET = prove 
 (`!s t. INFINITE s /\ s SUBSET t ==> INFINITE t`,
  REWRITE_TAC[INFINITE] THEN MESON_TAC[FINITE_SUBSET]);;

export_namedthm INFINITE_SUPERSET "INFINITE_SUPERSET";;

let FINITE_TRANSITIVITY_CHAIN = prove 
 (`!R s:A->bool.
        FINITE s /\
        (!x. ~(R x x)) /\
        (!x y z. R x y /\ R y z ==> R x z) /\
        (!x. x IN s ==> ?y. y IN s /\ R x y)
        ==> s = {}`,
  GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
  SET_TAC[]);;

export_namedthm FINITE_TRANSITIVITY_CHAIN "FINITE_TRANSITIVITY_CHAIN";;

let UNIONS_MAXIMAL_SETS = prove 
 (`!f. FINITE f
       ==> UNIONS {t:A->bool | t IN f /\ !u. u IN f ==> ~(t PSUBSET u)} =
           UNIONS f`,
  SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_UNIONS; SUBSET_RESTRICT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC UNIONS_MONO THEN
  X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_IN_GSPEC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~ p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\t u:A->bool. s SUBSET t /\ t PSUBSET u`;
    `{t:A->bool | t IN f /\ s SUBSET t}`]FINITE_TRANSITIVITY_CHAIN) THEN
  ASM_SIMP_TAC[NOT_IMP; FINITE_RESTRICT; FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN
  REPEAT CONJ_TAC THENL [SET_TAC[]; SET_TAC[]; ALL_TAC; ASM SET_TAC[]] THEN
  ASM_MESON_TAC[PSUBSET_TRANS; SUBSET_PSUBSET_TRANS; PSUBSET]);;

export_namedthm UNIONS_MAXIMAL_SETS "UNIONS_MAXIMAL_SETS";;

let FINITE_SUBSET_UNIONS = prove 
 (`!f s:A->bool.
        FINITE s /\ s SUBSET UNIONS f
        ==> ?f'. FINITE f' /\ f' SUBSET f /\ s SUBSET UNIONS f'`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [IN_UNIONS; RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u:A->A->bool` THEN DISCH_TAC THEN
  EXISTS_TAC `IMAGE (u:A->A->bool) s` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; UNIONS_IMAGE] THEN ASM SET_TAC[]);;

export_namedthm FINITE_SUBSET_UNIONS "FINITE_SUBSET_UNIONS";;

let UNIONS_IN_CHAIN = prove 
 (`!f:(A->bool)->bool.
        FINITE f /\ ~(f = {}) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> UNIONS f IN f`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT; UNIONS_INSERT] THEN
  REWRITE_TAC[FORALL_AND_THM; TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`;
              NOT_INSERT_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `f:(A->bool)->bool`] THEN
  ASM_CASES_TAC `f:(A->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; IN_INSERT; UNION_EMPTY] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `s UNION t = s \/ s UNION t = t
    ==> t IN f ==> s UNION t = s \/ s UNION t IN f`) THEN
  ASM SET_TAC[]);;

export_namedthm UNIONS_IN_CHAIN "UNIONS_IN_CHAIN";;

let INTERS_IN_CHAIN = prove 
 (`!f:(A->bool)->bool.
        FINITE f /\ ~(f = {}) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> INTERS f IN f`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT; INTERS_INSERT] THEN
  REWRITE_TAC[FORALL_AND_THM; TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`;
              NOT_INSERT_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `f:(A->bool)->bool`] THEN
  ASM_CASES_TAC `f:(A->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[INTERS_0; IN_INSERT; INTER_UNIV] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `s INTER t = s \/ s INTER t = t
    ==> t IN f ==> s INTER t = s \/ s INTER t IN f`) THEN
  ASM SET_TAC[]);;

export_namedthm INTERS_IN_CHAIN "INTERS_IN_CHAIN";;

let FINITE_SUBSET_UNIONS_CHAIN = prove 
 (`!f s:A->bool.
        FINITE s /\ s SUBSET UNIONS f /\ ~(f = {}) /\
        (!t u. t IN f /\ u IN f ==> t SUBSET u \/ u SUBSET t)
        ==> ?t. t IN f /\ s SUBSET t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(A->bool)->bool`; `s:A->bool`]
        FINITE_SUBSET_UNIONS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `t:(A->bool)->bool` THEN
  ASM_CASES_TAC `t:(A->bool)->bool = {}` THENL
   [ASM_SIMP_TAC[UNIONS_0] THEN ASM SET_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `UNIONS t:A->bool` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  MATCH_MP_TAC UNIONS_IN_CHAIN THEN ASM SET_TAC[]);;

export_namedthm FINITE_SUBSET_UNIONS_CHAIN "FINITE_SUBSET_UNIONS_CHAIN";;

(* ------------------------------------------------------------------------- *)
(* Recursion over finite sets; based on Ching-Tsun's code (archive 713).     *)
(* ------------------------------------------------------------------------- *)

export_theory "set-finite-recursion";;

let FINREC = new_recursive_definition num_RECURSION
  `(FINREC (f:A->B->B) b s a 0 <=> (s = {}) /\ (a = b)) /\
   (FINREC (f:A->B->B) b s a (SUC n) <=>
                ?x c. x IN s /\
                      FINREC f b (s DELETE x) c n  /\
                      (a = f x c))`;;

export_namedthm FINREC "FINREC";;

let FINREC_1_LEMMA = prove 
 (`!f b s a. FINREC f b s a (SUC 0) <=> ?x. (s = {x}) /\ (a = f x b)`,
  REWRITE_TAC[FINREC] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN SET_TAC[]);;

export_namedthm FINREC_1_LEMMA "FINREC_1_LEMMA";;

let FINREC_SUC_LEMMA = prove 
 (`!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n s z.
                FINREC f b s z (SUC n)
                ==> !x. x IN s ==> ?w. FINREC f b (s DELETE x) w n /\
                                       (z = f x w)`,
  let lem = prove(`s DELETE (x:A) DELETE y = s DELETE y DELETE x`,SET_TAC[]) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[FINREC_1_LEMMA] THEN REWRITE_TAC[FINREC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `b:B` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [FINREC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:B` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:A = y` THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `c:B` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `FINREC (f:A->B->B) b (s DELETE y) c (SUC n)` THEN
      DISCH_THEN(ANTE_RES_THEN (MP_TAC o SPEC `x:A`)) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:B` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(f:A->B->B) y v` THEN ASM_REWRITE_TAC[FINREC] THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`y:A`; `v:B`] THEN
        ONCE_REWRITE_TAC[lem] THEN ASM_REWRITE_TAC[IN_DELETE];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]]);;

export_namedthm FINREC_SUC_LEMMA "FINREC_SUC_LEMMA";;

let FINREC_UNIQUE_LEMMA = prove 
 (`!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n1 n2 s a1 a2.
                FINREC f b s a1 n1 /\ FINREC f b s a2 n2
                ==> (a1 = a2) /\ (n1 = n2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY];
    REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY];
    REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY];
    IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> MP_TAC(CONJUNCT1 th) THEN MP_TAC th) THEN
    DISCH_THEN(CONJUNCTS_THEN (ANTE_RES_THEN ASSUME_TAC)) THEN
    REWRITE_TAC[FINREC] THEN STRIP_TAC THEN ASM_MESON_TAC[]]);;

export_namedthm FINREC_UNIQUE_LEMMA "FINREC_UNIQUE_LEMMA";;

let FINREC_EXISTS_LEMMA = prove 
 (`!(f:A->B->B) b s. FINITE s ==> ?a n. FINREC f b s a n`,
  let lem = prove(`~(x IN s ) ==> ((x:A INSERT s) DELETE x = s)`,SET_TAC[]) in
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REPEAT STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`b:B`; `0`] THEN REWRITE_TAC[FINREC];
    MAP_EVERY EXISTS_TAC [`(f:A->B->B) x a`; `SUC n`] THEN
    REWRITE_TAC[FINREC] THEN MAP_EVERY EXISTS_TAC [`x:A`; `a:B`] THEN
    FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP lem th; IN_INSERT])]);;

export_namedthm FINREC_EXISTS_LEMMA "FINREC_EXISTS_LEMMA";;

let FINREC_FUN_LEMMA = prove 
 (`!P (R:A->B->C->bool).
       (!s. P s ==> ?a n. R s a n) /\
       (!n1 n2 s a1 a2. R s a1 n1 /\ R s a2 n2 ==> (a1 = a2) /\ (n1 = n2))
       ==> ?f. !s a. P s ==> ((?n. R s a n) <=> (f s = a))`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `\s:A. @a:B. ?n:C. R s a n` THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV THEN
    ASM_MESON_TAC[]]);;

export_namedthm FINREC_FUN_LEMMA "FINREC_FUN_LEMMA";;

let FINREC_FUN = prove 
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !s x. FINITE s /\ x IN s
                      ==> (g s = f x (g (s DELETE x)))`,
  REPEAT STRIP_TAC THEN IMP_RES_THEN MP_TAC FINREC_UNIQUE_LEMMA THEN
  DISCH_THEN(MP_TAC o SPEC `b:B`) THEN DISCH_THEN
   (MP_TAC o CONJ (SPECL [`f:A->B->B`; `b:B`] FINREC_EXISTS_LEMMA)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINREC_FUN_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_TAC `g:(A->bool)->B`) THEN
  EXISTS_TAC `g:(A->bool)->B` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `FINITE(EMPTY:A->bool)`
    (ANTE_RES_THEN (fun th -> GEN_REWRITE_TAC I [GSYM th])) THENL
     [REWRITE_TAC[FINITE_RULES];
      EXISTS_TAC `0` THEN REWRITE_TAC[FINREC]];
    REPEAT STRIP_TAC THEN
    ANTE_RES_THEN MP_TAC (ASSUME `FINITE(s:A->bool)`) THEN
    DISCH_THEN(ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `(g:(A->bool)->B) s`) THEN
    REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    INDUCT_TAC THENL
     [ASM_REWRITE_TAC[FINREC] THEN DISCH_TAC THEN UNDISCH_TAC `x:A IN s` THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY];
      IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN
      DISCH_THEN(ANTE_RES_THEN (MP_TAC o SPEC `x:A`)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:B` (CONJUNCTS_THEN ASSUME_TAC)) THEN
      SUBGOAL_THEN `(g (s DELETE x:A) = w:B)` SUBST1_TAC THENL
       [SUBGOAL_THEN `FINITE(s DELETE x:A)` MP_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[];
          DISCH_THEN(ANTE_RES_THEN (MP_TAC o GSYM)) THEN
          DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
          EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[]]]]);;

export_namedthm FINREC_FUN "FINREC_FUN";;

let SET_RECURSION_LEMMA = prove 
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !x s. FINITE s
                      ==> (g (x INSERT s) =
                                if x IN s then g s else f x (g s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `b:B` o MATCH_MP FINREC_FUN) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A->bool)->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:(A->bool)->B` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[GSYM ABSORPTION] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `FINITE(x:A INSERT s) /\ x IN (x INSERT s)` MP_TAC THENL
     [REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[FINITE_RULES];
      DISCH_THEN(ANTE_RES_THEN SUBST1_TAC) THEN
      REPEAT AP_TERM_TAC THEN UNDISCH_TAC `~(x:A IN s)` THEN SET_TAC[]]]);;

export_namedthm SET_RECURSION_LEMMA "SET_RECURSION_LEMMA";;

let ITSET = new_definition 
  `ITSET f s b =
        (@g. (g {} = b) /\
             !x s. FINITE s
                   ==> (g (x INSERT s) = if x IN s then g s else f x (g s)))
        s`;;

export_namedthm ITSET "ITSET";;

let FINITE_RECURSION = prove 
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f (x INSERT s) b =
                       if x IN s then ITSET f s b
                                 else f x (ITSET f s b))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ITSET] THEN
  CONV_TAC SELECT_CONV THEN MATCH_MP_TAC SET_RECURSION_LEMMA THEN
  ASM_REWRITE_TAC[]);;

export_namedthm FINITE_RECURSION "FINITE_RECURSION";;

let FINITE_RECURSION_DELETE = prove 
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f s b =
                       if x IN s then f x (ITSET f (s DELETE x) b)
                                 else ITSET f (s DELETE x) b)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP FINITE_RECURSION) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o SPEC `b:B`) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:A IN s` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o MATCH_MP FINITE_DELETE_IMP) THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC o SPEC `x:A`) THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
    REWRITE_TAC[IN_DELETE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `x:A IN s` THEN SET_TAC[];
    DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(x:A IN s)` THEN SET_TAC[]]);;

export_namedthm FINITE_RECURSION_DELETE "FINITE_RECURSION_DELETE";;

let ITSET_EQ = prove 
 (`!s f g b. FINITE(s) /\ (!x. x IN s ==> (f x = g x)) /\
             (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s))) /\
             (!x y s. ~(x = y) ==> (g x (g y s) = g y (g x s)))
             ==> (ITSET f s b = ITSET g s b)`,
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FINITE_RECURSION; NOT_IN_EMPTY; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN
  ASM_MESON_TAC[]);;

export_namedthm ITSET_EQ "ITSET_EQ";;

(* ------------------------------------------------------------------------- *)
(* Cardinality.                                                              *)
(* ------------------------------------------------------------------------- *)

export_theory "set-card";;

let CARD = new_definition 
 `CARD s = ITSET (\x n. SUC n) s 0`;;

export_namedthm CARD "CARD";;

let CARD_CLAUSES = prove 
 (`(CARD ({}:A->bool) = 0) /\
   (!(x:A) s. FINITE s ==>
                 (CARD (x INSERT s) =
                      if x IN s then CARD s else SUC(CARD s)))`,
  MP_TAC(ISPECL [`\(x:A) n. SUC n`; `0`] FINITE_RECURSION) THEN
  REWRITE_TAC[CARD]);;

export_namedthm CARD_CLAUSES "CARD_CLAUSES";;

let CARD_UNION = prove 
 (`!(s:A->bool) t. FINITE(s) /\ FINITE(t) /\ (s INTER t = EMPTY)
         ==> (CARD (s UNION t) = CARD s + CARD t)`,
  REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a ==> b /\ c ==> d`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNION_EMPTY; CARD_CLAUSES; INTER_EMPTY; ADD_CLAUSES] THEN
  X_GEN_TAC `x:A` THEN X_GEN_TAC `s:A->bool` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A INSERT s) UNION t = x INSERT (s UNION t)`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE ((s:A->bool) UNION t) /\ FINITE s`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_UNION_IMP THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:A`; `s:A->bool`] (CONJUNCT2 CARD_CLAUSES)) THEN
  MP_TAC(ISPECL [`x:A`; `s:A->bool UNION t`] (CONJUNCT2 CARD_CLAUSES)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(x:A IN (s UNION t))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION] THEN
    UNDISCH_TAC `(x:A INSERT s) INTER t = EMPTY` THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_INTER; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ASM_REWRITE_TAC[SUC_INJ; ADD_CLAUSES] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x:A INSERT s INTER t = EMPTY` THEN SET_TAC[]]);;

export_namedthm CARD_UNION "CARD_UNION";;

let CARD_DELETE = prove 
 (`!x:A s. FINITE(s)
           ==> (CARD(s DELETE x) = if x IN s then CARD(s) - 1 else CARD(s))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `s = x:A INSERT (s DELETE x)`
     (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL [UNDISCH_TAC `x:A IN s` THEN SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_DELETE; IN_DELETE; SUC_SUB1];
    AP_TERM_TAC THEN UNDISCH_TAC `~(x:A IN s)` THEN SET_TAC[]]);;

export_namedthm CARD_DELETE "CARD_DELETE";;

let CARD_UNION_EQ = prove 
 (`!s t u. FINITE u /\ (s INTER t = {}) /\ (s UNION t = u)
           ==> (CARD s + CARD t = CARD u)`,
  MESON_TAC[CARD_UNION; FINITE_SUBSET; SUBSET_UNION]);;

export_namedthm CARD_UNION_EQ "CARD_UNION_EQ";;

let CARD_DIFF = prove 
 (`!s t. FINITE s /\ t SUBSET s ==> CARD(s DIFF t) = CARD s - CARD t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `a + b:num = c ==> a = c - b`) THEN
  MATCH_MP_TAC CARD_UNION_EQ THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

export_namedthm CARD_DIFF "CARD_DIFF";;

let CARD_EQ_0 = prove 
 (`!s. FINITE s ==> ((CARD s = 0) <=> (s = {}))`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CARD_CLAUSES; NOT_INSERT_EMPTY; NOT_SUC]);;

export_namedthm CARD_EQ_0 "CARD_EQ_0";;

let CARD_SING = prove 
 (`!a:A. CARD {a} = 1`,
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; NOT_IN_EMPTY; ARITH]);;

export_namedthm CARD_SING "CARD_SING";;

(* ------------------------------------------------------------------------- *)
(* A stronger still form of induction where we get to choose the element.    *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDUCT_DELETE = prove 
 (`!P. P {} /\
       (!s. FINITE s /\ ~(s = {}) ==> ?x. x IN s /\ (P(s DELETE x) ==> P s))
       ==> !s:A->bool. FINITE s ==> P s`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `CARD(s:A->bool)` THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC
   `!s. FINITE s /\ ~(s = {}) ==> ?x:A. x IN s /\ (P(s DELETE x) ==> P s)` THEN
  DISCH_THEN(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (x:A)`) THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; CARD_EQ_0;
               ARITH_RULE `n - 1 < n <=> ~(n = 0)`]);;

export_namedthm FINITE_INDUCT_DELETE "FINITE_INDUCT_DELETE";;

(* ------------------------------------------------------------------------- *)
(* Relational form is often more useful.                                     *)
(* ------------------------------------------------------------------------- *)

export_theory "set-card-rel";;

let HAS_SIZE = new_definition 
  `s HAS_SIZE n <=> FINITE s /\ (CARD s = n)`;;

export_namedthm HAS_SIZE "HAS_SIZE";;

let HAS_SIZE_CARD = prove 
 (`!s n. s HAS_SIZE n ==> (CARD s = n)`,
  SIMP_TAC[HAS_SIZE]);;

export_namedthm HAS_SIZE_CARD "HAS_SIZE_CARD";;

let HAS_SIZE_0 = prove 
 (`!(s:A->bool). s HAS_SIZE 0 <=> (s = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  EQ_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[FINITE_RULES; CARD_CLAUSES] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN
  SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT2 CARD_CLAUSES) th]) THEN
  ASM_REWRITE_TAC[NOT_SUC]);;

export_namedthm HAS_SIZE_0 "HAS_SIZE_0";;

let HAS_SIZE_SUC = prove 
 (`!(s:A->bool) n. s HAS_SIZE (SUC n) <=>
                   ~(s = {}) /\ !a. a IN s ==> (s DELETE a) HAS_SIZE n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; NOT_SUC] THEN
  REWRITE_TAC[FINITE_DELETE] THEN
  ASM_CASES_TAC `FINITE(s:A->bool)` THEN
  ASM_REWRITE_TAC[NOT_FORALL_THM; MEMBER_NOT_EMPTY] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`a:A`; `s DELETE a:A`] (CONJUNCT2 CARD_CLAUSES)) THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
    SUBGOAL_THEN `a INSERT (s DELETE a:A) = s` SUBST1_TAC THENL
     [UNDISCH_TAC `a:A IN s` THEN SET_TAC[];
      ASM_REWRITE_TAC[SUC_INJ] THEN MESON_TAC[]];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
    MP_TAC(ISPECL [`a:A`; `s DELETE a:A`] (CONJUNCT2 CARD_CLAUSES)) THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
    SUBGOAL_THEN `a INSERT (s DELETE a:A) = s` SUBST1_TAC THENL
     [UNDISCH_TAC `a:A IN s` THEN SET_TAC[];
      ASM_MESON_TAC[]]]);;

export_namedthm HAS_SIZE_SUC "HAS_SIZE_SUC";;

let HAS_SIZE_UNION = prove 
 (`!s t m n. s HAS_SIZE m /\ t HAS_SIZE n /\ DISJOINT s t
             ==> (s UNION t) HAS_SIZE (m + n)`,
  SIMP_TAC[HAS_SIZE; FINITE_UNION; DISJOINT; CARD_UNION]);;

export_namedthm HAS_SIZE_UNION "HAS_SIZE_UNION";;

let HAS_SIZE_DIFF = prove 
 (`!s t m n. s HAS_SIZE m /\ t HAS_SIZE n /\ t SUBSET s
             ==> (s DIFF t) HAS_SIZE (m - n)`,
  SIMP_TAC[HAS_SIZE; FINITE_DIFF; CARD_DIFF]);;

export_namedthm HAS_SIZE_DIFF "HAS_SIZE_DIFF";;

let HAS_SIZE_UNIONS = prove 
 (`!s t:A->B->bool m n.
        s HAS_SIZE m /\
        (!x. x IN s ==> t(x) HAS_SIZE n) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (t x) (t y))
        ==> UNIONS {t(x) | x IN s} HAS_SIZE (m * n)`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[CARD_CLAUSES] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
    REWRITE_TAC[MULT_CLAUSES; HAS_SIZE_0; EMPTY_UNIONS] THEN
    REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:A->B->bool`; `m:num`; `n:num`] THEN
  ASM_SIMP_TAC[CARD_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SET_RULE
   `UNIONS {t y | y IN x INSERT s} = t x UNION UNIONS {t y | y IN s}`] THEN
  REWRITE_TAC[ARITH_RULE `SUC a * b = b + a * b`] THEN
  MATCH_MP_TAC HAS_SIZE_UNION THEN ASM_SIMP_TAC[IN_INSERT] THEN
  REWRITE_TAC[SET_RULE
   `DISJOINT a (UNIONS s) <=> !x. x IN s ==> DISJOINT a x`] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  ASM_MESON_TAC[IN_INSERT]);;

export_namedthm HAS_SIZE_UNIONS "HAS_SIZE_UNIONS";;

let FINITE_HAS_SIZE = prove 
 (`!s. FINITE s <=> s HAS_SIZE CARD s`,
  REWRITE_TAC[HAS_SIZE]);;

export_namedthm FINITE_HAS_SIZE "FINITE_HAS_SIZE";;

(* ------------------------------------------------------------------------- *)
(* This is often more useful as a rewrite.                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_CLAUSES = prove 
 (`(s HAS_SIZE 0 <=> (s = {})) /\
   (s HAS_SIZE (SUC n) <=>
        ?a t. t HAS_SIZE n /\ ~(a IN t) /\ (s = a INSERT t))`,
  let lemma = SET_RULE `a IN s ==> (s = a INSERT (s DELETE a))` in
  REWRITE_TAC[HAS_SIZE_0] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[HAS_SIZE_SUC; GSYM MEMBER_NOT_EMPTY] THEN
    MESON_TAC[lemma; IN_DELETE];
    SIMP_TAC[LEFT_IMP_EXISTS_THM; HAS_SIZE; CARD_CLAUSES; FINITE_INSERT]]);;

export_namedthm HAS_SIZE_CLAUSES "HAS_SIZE_CLAUSES";;

(* ------------------------------------------------------------------------- *)
(* Produce an explicit expansion for "s HAS_SIZE n" for numeral n.           *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_CONV =
  let pth = prove
   (`(~(a IN {}) /\ P <=> P) /\
     (~(a IN {b}) /\ P <=> ~(a = b) /\ P) /\
     (~(a IN (b INSERT cs)) /\ P <=> ~(a = b) /\ ~(a IN cs) /\ P)`,
    SET_TAC[])
  and qth = prove
   (`((?s. s HAS_SIZE 0 /\ P s) <=> P {}) /\
     ((?s. s HAS_SIZE (SUC n) /\ P s) <=>
      (?a s. s HAS_SIZE n /\ ~(a IN s) /\ P(a INSERT s)))`,
    REWRITE_TAC[HAS_SIZE_CLAUSES] THEN MESON_TAC[]) in
  let qconv_0 = GEN_REWRITE_CONV I [CONJUNCT1 qth]
  and qconv_1 = GEN_REWRITE_CONV I [CONJUNCT2 qth]
  and rconv_0 = GEN_REWRITE_CONV I [CONJUNCT1 pth]
  and rconv_1 = GEN_REWRITE_CONV I [CONJUNCT2 pth] in
  let rec EXISTS_HAS_SIZE_AND_CONV tm =
   (qconv_0 ORELSEC
    (BINDER_CONV(LAND_CONV(RAND_CONV num_CONV)) THENC
     qconv_1 THENC
     BINDER_CONV EXISTS_HAS_SIZE_AND_CONV)) tm in
  let rec NOT_IN_INSERT_CONV tm =
   ((rconv_0 THENC NOT_IN_INSERT_CONV) ORELSEC
    (rconv_1 THENC RAND_CONV NOT_IN_INSERT_CONV) ORELSEC
    ALL_CONV) tm in
  let HAS_SIZE_CONV =
    GEN_REWRITE_CONV I [CONJUNCT1 HAS_SIZE_CLAUSES] ORELSEC
    (RAND_CONV num_CONV THENC
     GEN_REWRITE_CONV I [CONJUNCT2 HAS_SIZE_CLAUSES] THENC
     BINDER_CONV EXISTS_HAS_SIZE_AND_CONV) in
  fun tm ->
    let th = HAS_SIZE_CONV tm in
    let tm' = rand(concl th) in
    let evs,bod = strip_exists tm' in
    if evs = [] then th else
    let th' = funpow (length evs) BINDER_CONV NOT_IN_INSERT_CONV tm' in
    TRANS th th';;

(* ------------------------------------------------------------------------- *)
(* Various useful lemmas about cardinalities of unions etc.                  *)
(* ------------------------------------------------------------------------- *)

export_theory "set-card-misc";;

let CARD_SUBSET_EQ = prove 
 (`!(a:A->bool) b. FINITE b /\ a SUBSET b /\ (CARD a = CARD b) ==> (a = b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:A->bool`; `b DIFF (a:A->bool)`] CARD_UNION) THEN
  SUBGOAL_THEN `FINITE(a:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(b:A->bool DIFF a)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `b:A->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a:A->bool INTER (b DIFF a) = EMPTY` ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a UNION (b:A->bool DIFF a) = b` ASSUME_TAC THENL
   [UNDISCH_TAC `a:A->bool SUBSET b` THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(a = a + b) <=> (b = 0)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `b:A->bool DIFF a = EMPTY` MP_TAC THENL
   [REWRITE_TAC[GSYM HAS_SIZE_0] THEN
    ASM_REWRITE_TAC[HAS_SIZE];
    UNDISCH_TAC `a:A->bool SUBSET b` THEN SET_TAC[]]);;

export_namedthm CARD_SUBSET_EQ "CARD_SUBSET_EQ";;

let CARD_SUBSET = prove 
 (`!(a:A->bool) b. a SUBSET b /\ FINITE(b) ==> CARD(a) <= CARD(b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `b:A->bool = a UNION (b DIFF a)` SUBST1_TAC THENL
   [UNDISCH_TAC `a:A->bool SUBSET b` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD (a UNION b DIFF a) = CARD(a:A->bool) + CARD(b DIFF a)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CARD_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `b:A->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `b:A->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SET_TAC[]];
    ARITH_TAC]);;

export_namedthm CARD_SUBSET "CARD_SUBSET";;

let CARD_SUBSET_LE = prove 
 (`!(a:A->bool) b. FINITE b /\ a SUBSET b /\ (CARD b <= CARD a) ==> (a = b)`,
  MESON_TAC[CARD_SUBSET; CARD_SUBSET_EQ; LE_ANTISYM]);;

export_namedthm CARD_SUBSET_LE "CARD_SUBSET_LE";;

let SUBSET_CARD_EQ = prove 
 (`!s t. FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t)`,
  MESON_TAC[CARD_SUBSET_EQ; LE_ANTISYM; CARD_SUBSET]);;

export_namedthm SUBSET_CARD_EQ "SUBSET_CARD_EQ";;

let CARD_PSUBSET = prove 
 (`!(a:A->bool) b. a PSUBSET b /\ FINITE(b) ==> CARD(a) < CARD(b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SET_RULE
   `a PSUBSET b <=> ?x. x IN b /\ ~(x IN a) /\ a SUBSET (b DELETE x)` ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `CARD(b DELETE (x:A))` THEN
  ASM_SIMP_TAC[CARD_SUBSET; FINITE_DELETE] THEN
  ASM_SIMP_TAC[CARD_DELETE; ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ASM_MESON_TAC[CARD_EQ_0; MEMBER_NOT_EMPTY]);;

export_namedthm CARD_PSUBSET "CARD_PSUBSET";;

let CARD_UNION_LE = prove 
 (`!s t:A->bool.
        FINITE s /\ FINITE t ==> CARD(s UNION t) <= CARD(s) + CARD(t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(s:A->bool) + CARD(t DIFF s)` THEN
  ASM_SIMP_TAC[LE_ADD_LCANCEL; CARD_SUBSET; SUBSET_DIFF; FINITE_DIFF] THEN
  MATCH_MP_TAC EQ_IMP_LE THEN
  ONCE_REWRITE_TAC[SET_RULE `s UNION t = s UNION (t DIFF s)`] THEN
  MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC[FINITE_DIFF] THEN SET_TAC[]);;

export_namedthm CARD_UNION_LE "CARD_UNION_LE";;

let CARD_UNIONS_LE = prove 
 (`!s t:A->B->bool m n.
        s HAS_SIZE m /\ (!x. x IN s ==> FINITE(t x) /\ CARD(t x) <= n)
        ==> CARD(UNIONS {t(x) | x IN s}) <= m * n`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THEN
  REWRITE_TAC[SET_RULE `UNIONS {t x | x IN {}} = {}`; CARD_CLAUSES; LE_0] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[SET_RULE
   `UNIONS {t x | x IN a INSERT s} = t(a) UNION UNIONS {t x | x IN s}`] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC
   `CARD((t:A->B->bool) x) + CARD(UNIONS {(t:A->B->bool) y | y IN s})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_UNION_LE THEN ASM_SIMP_TAC[IN_INSERT] THEN
    REWRITE_TAC[SET_RULE `{t x | x IN s} = IMAGE t s`] THEN
    ASM_SIMP_TAC[FINITE_FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE;
                 IN_INSERT];
    MATCH_MP_TAC(ARITH_RULE `a <= n /\ b <= x * n ==> a + b <= SUC x * n`) THEN
    ASM_SIMP_TAC[IN_INSERT]]);;

export_namedthm CARD_UNIONS_LE "CARD_UNIONS_LE";;

let CARD_UNION_GEN = prove 
 (`!s t. FINITE s /\ FINITE t
         ==> CARD(s UNION t) = (CARD(s) + CARD(t)) - CARD(s INTER t)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `s UNION t = s UNION (t DIFF s)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `x:num <= y ==> (a + y) - x = a + (y - x)`;
               CARD_SUBSET; INTER_SUBSET; GSYM CARD_DIFF] THEN
  REWRITE_TAC[SET_RULE `t DIFF (s INTER t) = t DIFF s`] THEN
  MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC[FINITE_DIFF] THEN SET_TAC[]);;

export_namedthm CARD_UNION_GEN "CARD_UNION_GEN";;

let CARD_UNION_OVERLAP_EQ = prove 
 (`!s t. FINITE s /\ FINITE t
         ==> (CARD(s UNION t) = CARD s + CARD t <=> s INTER t = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_UNION_GEN] THEN
  REWRITE_TAC[ARITH_RULE `a - b = a <=> b = 0 \/ a = 0`] THEN
  ASM_SIMP_TAC[ADD_EQ_0; CARD_EQ_0; FINITE_INTER] THEN SET_TAC[]);;

export_namedthm CARD_UNION_OVERLAP_EQ "CARD_UNION_OVERLAP_EQ";;

let CARD_UNION_OVERLAP = prove 
 (`!s t. FINITE s /\ FINITE t /\ CARD(s UNION t) < CARD(s) + CARD(t)
         ==> ~(s INTER t = {})`,
  SIMP_TAC[GSYM CARD_UNION_OVERLAP_EQ] THEN ARITH_TAC);;

export_namedthm CARD_UNION_OVERLAP "CARD_UNION_OVERLAP";;

(* ------------------------------------------------------------------------- *)
(* Cardinality of image under maps, injective or general.                    *)
(* ------------------------------------------------------------------------- *)

export_theory "set-card-image";;

let CARD_IMAGE_INJ = prove 
 (`!(f:A->B) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
                FINITE s ==> (CARD (IMAGE f s) = CARD s)`,
  GEN_TAC THEN
  REWRITE_TAC[TAUT `a /\ b ==> c <=> b ==> a ==> c`] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; IMAGE_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_IMAGE; IN_IMAGE] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[IN_INSERT]);;

export_namedthm CARD_IMAGE_INJ "CARD_IMAGE_INJ";;

let HAS_SIZE_IMAGE_INJ = prove 
 (`!(f:A->B) s n.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\ s HAS_SIZE n
        ==> (IMAGE f s) HAS_SIZE n`,
  SIMP_TAC[HAS_SIZE; FINITE_IMAGE] THEN MESON_TAC[CARD_IMAGE_INJ]);;

export_namedthm HAS_SIZE_IMAGE_INJ "HAS_SIZE_IMAGE_INJ";;

let CARD_IMAGE_LE = prove 
 (`!(f:A->B) s. FINITE s ==> CARD(IMAGE f s) <= CARD s`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IMAGE_CLAUSES; CARD_CLAUSES; FINITE_IMAGE; LE_REFL] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ARITH_TAC);;

export_namedthm CARD_IMAGE_LE "CARD_IMAGE_LE";;

let CARD_IMAGE_INJ_EQ = prove 
 (`!f:A->B s t.
        FINITE s /\
        (!x. x IN s ==> f(x) IN t) /\
        (!y. y IN t ==> ?!x. x IN s /\ f(x) = y)
        ==> CARD t = CARD s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = IMAGE (f:A->B) s` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[]]);;

export_namedthm CARD_IMAGE_INJ_EQ "CARD_IMAGE_INJ_EQ";;

let CARD_SUBSET_IMAGE = prove 
 (`!f s t. FINITE t /\ s SUBSET IMAGE f t ==> CARD s <= CARD t`,
  MESON_TAC[LE_TRANS; FINITE_IMAGE; CARD_IMAGE_LE; CARD_SUBSET]);;

export_namedthm CARD_SUBSET_IMAGE "CARD_SUBSET_IMAGE";;

let HAS_SIZE_IMAGE_INJ_EQ = prove 
 (`!f s n.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ((IMAGE f s) HAS_SIZE n <=> s HAS_SIZE n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  MATCH_MP_TAC(TAUT
   `(a' <=> a) /\ (a ==> (b' <=> b)) ==> (a' /\ b' <=> a /\ b)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ;
    DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CARD_IMAGE_INJ] THEN
  ASM_REWRITE_TAC[]);;

export_namedthm HAS_SIZE_IMAGE_INJ_EQ "HAS_SIZE_IMAGE_INJ_EQ";;

let CARD_IMAGE_EQ_INJ = prove 
 (`!f:A->B s.
        FINITE s
        ==> (CARD(IMAGE f s) = CARD s <=>
             !x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[CARD_IMAGE_INJ]] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:A = y` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `CARD(IMAGE (f:A->B) s) = CARD s` THEN
  SUBGOAL_THEN `IMAGE  (f:A->B) s = IMAGE f (s DELETE y)` SUBST1_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[]] THEN
  MATCH_MP_TAC(ARITH_RULE `!n. m <= n /\ n < p ==> ~(m:num = p)`) THEN
  EXISTS_TAC `CARD(s DELETE (y:A))` THEN
  ASM_SIMP_TAC[CARD_IMAGE_LE; FINITE_DELETE] THEN
  ASM_SIMP_TAC[CARD_DELETE; CARD_EQ_0;
               ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ASM SET_TAC[]);;

export_namedthm CARD_IMAGE_EQ_INJ "CARD_IMAGE_EQ_INJ";;

(* ------------------------------------------------------------------------- *)
(* Choosing a smaller subset of a given size.                                *)
(* ------------------------------------------------------------------------- *)

export_theory "set-choose-subset";;

let CHOOSE_SUBSET_STRONG = prove 
 (`!n s:A->bool.
        (FINITE s ==> n <= CARD s) ==> ?t. t SUBSET s /\ t HAS_SIZE n`,
  INDUCT_TAC THEN REWRITE_TAC[HAS_SIZE_0; HAS_SIZE_SUC] THENL
   [MESON_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC SET_PROVE_CASES THEN
  REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES; ARITH_RULE `~(SUC n <= 0)`] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; LE_SUC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(a:A) INSERT t` THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[HAS_SIZE; CARD_DELETE; FINITE_INSERT; FINITE_DELETE;
               CARD_CLAUSES] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
  ASM SET_TAC[]);;

export_namedthm CHOOSE_SUBSET_STRONG "CHOOSE_SUBSET_STRONG";;

let CHOOSE_SUBSET_EQ = prove 
 (`!n s:A->bool.
     (FINITE s ==> n <= CARD s) <=> (?t. t SUBSET s /\ t HAS_SIZE n)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[CHOOSE_SUBSET_STRONG] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  TRANS_TAC LE_TRANS `CARD(t:A->bool)` THEN
  ASM_MESON_TAC[CARD_SUBSET; HAS_SIZE; LE_REFL]);;

export_namedthm CHOOSE_SUBSET_EQ "CHOOSE_SUBSET_EQ";;

let CHOOSE_SUBSET = prove 
 (`!s:A->bool. FINITE s ==> !n. n <= CARD s ==> ?t. t SUBSET s /\ t HAS_SIZE n`,
  MESON_TAC[CHOOSE_SUBSET_STRONG]);;

export_namedthm CHOOSE_SUBSET "CHOOSE_SUBSET";;

let CHOOSE_SUBSET_BETWEEN = prove 
 (`!n s u:A->bool.
        s SUBSET u /\ FINITE s /\ CARD s <= n /\ (FINITE u ==> n <= CARD u)
        ==> ?t. s SUBSET t /\ t SUBSET u /\ t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n - CARD(s:A->bool)`; `u DIFF s:A->bool`]
        CHOOSE_SUBSET_STRONG) THEN
  ANTS_TAC THENL
   [ASM_CASES_TAC `FINITE(u:A->bool)` THEN
    ASM_SIMP_TAC[CARD_DIFF; ARITH_RULE `n:num <= m ==> n - x <= m - x`] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    ASM_MESON_TAC[FINITE_UNION; FINITE_SUBSET; SET_RULE
     `u SUBSET (u DIFF s) UNION s`];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s UNION t:A->bool` THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    SUBGOAL_THEN `n:num = CARD(s) + (n - CARD(s:A->bool))` SUBST1_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC HAS_SIZE_UNION] THEN
      ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[HAS_SIZE] THEN ASM SET_TAC[]]);;

export_namedthm CHOOSE_SUBSET_BETWEEN "CHOOSE_SUBSET_BETWEEN";;

let CARD_LE_UNIONS_CHAIN = prove 
 (`!(f:(A->bool)->bool) n.
        (!t u. t IN f /\ u IN f ==> t SUBSET u \/ u SUBSET t) /\
        (!t. t IN f ==> FINITE t /\ CARD t <= n)
        ==> FINITE(UNIONS f) /\ CARD(UNIONS f) <= n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `f:(A->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; FINITE_EMPTY; CARD_CLAUSES; LE_0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
  REWRITE_TAC[ARITH_RULE `~(x <= n) <=> SUC n <= x`] THEN
  REWRITE_TAC[CHOOSE_SUBSET_EQ] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:A->bool` THEN
  REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET_UNIONS_CHAIN THEN
  ASM_REWRITE_TAC[]);;

export_namedthm CARD_LE_UNIONS_CHAIN "CARD_LE_UNIONS_CHAIN";;

let CARD_LE_1 = prove 
 (`!s:A->bool. FINITE s /\ CARD s <= 1 <=> ?a. s SUBSET {a}`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `c <= 1 <=> c = 0 \/ c = 1`] THEN
  REWRITE_TAC[LEFT_OR_DISTRIB; GSYM HAS_SIZE] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN SET_TAC[]);;

export_namedthm CARD_LE_1 "CARD_LE_1";;

(* ------------------------------------------------------------------------- *)
(* Cardinality of product.                                                   *)
(* ------------------------------------------------------------------------- *)

export_theory "set-card-product";;

let HAS_SIZE_PRODUCT_DEPENDENT = prove 
 (`!s m t n.
         s HAS_SIZE m /\ (!x. x IN s ==> t(x) HAS_SIZE n)
         ==> {(x:A,y:B) | x IN s /\ y IN t(x)} HAS_SIZE (m * n)`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CARD_CLAUSES; NOT_IN_EMPTY; IN_INSERT] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MULT_CLAUSES; HAS_SIZE_0] THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  MAP_EVERY X_GEN_TAC [`t:A->B->bool`; `n:num`] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `CARD(s:A->bool)`) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES] THEN DISCH_TAC THEN
  REWRITE_TAC[SET_RULE
    `{(x,y) | (x = a \/ x IN s) /\ y IN t(x)} =
     {(x,y) | x IN s /\ y IN t(x)} UNION
     IMAGE (\y. (a,y)) (t a)`] THEN
  MATCH_MP_TAC HAS_SIZE_UNION THEN
  ASM_SIMP_TAC[HAS_SIZE_IMAGE_INJ; PAIR_EQ] THEN
  REWRITE_TAC[DISJOINT; IN_IMAGE; IN_ELIM_THM; IN_INTER; EXTENSION;
              NOT_IN_EMPTY; EXISTS_PAIR_THM; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[PAIR_EQ]);;

export_namedthm HAS_SIZE_PRODUCT_DEPENDENT "HAS_SIZE_PRODUCT_DEPENDENT";;

let FINITE_PRODUCT_DEPENDENT = prove 
 (`!f:A->B->C s t.
        FINITE s /\ (!x. x IN s ==> FINITE(t x))
        ==> FINITE {f x y | x IN s /\ y IN (t x)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\(x,y). (f:A->B->C) x y) {x,y | x IN s /\ y IN t x}` THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE; MESON_TAC[]] THEN
  MAP_EVERY UNDISCH_TAC
   [`!x:A. x IN s ==> FINITE(t x :B->bool)`; `FINITE(s:A->bool)`] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`t:A->B->bool`; `s:A->bool`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [GEN_TAC THEN SUBGOAL_THEN `{(x:A,y:B) | x IN {} /\ y IN (t x)} = {}`
     (fun th -> REWRITE_TAC[th; FINITE_RULES]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `t:A->B->bool` THEN
  SUBGOAL_THEN
   `{(x:A,y:B) | x IN (a INSERT s) /\ y IN (t x)} =
    IMAGE (\y. a,y) (t a) UNION {(x,y) | x IN s /\ y IN (t x)}`
   (fun th -> ASM_SIMP_TAC[IN_INSERT; FINITE_IMAGE; FINITE_UNION; th]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INSERT; IN_UNION] THEN
  MESON_TAC[]);;

export_namedthm FINITE_PRODUCT_DEPENDENT "FINITE_PRODUCT_DEPENDENT";;

let FINITE_PRODUCT = prove 
 (`!s t. FINITE s /\ FINITE t ==> FINITE {(x:A,y:B) | x IN s /\ y IN t}`,
  SIMP_TAC[FINITE_PRODUCT_DEPENDENT]);;

export_namedthm FINITE_PRODUCT "FINITE_PRODUCT";;

let CARD_PRODUCT = prove 
 (`!s t. FINITE s /\ FINITE t
         ==> (CARD {(x:A,y:B) | x IN s /\ y IN t} = CARD s * CARD t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:A->bool`; `CARD(s:A->bool)`; `\x:A. t:B->bool`;
                  `CARD(t:B->bool)`] HAS_SIZE_PRODUCT_DEPENDENT) THEN
  ASM_SIMP_TAC[HAS_SIZE]);;

export_namedthm CARD_PRODUCT "CARD_PRODUCT";;

let HAS_SIZE_PRODUCT = prove 
 (`!s m t n. s HAS_SIZE m /\ t HAS_SIZE n
             ==> {(x:A,y:B) | x IN s /\ y IN t} HAS_SIZE (m * n)`,
  SIMP_TAC[HAS_SIZE; CARD_PRODUCT; FINITE_PRODUCT]);;

export_namedthm HAS_SIZE_PRODUCT "HAS_SIZE_PRODUCT";;

(* ------------------------------------------------------------------------- *)
(* Actually introduce a Cartesian product operation.                         *)
(* ------------------------------------------------------------------------- *)

export_theory "set-cart-prod";;

parse_as_infix("CROSS",(22,"right"));;

let CROSS = new_definition 
 `s CROSS t = {x,y | x IN s /\ y IN t}`;;

export_namedthm CROSS "CROSS";;

let IN_CROSS = prove 
 (`!x y s t. (x,y) IN (s CROSS t) <=> x IN s /\ y IN t`,
  REWRITE_TAC[CROSS; IN_ELIM_PAIR_THM]);;

export_namedthm IN_CROSS "IN_CROSS";;

let HAS_SIZE_CROSS = prove 
 (`!s t m n. s HAS_SIZE m /\ t HAS_SIZE n ==> (s CROSS t) HAS_SIZE (m * n)`,
  REWRITE_TAC[CROSS; HAS_SIZE_PRODUCT]);;

export_namedthm HAS_SIZE_CROSS "HAS_SIZE_CROSS";;

let FINITE_CROSS = prove 
 (`!s t. FINITE s /\ FINITE t ==> FINITE(s CROSS t)`,
  SIMP_TAC[CROSS; FINITE_PRODUCT]);;

export_namedthm FINITE_CROSS "FINITE_CROSS";;

let CARD_CROSS = prove 
 (`!s t. FINITE s /\ FINITE t ==> CARD(s CROSS t) = CARD s * CARD t`,
  SIMP_TAC[CROSS; CARD_PRODUCT]);;

export_namedthm CARD_CROSS "CARD_CROSS";;

let CROSS_EQ_EMPTY = prove 
 (`!s t. s CROSS t = {} <=> s = {} \/ t = {}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_CROSS; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

export_namedthm CROSS_EQ_EMPTY "CROSS_EQ_EMPTY";;

let CROSS_EMPTY = prove 
 (`(!s:A->bool. s CROSS {} = {}) /\ (!t:B->bool. {} CROSS t = {})`,
  REWRITE_TAC[CROSS_EQ_EMPTY]);;

export_namedthm CROSS_EMPTY "CROSS_EMPTY";;

let CROSS_SING = prove 
 (`!x:A y:B. {x} CROSS {y} = {(x,y)}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_SING; IN_CROSS; PAIR_EQ]);;

export_namedthm CROSS_SING "CROSS_SING";;

let CROSS_UNIV = prove 
 (`(:A) CROSS (:B) = (:A#B)`,
  REWRITE_TAC[CROSS; EXTENSION; IN_ELIM_PAIR_THM; FORALL_PAIR_THM; IN_UNIV]);;

export_namedthm CROSS_UNIV "CROSS_UNIV";;

let FINITE_CROSS_EQ = prove 
 (`!s:A->bool t:B->bool.
        FINITE(s CROSS t) <=> s = {} \/ t = {} \/ FINITE s /\ FINITE t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[CROSS_EMPTY; FINITE_EMPTY] THEN
  ASM_CASES_TAC `t:B->bool = {}` THEN
  ASM_REWRITE_TAC[CROSS_EMPTY; FINITE_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[FINITE_CROSS] THEN REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP(ISPEC `FST:A#B->A` FINITE_IMAGE));
    FIRST_ASSUM(MP_TAC o MATCH_MP(ISPEC `SND:A#B->B` FINITE_IMAGE))] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS] THEN
  ASM SET_TAC[]);;

export_namedthm FINITE_CROSS_EQ "FINITE_CROSS_EQ";;

let FINITE_UNIV_PAIR = prove 
 (`FINITE(:A#A) <=> FINITE(:A)`,
  MP_TAC(ISPECL [`(:A)`; `(:A)`] FINITE_CROSS_EQ) THEN
  REWRITE_TAC[CROSS_UNIV; UNIV_NOT_EMPTY]);;

export_namedthm FINITE_UNIV_PAIR "FINITE_UNIV_PAIR";;

let INFINITE_UNIV_PAIR = prove 
 (`INFINITE(:A#A) <=> INFINITE(:A)`,
  REWRITE_TAC[INFINITE; FINITE_UNIV_PAIR]);;

export_namedthm INFINITE_UNIV_PAIR "INFINITE_UNIV_PAIR";;

let FORALL_IN_CROSS = prove 
 (`!P s t. (!z. z IN s CROSS t ==> P z) <=>
           (!x y. x IN s /\ y IN t ==> P(x,y))`,
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS]);;

export_namedthm FORALL_IN_CROSS "FORALL_IN_CROSS";;

let EXISTS_IN_CROSS = prove 
 (`!P s t. (?z. z IN s CROSS t /\ P z) <=>
           (?x y. x IN s /\ y IN t /\ P(x,y))`,
  REWRITE_TAC[EXISTS_PAIR_THM; GSYM CONJ_ASSOC; IN_CROSS]);;

export_namedthm EXISTS_IN_CROSS "EXISTS_IN_CROSS";;

let SUBSET_CROSS = prove 
 (`!s t s' t'. s CROSS t SUBSET s' CROSS t' <=>
                s = {} \/ t = {} \/ s SUBSET s' /\ t SUBSET t'`,
  SIMP_TAC[CROSS; EXTENSION; IN_ELIM_PAIR_THM; SUBSET;
   FORALL_PAIR_THM; IN_CROSS; NOT_IN_EMPTY] THEN MESON_TAC[]);;

export_namedthm SUBSET_CROSS "SUBSET_CROSS";;

let CROSS_MONO = prove 
 (`!s t s' t'. s SUBSET s' /\ t SUBSET t' ==> s CROSS t SUBSET s' CROSS t'`,
  SIMP_TAC[SUBSET_CROSS]);;

export_namedthm CROSS_MONO "CROSS_MONO";;

let CROSS_EQ = prove 
 (`!s s':A->bool t t':B->bool.
        s CROSS t = s' CROSS t' <=>
        (s = {} \/ t = {}) /\ (s' = {} \/ t' = {}) \/ s = s' /\ t = t'`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_CROSS] THEN SET_TAC[]);;

export_namedthm CROSS_EQ "CROSS_EQ";;

let IMAGE_FST_CROSS = prove 
 (`!s:A->bool t:B->bool.
        IMAGE FST (s CROSS t) = if t = {} then {} else s`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[CROSS_EMPTY; IMAGE_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[EXISTS_IN_CROSS; FST] THEN ASM SET_TAC[]);;

export_namedthm IMAGE_FST_CROSS "IMAGE_FST_CROSS";;

let IMAGE_SND_CROSS = prove 
 (`!s:A->bool t:B->bool.
        IMAGE SND (s CROSS t) = if s = {} then {} else t`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[CROSS_EMPTY; IMAGE_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[EXISTS_IN_CROSS; SND] THEN ASM SET_TAC[]);;

export_namedthm IMAGE_SND_CROSS "IMAGE_SND_CROSS";;

let IMAGE_PAIRED_CROSS = prove 
 (`!(f:A->B) (g:C->D) s t.
         IMAGE (\(x,y). f x,g y) (s CROSS t) = (IMAGE f s) CROSS (IMAGE g t)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS; FORALL_PAIR_THM;
              PAIR_EQ] THEN
  MESON_TAC[]);;

export_namedthm IMAGE_PAIRED_CROSS "IMAGE_PAIRED_CROSS";;

let CROSS_INTER = prove 
 (`(!s t u. s CROSS (t INTER u) = (s CROSS t) INTER (s CROSS u)) /\
   (!s t u. (s INTER t) CROSS u = (s CROSS u) INTER (t CROSS u))`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_INTER; IN_CROSS] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

export_namedthm CROSS_INTER "CROSS_INTER";;

let CROSS_UNION = prove 
 (`(!s t u. s CROSS (t UNION u) = (s CROSS t) UNION (s CROSS u)) /\
   (!s t u. (s UNION t) CROSS u = (s CROSS u) UNION (t CROSS u))`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_UNION; IN_CROSS] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

export_namedthm CROSS_UNION "CROSS_UNION";;

let CROSS_DIFF = prove 
 (`(!s t u. s CROSS (t DIFF u) = (s CROSS t) DIFF (s CROSS u)) /\
   (!s t u. (s DIFF t) CROSS u = (s CROSS u) DIFF (t CROSS u))`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_DIFF; IN_CROSS] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

export_namedthm CROSS_DIFF "CROSS_DIFF";;

let INTER_CROSS = prove 
 (`!s s' t t'.
      (s CROSS t) INTER (s' CROSS t') = (s INTER s') CROSS (t INTER t')`,
  REWRITE_TAC[EXTENSION; IN_INTER; FORALL_PAIR_THM; IN_CROSS] THEN
  CONV_TAC TAUT);;

export_namedthm INTER_CROSS "INTER_CROSS";;

let CROSS_UNIONS_UNIONS,CROSS_UNIONS = (CONJ_PAIR o prove)
 (`(!f g. (UNIONS f) CROSS (UNIONS g) =
          UNIONS {s CROSS t | s IN f /\ t IN g}) /\
   (!s f. s CROSS (UNIONS f) = UNIONS {s CROSS t | t IN f}) /\
   (!f t. (UNIONS f) CROSS t = UNIONS {s CROSS t | s IN f})`,
  REWRITE_TAC[UNIONS_GSPEC; EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM;
              IN_CROSS] THEN
  SET_TAC[]);;

export_namedthm CROSS_UNIONS_UNIONS "CROSS_UNIONS_UNIONS";;
export_namedthm CROSS_UNIONS "CROSS_UNIONS";;

let CROSS_INTERS_INTERS,CROSS_INTERS = (CONJ_PAIR o prove)
 (`(!f g. (INTERS f) CROSS (INTERS g) =
          if f = {} then INTERS {UNIV CROSS t | t IN g}
          else if g = {} then INTERS {s CROSS UNIV | s IN f}
          else INTERS {s CROSS t | s IN f /\ t IN g}) /\
   (!s f. s CROSS (INTERS f) =
          if f = {} then s CROSS UNIV else INTERS {s CROSS t | t IN f}) /\
   (!f t. (INTERS f) CROSS t =
          if f = {} then UNIV CROSS t else INTERS {s CROSS t | s IN f})`,
  REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[INTERS_GSPEC; EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM;
                  IN_CROSS; NOT_IN_EMPTY] THEN
  ASM SET_TAC[]);;
  
export_namedthm CROSS_INTERS_INTERS "CROSS_INTERS_INTERS";;
export_namedthm CROSS_INTERS "CROSS_INTERS";;


let DISJOINT_CROSS = prove 
 (`!s:A->bool t:B->bool s' t'.
        DISJOINT (s CROSS t) (s' CROSS t') <=>
        DISJOINT s s' \/ DISJOINT t t'`,
  REWRITE_TAC[DISJOINT; INTER_CROSS; CROSS_EQ_EMPTY]);;

export_namedthm DISJOINT_CROSS "DISJOINT_CROSS";;

(* ------------------------------------------------------------------------- *)
(* "Extensional" functions, mapping to a fixed value ARB outside the domain. *)
(* Even though these are still total, they're a conveniently better model    *)
(* of the partial function space (e.g. the space has the right cardinality). *)
(* ------------------------------------------------------------------------- *)

export_theory "set-function-extensional";;

let ARB = new_definition 
  `ARB = (@x:A. F)`;;

export_namedthm ARB "ARB";;

let EXTENSIONAL = new_definition 
  `EXTENSIONAL s = {f:A->B | !x. ~(x IN s) ==> f x = ARB}`;;

export_namedthm EXTENSIONAL "EXTENSIONAL";;

let IN_EXTENSIONAL = prove 
 (`!s f:A->B. f IN EXTENSIONAL s <=> (!x. ~(x IN s) ==> f x = ARB)`,
  REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM]);;

export_namedthm IN_EXTENSIONAL "IN_EXTENSIONAL";;

let IN_EXTENSIONAL_UNDEFINED = prove 
 (`!s f:A->B x. f IN EXTENSIONAL s /\ ~(x IN s) ==> f x = ARB`,
  SIMP_TAC[IN_EXTENSIONAL]);;

export_namedthm IN_EXTENSIONAL_UNDEFINED "IN_EXTENSIONAL_UNDEFINED";;

let EXTENSIONAL_EMPTY = prove 
 (`EXTENSIONAL {} = {\x:A. ARB:B}`,
  REWRITE_TAC[EXTENSION; IN_EXTENSIONAL; IN_SING; NOT_IN_EMPTY] THEN
  REWRITE_TAC[FUN_EQ_THM]);;

export_namedthm EXTENSIONAL_EMPTY "EXTENSIONAL_EMPTY";;

let EXTENSIONAL_UNIV = prove 
 (`!f. EXTENSIONAL (:A) f`,
  REWRITE_TAC[EXTENSIONAL; IN_UNIV; IN_ELIM_THM]);;

export_namedthm EXTENSIONAL_UNIV "EXTENSIONAL_UNIV";;

let EXTENSIONAL_EQ = prove 
 (`!s f g:A->B.
     f IN EXTENSIONAL s /\ g IN EXTENSIONAL s /\ (!x. x IN s ==> f x = g x)
     ==> f = g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  ASM_CASES_TAC `x:A IN s` THENL
  [ASM_SIMP_TAC[]; ASM_MESON_TAC[IN_EXTENSIONAL_UNDEFINED]]);;

export_namedthm EXTENSIONAL_EQ "EXTENSIONAL_EQ";;

(* ------------------------------------------------------------------------- *)
(* Restriction of a function to an EXTENSIONAL one on a subset.              *)
(* ------------------------------------------------------------------------- *)

export_theory "set-function-restriction";;

let RESTRICTION = new_definition 
  `RESTRICTION s (f:A->B) x = if x IN s then f x else ARB`;;

export_namedthm RESTRICTION "RESTRICTION";;

let RESTRICTION_DEFINED = prove 
 (`!s f:A->B x. x IN s ==> RESTRICTION s f x = f x`,
  SIMP_TAC[RESTRICTION]);;

export_namedthm RESTRICTION_DEFINED "RESTRICTION_DEFINED";;

let RESTRICTION_UNDEFINED = prove 
 (`!s f:A->B x. ~(x IN s) ==> RESTRICTION s f x = ARB`,
  SIMP_TAC[RESTRICTION]);;

export_namedthm RESTRICTION_UNDEFINED "RESTRICTION_UNDEFINED";;

let RESTRICTION_EQ = prove 
 (`!s f:A->B x y. x IN s /\ f x = y ==> RESTRICTION s f x = y`,
  SIMP_TAC[RESTRICTION_DEFINED]);;

export_namedthm RESTRICTION_EQ "RESTRICTION_EQ";;

let RESTRICTION_IN_EXTENSIONAL = prove 
 (`!s f:A->B. RESTRICTION s f IN EXTENSIONAL s`,
  SIMP_TAC[IN_EXTENSIONAL; RESTRICTION]);;

export_namedthm RESTRICTION_IN_EXTENSIONAL "RESTRICTION_IN_EXTENSIONAL";;

let RESTRICTION_EXTENSION = prove 
 (`!s f g:A->B. RESTRICTION s f = RESTRICTION s g <=>
                (!x. x IN s ==> f x = g x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RESTRICTION; FUN_EQ_THM] THEN MESON_TAC[]);;

export_namedthm RESTRICTION_EXTENSION "RESTRICTION_EXTENSION";;

let RESTRICTION_FIXPOINT = prove 
 (`!s f:A->B. RESTRICTION s f = f <=> f IN EXTENSIONAL s`,
  REWRITE_TAC[IN_EXTENSIONAL; FUN_EQ_THM; RESTRICTION] THEN MESON_TAC[]);;

export_namedthm RESTRICTION_FIXPOINT "RESTRICTION_FIXPOINT";;

let RESTRICTION_RESTRICTION = prove 
 (`!s t f:A->B.
        s SUBSET t ==> RESTRICTION s (RESTRICTION t f) = RESTRICTION s f`,
  REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN SET_TAC[]);;

export_namedthm RESTRICTION_RESTRICTION "RESTRICTION_RESTRICTION";;

let RESTRICTION_IDEMP = prove 
 (`!s f:A->B. RESTRICTION s (RESTRICTION s f) = RESTRICTION s f`,
  REWRITE_TAC[RESTRICTION_FIXPOINT; RESTRICTION_IN_EXTENSIONAL]);;

export_namedthm RESTRICTION_IDEMP "RESTRICTION_IDEMP";;

let IMAGE_RESTRICTION = prove 
 (`!f:A->B s t. s SUBSET t ==> IMAGE (RESTRICTION t f) s = IMAGE f s`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; RESTRICTION] THEN SET_TAC[]);;

export_namedthm IMAGE_RESTRICTION "IMAGE_RESTRICTION";;

let RESTRICTION_COMPOSE_RIGHT = prove 
 (`!f:A->B g:B->C s.
        RESTRICTION s (g o RESTRICTION s f) =
        RESTRICTION s (g o f)`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; RESTRICTION] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN SET_TAC[]);;

export_namedthm RESTRICTION_COMPOSE_RIGHT "RESTRICTION_COMPOSE_RIGHT";;

let RESTRICTION_COMPOSE_LEFT = prove 
 (`!f:A->B g:B->C s t.
        IMAGE f s SUBSET t
        ==> RESTRICTION s (RESTRICTION t g o f) =
            RESTRICTION s (g o f)`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; RESTRICTION] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN SET_TAC[]);;

export_namedthm RESTRICTION_COMPOSE_LEFT "RESTRICTION_COMPOSE_LEFT";;

let RESTRICTION_COMPOSE = prove 
 (`!f:A->B g:B->C s t.
        IMAGE f s SUBSET t
        ==> RESTRICTION s (RESTRICTION t g o RESTRICTION s f) =
            RESTRICTION s (g o f)`,
  SIMP_TAC[RESTRICTION_COMPOSE_LEFT; RESTRICTION_COMPOSE_RIGHT]);;

export_namedthm RESTRICTION_COMPOSE "RESTRICTION_COMPOSE";;

(* ------------------------------------------------------------------------- *)
(* General Cartesian product / dependent function space.                     *)
(* ------------------------------------------------------------------------- *)

export_theory "set-cart-prod";;

let cartesian_product = new_definition 
 `cartesian_product k s =
        {f:K->A | EXTENSIONAL k f /\ !i. i IN k ==> f i IN s i}`;;

export_namedthm cartesian_product "cartesian_product";;

let IN_CARTESIAN_PRODUCT = prove 
 (`!k s (x:K->A).
        x IN cartesian_product k s <=>
        EXTENSIONAL k x /\ (!i. i IN k ==> x i IN s i)`,
  REWRITE_TAC[cartesian_product; IN_ELIM_THM]);;

export_namedthm IN_CARTESIAN_PRODUCT "IN_CARTESIAN_PRODUCT";;

let CARTESIAN_PRODUCT = prove 
 (`!k s. cartesian_product k s =
         {f:K->A | !i. f i IN (if i IN k then s i else {ARB})}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[cartesian_product; IN_ELIM_THM; EXTENSIONAL] THEN
  MESON_TAC[IN_SING]);;

export_namedthm CARTESIAN_PRODUCT "CARTESIAN_PRODUCT";;

let RESTRICTION_IN_CARTESIAN_PRODUCT = prove 
 (`!k s (f:K->A).
        RESTRICTION k f IN cartesian_product k s <=>
        !i. i IN k ==> (f i) IN (s i)`,
  REWRITE_TAC[RESTRICTION; cartesian_product; EXTENSIONAL; IN_ELIM_THM] THEN
  SET_TAC[]);;

export_namedthm RESTRICTION_IN_CARTESIAN_PRODUCT "RESTRICTION_IN_CARTESIAN_PRODUCT";;

let CARTESIAN_PRODUCT_AS_RESTRICTIONS = prove 
 (`!k (s:K->A->bool).
      cartesian_product k s =
      {RESTRICTION k f |f| !i. i IN k ==> f i IN s i}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
  X_GEN_TAC `x:K->A` THEN
  REWRITE_TAC[cartesian_product; IN_ELIM_THM; EXTENSIONAL] THEN
  STRIP_TAC THEN EXISTS_TAC `x:K->A` THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN ASM_MESON_TAC[]);;

export_namedthm CARTESIAN_PRODUCT_AS_RESTRICTIONS "CARTESIAN_PRODUCT_AS_RESTRICTIONS";;

let CARTESIAN_PRODUCT_EQ_EMPTY = prove 
 (`!k s:K->A->bool.
        cartesian_product k s = {} <=> ?i. i IN k /\ s i = {}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  REWRITE_TAC[SET_RULE
   `(?i. i IN k /\ s i = {}) <=> ~(!i. ?a. i IN k ==> a IN s i)`] THEN
  REWRITE_TAC[SKOLEM_THM; NOT_EXISTS_THM; cartesian_product] THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `f:K->A` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\i. if i IN k then (f:K->A) i else ARB`) THEN
  REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM] THEN SIMP_TAC[]);;

export_namedthm CARTESIAN_PRODUCT_EQ_EMPTY "CARTESIAN_PRODUCT_EQ_EMPTY";;

let CARTESIAN_PRODUCT_EMPTY = prove 
 (`!s. cartesian_product {} s = {(\i. ARB)}`,
  REWRITE_TAC[CARTESIAN_PRODUCT; NOT_IN_EMPTY; EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN REWRITE_TAC[FUN_EQ_THM]);;

export_namedthm CARTESIAN_PRODUCT_EMPTY "CARTESIAN_PRODUCT_EMPTY";;

let CARTESIAN_PRODUCT_EQ_MEMBERS = prove 
 (`!k s x y:K->A.
        x IN cartesian_product k s /\ y IN cartesian_product k s /\
        (!i. i IN k ==> x i = y i)
        ==> x = y`,
  REWRITE_TAC[cartesian_product; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EXTENSIONAL_EQ THEN
  EXISTS_TAC `k:K->bool` THEN ASM_REWRITE_TAC[IN]);;

export_namedthm CARTESIAN_PRODUCT_EQ_MEMBERS "CARTESIAN_PRODUCT_EQ_MEMBERS";;

let CARTESIAN_PRODUCT_EQ_MEMBERS_EQ = prove 
 (`!k s x y.
        x IN cartesian_product k s /\
        y IN cartesian_product k s
        ==> (x = y <=> !i. i IN k ==> x i = y i)`,
  MESON_TAC[CARTESIAN_PRODUCT_EQ_MEMBERS]);;

export_namedthm CARTESIAN_PRODUCT_EQ_MEMBERS_EQ "CARTESIAN_PRODUCT_EQ_MEMBERS_EQ";;

let SUBSET_CARTESIAN_PRODUCT = prove 
 (`!k s t:K->A->bool.
        cartesian_product k s SUBSET cartesian_product k t <=>
        cartesian_product k s = {} \/ !i. i IN k ==> s i SUBSET t i`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `cartesian_product k (s:K->A->bool) = {}` THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
  REWRITE_TAC[SUBSET; cartesian_product; IN_ELIM_THM] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE RAND_CONV [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
  REWRITE_TAC[SET_RULE
   `~(?i. i IN k /\ s i = {}) <=> (!i. ?a. i IN k ==> a IN s i)`] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:K->A` THEN DISCH_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `i:K` THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `(\j. if j IN k then if j = i then x else z j else ARB):K->A`) THEN
  REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM] THEN SIMP_TAC[] THEN
  ASM_MESON_TAC[]);;

export_namedthm SUBSET_CARTESIAN_PRODUCT "SUBSET_CARTESIAN_PRODUCT";;

let CARTESIAN_PRODUCT_EQ = prove 
 (`!k s t:K->A->bool.
        cartesian_product k s = cartesian_product k t <=>
        cartesian_product k s = {} /\ cartesian_product k t = {} \/
        !i. i IN k ==> s i = t i`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `!i. i IN k ==> (s:K->A->bool) i = t i` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[cartesian_product; EXTENSION; IN_ELIM_THM];
    ASM_CASES_TAC `cartesian_product k (t:K->A->bool) = {}` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `cartesian_product k (s:K->A->bool) = {}` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_CARTESIAN_PRODUCT] THEN
    ASM SET_TAC[]]);;

export_namedthm CARTESIAN_PRODUCT_EQ "CARTESIAN_PRODUCT_EQ";;

let INTER_CARTESIAN_PRODUCT = prove 
 (`!k s t:K->A->bool.
        (cartesian_product k s) INTER (cartesian_product k t) =
        cartesian_product k (\i. s i INTER t i)`,
  REWRITE_TAC[EXTENSION; cartesian_product; IN_INTER; IN_ELIM_THM] THEN
  SET_TAC[]);;

export_namedthm INTER_CARTESIAN_PRODUCT "INTER_CARTESIAN_PRODUCT";;

let CARTESIAN_PRODUCT_UNIV = prove 
 (`cartesian_product (:K) (\i. (:A)) = (:K->A)`,
  REWRITE_TAC[EXTENSION; IN_UNIV; cartesian_product; IN_ELIM_THM] THEN
  REWRITE_TAC[EXTENSIONAL_UNIV]);;

export_namedthm CARTESIAN_PRODUCT_UNIV "CARTESIAN_PRODUCT_UNIV";;

let CARTESIAN_PRODUCT_SINGS = prove 
 (`!k x:K->A. EXTENSIONAL k x ==> cartesian_product k (\i. {x i}) = {x}`,
  REWRITE_TAC[cartesian_product; IN_SING] THEN
  REWRITE_TAC[EXTENSION; EXTENSIONAL; IN_ELIM_THM; IN_SING] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]);;

export_namedthm CARTESIAN_PRODUCT_SINGS "CARTESIAN_PRODUCT_SINGS";;

let CARTESIAN_PRODUCT_SINGS_GEN = prove 
 (`!k x. cartesian_product k (\i. {x i}) = {RESTRICTION k x}`,
  REWRITE_TAC[cartesian_product; IN_SING] THEN
  REWRITE_TAC[EXTENSION; EXTENSIONAL; IN_ELIM_THM; IN_SING] THEN
  REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN MESON_TAC[]);;

export_namedthm CARTESIAN_PRODUCT_SINGS_GEN "CARTESIAN_PRODUCT_SINGS_GEN";;

let IMAGE_PROJECTION_CARTESIAN_PRODUCT = prove 
 (`!k s:K->A->bool i.
        IMAGE (\x. x i) (cartesian_product k s) =
        if cartesian_product k s = {} then {}
        else if i IN k then s i else {ARB}`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `cartesian_product k (s:K->A->bool) = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
  SIMP_TAC[CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE RAND_CONV [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
  REWRITE_TAC[SET_RULE
   `~(?i. i IN k /\ s i = {}) <=> (!i. ?a. i IN k ==> a IN s i)`] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:K->A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  EXISTS_TAC
   `\j. if j = i then x else if j IN k then (z:K->A) j else ARB` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_SING]);;

export_namedthm IMAGE_PROJECTION_CARTESIAN_PRODUCT "IMAGE_PROJECTION_CARTESIAN_PRODUCT";;

let FORALL_CARTESIAN_PRODUCT_ELEMENTS = prove 
 (`!P k s:K->A->bool.
        (!z i. z IN cartesian_product k s /\ i IN k ==> P i (z i)) <=>
        cartesian_product k s = {} \/
        (!i x. i IN k /\ x IN s i ==> P i x)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `cartesian_product k (s:K->A->bool) = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC[cartesian_product; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_TAC; MESON_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
   [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; SET_RULE
     `~(?i. i IN k /\ s i = {}) <=> (!i. ?x. i IN k ==> x IN s i)`] THEN
  X_GEN_TAC `z:K->A` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:K`; `x:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\j. if j = i then x else if j IN k then (z:K->A) j else ARB`; `i:K`]) THEN
  ASM_REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

export_namedthm FORALL_CARTESIAN_PRODUCT_ELEMENTS "FORALL_CARTESIAN_PRODUCT_ELEMENTS";;

let FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ = prove 
 (`!P k s.
        ~(cartesian_product k s = {})
        ==> ((!i x. i IN k /\ x IN s i ==> P i x) <=>
             !z i. z IN cartesian_product k s /\ i IN k ==> P i (z i))`,
  SIMP_TAC[FORALL_CARTESIAN_PRODUCT_ELEMENTS]);;

export_namedthm FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ "FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ";;

(* ------------------------------------------------------------------------- *)
(* Product of a family of maps.                                              *)
(* ------------------------------------------------------------------------- *)

export_theory "set-prod-family";;

let product_map = new_definition 
 `product_map k (f:K->A->B) = \x. RESTRICTION k (\i. f i (x i))`;;

export_namedthm product_map "product_map";;

let PRODUCT_MAP_RESTRICTION = prove 
 (`!(f:K->A->B) k x.
        product_map k f (RESTRICTION k x) = RESTRICTION k (\i. f i (x i))`,
  SIMP_TAC[product_map; RESTRICTION; o_THM; FUN_EQ_THM]);;

export_namedthm PRODUCT_MAP_RESTRICTION "PRODUCT_MAP_RESTRICTION";;

let IMAGE_PRODUCT_MAP = prove 
 (`!(f:K->A->B) k s.
        IMAGE (product_map k f) (cartesian_product k s) =
        cartesian_product k (\i. IMAGE (f i) (s i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CARTESIAN_PRODUCT_AS_RESTRICTIONS] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[product_map; GSYM IMAGE_o; o_DEF] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `g:K->B` THEN
  REWRITE_TAC[IN_IMAGE; RESTRICTION; IN_ELIM_THM] THEN
  EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[RESTRICTION_EXTENSION] THEN
  ASM SET_TAC[]);;

export_namedthm IMAGE_PRODUCT_MAP "IMAGE_PRODUCT_MAP";;

(* ------------------------------------------------------------------------- *)
(* Disjoint union construction for a family of sets.                         *)
(* ------------------------------------------------------------------------- *)

export_theory "set-disjoint-union-family";;

let disjoint_union = new_definition 
 `disjoint_union (k:K->bool) (s:K->A->bool) = { (i,x) | i IN k /\ x IN s i}`;;

export_namedthm disjoint_union "disjoint_union";;

let SUBSET_DISJOINT_UNION = prove 
 (`!k (s:K->A->bool) t.
        disjoint_union k s SUBSET disjoint_union k t <=>
        !i. i IN k ==> s i SUBSET t i`,
  REWRITE_TAC[SUBSET; disjoint_union; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM] THEN SET_TAC[]);;

export_namedthm SUBSET_DISJOINT_UNION "SUBSET_DISJOINT_UNION";;

let DISJOINT_UNION_EQ = prove 
 (`!k (s:K->A->bool) t.
        disjoint_union k s = disjoint_union k t <=>
        !i. i IN k ==> s i = t i`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_DISJOINT_UNION] THEN
  SET_TAC[]);;

export_namedthm DISJOINT_UNION_EQ "DISJOINT_UNION_EQ";;

let SUBSET_DISJOINT_UNION_EXISTS = prove 
 (`!k (s:K->A->bool) u.
        u SUBSET disjoint_union k s <=>
        ?t. u = disjoint_union k t /\ !i. i IN k ==> t i SUBSET s i`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC; MESON_TAC[SUBSET_DISJOINT_UNION]] THEN
  EXISTS_TAC `\i. {x | (i,x) IN (u:K#A->bool)}` THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[SUBSET; EXTENSION] THEN
  REWRITE_TAC[disjoint_union; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  SET_TAC[]);;

export_namedthm SUBSET_DISJOINT_UNION_EXISTS "SUBSET_DISJOINT_UNION_EXISTS";;

let INTER_DISJOINT_UNION = prove 
 (`!k s t:K->A->bool.
        (disjoint_union k s) INTER (disjoint_union k t) =
        disjoint_union k (\i. s i INTER t i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; disjoint_union; IN_INTER; IN_ELIM_THM] THEN
  MESON_TAC[PAIR_EQ]);;

export_namedthm INTER_DISJOINT_UNION "INTER_DISJOINT_UNION";;

let UNION_DISJOINT_UNION = prove 
 (`!k s t:K->A->bool.
        (disjoint_union k s) UNION (disjoint_union k t) =
        disjoint_union k (\i. s i UNION t i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; disjoint_union; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[PAIR_EQ]);;

export_namedthm UNION_DISJOINT_UNION "UNION_DISJOINT_UNION";;

let DISJOINT_UNION_EQ_EMPTY = prove 
 (`!k s:K->A->bool.
        disjoint_union k s = {} <=> !i. i IN k ==> s i = {}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; disjoint_union; IN_ELIM_PAIR_THM;
              NOT_IN_EMPTY] THEN
  SET_TAC[]);;

export_namedthm DISJOINT_UNION_EQ_EMPTY "DISJOINT_UNION_EQ_EMPTY";;

let DISJOINT_DISJOINT_UNION = prove 
 (`!k s t:K->A->bool.
        DISJOINT (disjoint_union k s) (disjoint_union k t) =
        !i. i IN k ==> DISJOINT (s i) (t i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DISJOINT; INTER_DISJOINT_UNION; DISJOINT_UNION_EQ_EMPTY]);;

export_namedthm DISJOINT_DISJOINT_UNION "DISJOINT_DISJOINT_UNION";;

(* ------------------------------------------------------------------------- *)
(* Cardinality of functions with bounded domain (support) and range.         *)
(* ------------------------------------------------------------------------- *)

export_theory "set-function-bounded";;

let HAS_SIZE_FUNSPACE = prove 
 (`!d n t:B->bool m s:A->bool.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | (!x. x IN s ==> f(x) IN t) /\ (!x. ~(x IN s) ==> (f x = d))}
            HAS_SIZE (n EXP m)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[HAS_SIZE_CLAUSES] THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; EXP] THEN
    CONV_TAC HAS_SIZE_CONV THEN EXISTS_TAC `(\x. d):A->B` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN REWRITE_TAC[FUN_EQ_THM];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`s0:A->bool`; `a:A`; `s:A->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:A->bool`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{f:A->B | (!x. x IN a INSERT s ==> f x IN t) /\
              (!x. ~(x IN a INSERT s) ==> (f x = d))} =
    IMAGE (\(b,g) x. if x = a then b else g(x))
          {b,g | b IN t /\
                 g IN {f | (!x. x IN s ==> f x IN t) /\
                           (!x. ~(x IN s) ==> (f x = d))}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_THM;
                EXISTS_PAIR_THM] THEN
    REWRITE_TAC[PAIR_EQ; CONJ_ASSOC; ONCE_REWRITE_RULE[CONJ_SYM]
     UNWIND_THM1] THEN
    X_GEN_TAC `f:A->B` THEN REWRITE_TAC[IN_INSERT] THEN EQ_TAC THENL
     [STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [`(f:A->B) a`; `\x. if x IN s then (f:A->B) x else d`] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `b:B` (X_CHOOSE_THEN `g:A->B`
        STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_SIMP_TAC[EXP; HAS_SIZE_PRODUCT] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; PAIR_EQ; CONJ_ASSOC] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    ASM_MESON_TAC[]]);;

export_namedthm HAS_SIZE_FUNSPACE "HAS_SIZE_FUNSPACE";;

let CARD_FUNSPACE = prove 
 (`!s t. FINITE s /\ FINITE t
         ==> (CARD {f | (!x. x IN s ==> f(x) IN t) /\
                        (!x. ~(x IN s) ==> (f x = d))} =
              (CARD t) EXP (CARD s))`,
  MESON_TAC[HAS_SIZE_FUNSPACE; HAS_SIZE]);;

export_namedthm CARD_FUNSPACE "CARD_FUNSPACE";;

let FINITE_FUNSPACE = prove 
 (`!s t. FINITE s /\ FINITE t
         ==> FINITE {f | (!x. x IN s ==> f(x) IN t) /\
                         (!x. ~(x IN s) ==> (f x = d))}`,
  MESON_TAC[HAS_SIZE_FUNSPACE; HAS_SIZE]);;

export_namedthm FINITE_FUNSPACE "FINITE_FUNSPACE";;

let HAS_SIZE_FUNSPACE_UNIV = prove 
 (`!m n. (:A) HAS_SIZE m /\ (:B) HAS_SIZE n ==> (:A->B) HAS_SIZE (n EXP m)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_FUNSPACE) THEN
  REWRITE_TAC[IN_UNIV; UNIV_GSPEC]);;

export_namedthm HAS_SIZE_FUNSPACE_UNIV "HAS_SIZE_FUNSPACE_UNIV";;

let CARD_FUNSPACE_UNIV = prove 
 (`FINITE(:A) /\ FINITE(:B) ==> CARD(:A->B) = CARD(:B) EXP CARD(:A)`,
  MESON_TAC[HAS_SIZE_FUNSPACE_UNIV; HAS_SIZE]);;

export_namedthm CARD_FUNSPACE_UNIV "CARD_FUNSPACE_UNIV";;

let FINITE_FUNSPACE_UNIV = prove 
 (`FINITE(:A) /\ FINITE(:B) ==> FINITE(:A->B)`,
  MESON_TAC[HAS_SIZE_FUNSPACE_UNIV; HAS_SIZE]);;

export_namedthm FINITE_FUNSPACE_UNIV "FINITE_FUNSPACE_UNIV";;

(* ------------------------------------------------------------------------- *)
(* Cardinality of type bool.                                                 *)
(* ------------------------------------------------------------------------- *)

export_theory "set-card-bool";;

let HAS_SIZE_BOOL = prove 
 (`(:bool) HAS_SIZE 2`,
  SUBGOAL_THEN `(:bool) = {F,T}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIV; IN_INSERT] THEN CONV_TAC TAUT;
    SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; ARITH;
             IN_SING; NOT_IN_EMPTY]]);;

export_namedthm HAS_SIZE_BOOL "HAS_SIZE_BOOL";;

let CARD_BOOL = prove 
 (`CARD(:bool) = 2`,
  MESON_TAC[HAS_SIZE_BOOL; HAS_SIZE]);;

export_namedthm CARD_BOOL "CARD_BOOL";;

let FINITE_BOOL = prove 
 (`FINITE(:bool)`,
  MESON_TAC[HAS_SIZE_BOOL; HAS_SIZE]);;

export_namedthm FINITE_BOOL "FINITE_BOOL";;

(* ------------------------------------------------------------------------- *)
(* Hence cardinality of powerset.                                            *)
(* ------------------------------------------------------------------------- *)

export_theory "set-card-powerset";;

let HAS_SIZE_POWERSET = prove 
 (`!(s:A->bool) n. s HAS_SIZE n ==> {t | t SUBSET s} HAS_SIZE (2 EXP n)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `{t | t SUBSET s} =
    {f | (!x:A. x IN s ==> f(x) IN UNIV) /\ (!x. ~(x IN s) ==> (f x = F))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV; SUBSET; IN; CONTRAPOS_THM];
    MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC HAS_SIZE_CONV THEN MAP_EVERY EXISTS_TAC [`T`; `F`] THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC TAUT]);;

export_namedthm HAS_SIZE_POWERSET "HAS_SIZE_POWERSET";;

let CARD_POWERSET = prove 
 (`!s:A->bool. FINITE s ==> (CARD {t | t SUBSET s} = 2 EXP (CARD s))`,
  MESON_TAC[HAS_SIZE_POWERSET; HAS_SIZE]);;

export_namedthm CARD_POWERSET "CARD_POWERSET";;

let FINITE_POWERSET = prove 
 (`!s:A->bool. FINITE s ==> FINITE {t | t SUBSET s}`,
  MESON_TAC[HAS_SIZE_POWERSET; HAS_SIZE]);;

export_namedthm FINITE_POWERSET "FINITE_POWERSET";;

let FINITE_POWERSET_EQ = prove 
 (`!s:A->bool. FINITE {t | t SUBSET s} <=> FINITE s`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[FINITE_POWERSET] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(IMAGE (\x:A. {x}) s)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        FINITE_SUBSET)) THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_SING];
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
    SET_TAC[]]);;

export_namedthm FINITE_POWERSET_EQ "FINITE_POWERSET_EQ";;

let FINITE_UNIONS = prove 
 (`!s:(A->bool)->bool.
        FINITE(UNIONS s) <=> FINITE s /\ (!t. t IN s ==> FINITE t)`,
  GEN_TAC THEN ASM_CASES_TAC `FINITE(s:(A->bool)->bool)` THEN
  ASM_SIMP_TAC[FINITE_FINITE_UNIONS] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_POWERSET) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN SET_TAC[]);;

export_namedthm FINITE_UNIONS "FINITE_UNIONS";;

let POWERSET_CLAUSES = prove 
 (`{s | s SUBSET {}} = {{}} /\
   (!a:A t. {s | s SUBSET (a INSERT t)} =
            {s | s SUBSET t} UNION IMAGE (\s. a INSERT s) {s | s SUBSET t})`,
  REWRITE_TAC[SUBSET_INSERT_DELETE; SUBSET_EMPTY; SING_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[UNION_SUBSET] THEN
  ONCE_REWRITE_TAC[SUBSET] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNION; IN_IMAGE] THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  X_GEN_TAC `s:A->bool` THEN
  ASM_CASES_TAC `(a:A) IN s` THENL [ALL_TAC; ASM SET_TAC[]] THEN
  STRIP_TAC THEN DISJ2_TAC THEN EXISTS_TAC `s DELETE (a:A)` THEN
  ASM SET_TAC[]);;

export_namedthm POWERSET_CLAUSES "POWERSET_CLAUSES";;

let FINITE_IMAGE_INFINITE = prove 
 (`!f:A->B s.
        INFINITE s /\ FINITE(IMAGE f s)
        ==> ?a. a IN s /\ INFINITE {x | x IN s /\ f x = f a}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; INFINITE; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `s = UNIONS {{x | x IN s /\ (f:A->B) x = y} |y| y IN IMAGE f s}`
  SUBST1_TAC THENL [REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_UNIONS; SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE]);;

export_namedthm FINITE_IMAGE_INFINITE "FINITE_IMAGE_INFINITE";;

let FINITE_RESTRICTED_FUNSPACE = prove 
 (`!s:A->bool t:B->bool k.
        FINITE s /\ FINITE t
        ==> FINITE {f | IMAGE f s SUBSET t /\ {x | ~(f x = k x)} SUBSET s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `IMAGE (\u:(A#B)->bool x. if ?y. (x,y) IN u then @y. (x,y) IN u else k x)
          {u | u SUBSET (s CROSS t)}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_CROSS; FINITE_IMAGE] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
  X_GEN_TAC `f:A->B` THEN STRIP_TAC THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  EXISTS_TAC `IMAGE (\x. x,(f:A->B) x) {x | ~(f x = k x)}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_CROSS] THEN
    ASM SET_TAC[]] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; PAIR_EQ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM1; UNWIND_THM2] THEN
  ASM_CASES_TAC `(f:A->B) x = k x` THEN ASM_REWRITE_TAC[]);;

export_namedthm FINITE_RESTRICTED_FUNSPACE "FINITE_RESTRICTED_FUNSPACE";;

(* ------------------------------------------------------------------------- *)
(* Set of numbers is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

export_theory "set-card-num";;

let NUMSEG_CLAUSES_LT = prove 
 (`{i | i < 0} = {} /\
   (!k. {i | i < SUC k} = k INSERT {i | i < k})`,
  REWRITE_TAC[LT] THEN SET_TAC[]);;

export_namedthm NUMSEG_CLAUSES_LT "NUMSEG_CLAUSES_LT";;

let HAS_SIZE_NUMSEG_LT = prove 
 (`!n. {m | m < n} HAS_SIZE n`,
  REWRITE_TAC[HAS_SIZE] THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[NUMSEG_CLAUSES_LT; FINITE_EMPTY; CARD_CLAUSES; FINITE_INSERT;
               IN_ELIM_THM; LT_REFL]);;

export_namedthm HAS_SIZE_NUMSEG_LT "HAS_SIZE_NUMSEG_LT";;

let CARD_NUMSEG_LT = prove 
 (`!n. CARD {m | m < n} = n`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LT]);;

export_namedthm CARD_NUMSEG_LT "CARD_NUMSEG_LT";;

let FINITE_NUMSEG_LT = prove 
 (`!n:num. FINITE {m | m < n}`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LT]);;

export_namedthm FINITE_NUMSEG_LT "FINITE_NUMSEG_LT";;

let NUMSEG_CLAUSES_LE = prove 
 (`{i | i <= 0} = {0} /\
   (!k. {i | i <= SUC k} = SUC k INSERT {i | i <= k})`,
  REWRITE_TAC[LE] THEN SET_TAC[]);;

export_namedthm NUMSEG_CLAUSES_LE "NUMSEG_CLAUSES_LE";;

let HAS_SIZE_NUMSEG_LE = prove 
 (`!n. {m | m <= n} HAS_SIZE (n + 1)`,
  REWRITE_TAC[GSYM LT_SUC_LE; HAS_SIZE_NUMSEG_LT; ADD1]);;

export_namedthm HAS_SIZE_NUMSEG_LE "HAS_SIZE_NUMSEG_LE";;

let FINITE_NUMSEG_LE = prove 
 (`!n. FINITE {m | m <= n}`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LE]);;

export_namedthm FINITE_NUMSEG_LE "FINITE_NUMSEG_LE";;

let CARD_NUMSEG_LE = prove 
 (`!n. CARD {m | m <= n} = n + 1`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LE]);;

export_namedthm CARD_NUMSEG_LE "CARD_NUMSEG_LE";;

let num_FINITE = prove 
 (`!s:num->bool. FINITE s <=> ?a. !x. x IN s ==> x <= a`,
  GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`s:num->bool`,`s:num->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[LE_CASES; LE_TRANS];
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{m:num | m <= n}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM]]);;

export_namedthm num_FINITE "num_FINITE";;

let num_FINITE_AVOID = prove 
 (`!s:num->bool. FINITE(s) ==> ?a. ~(a IN s)`,
  MESON_TAC[num_FINITE; LT; NOT_LT]);;

export_namedthm num_FINITE_AVOID "num_FINITE_AVOID";;

let num_INFINITE_EQ = prove 
 (`!s:num->bool. INFINITE s <=> !N. ?n. N <= n /\ n IN s`,
  GEN_TAC THEN REWRITE_TAC[INFINITE; num_FINITE] THEN
  MESON_TAC[NOT_LE; LT_IMP_LE; LE_SUC_LT]);;

export_namedthm num_INFINITE_EQ "num_INFINITE_EQ";;

let num_INFINITE = prove 
 (`INFINITE(:num)`,
  REWRITE_TAC[INFINITE] THEN MESON_TAC[num_FINITE_AVOID; IN_UNIV]);;

export_namedthm num_INFINITE "num_INFINITE";;

(* ------------------------------------------------------------------------- *)
(* Set of strings is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

export_theory "set-card-strings";;

let string_INFINITE = prove 
 (`INFINITE(:string)`,
  MP_TAC num_INFINITE THEN REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
  DISCH_THEN(MP_TAC o ISPEC `LENGTH:string->num` o MATCH_MP FINITE_IMAGE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN MESON_TAC[LENGTH_REPLICATE]);;

export_namedthm string_INFINITE "string_INFINITE";;

(* ------------------------------------------------------------------------- *)
(* Non-trivial intervals of reals are infinite.                              *)
(* ------------------------------------------------------------------------- *)

export_theory "set-card-intervals";;

let FINITE_REAL_INTERVAL = prove 
 (`(!a. ~FINITE {x:real | a < x}) /\
   (!a. ~FINITE {x:real | a <= x}) /\
   (!b. ~FINITE {x:real | x < b}) /\
   (!b. ~FINITE {x:real | x <= b}) /\
   (!a b. FINITE {x:real | a < x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a < x /\ x <= b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x <= b} <=> b <= a)`,
  SUBGOAL_THEN `!a b. FINITE {x:real | a < x /\ x < b} <=> b <= a`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    ASM_CASES_TAC `a:real < b` THEN
    ASM_SIMP_TAC[REAL_ARITH `~(a:real < b) ==> ~(a < x /\ x < b)`] THEN
    REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (\n. a + (b - a) / (&n + &2)) (:num)`) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    SIMP_TAC[REAL_LT_ADDR; REAL_ARITH `a + x / y < b <=> x / y < b - a`] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_LT_LDIV_EQ; NOT_IMP;
                 REAL_ARITH `&0:real < &n + &2`] THEN
    REWRITE_TAC[REAL_ARITH `x:real < x * (n + &2) <=> &0 < x * (n + &1)`] THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_MUL; REAL_ARITH `&0:real < &n + &1`] THEN
    MP_TAC num_INFINITE THEN REWRITE_TAC[INFINITE] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
     `a < b ==> (a + (b - a) / (&n + &2) = a + (b - a) / (&m + &2) <=>
                 &n:real = &m)`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `{x:real | a < x /\ x < a + &1}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `{x:real | a < x /\ x < a + &1}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `{x:real | b - &1 < x /\ x < b}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `{x:real | b - &1 < x /\ x < b}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH
     `a:real <= x /\ x < b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = a`];
    REWRITE_TAC[REAL_ARITH
     `a:real < x /\ x <= b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = b`];
    ASM_CASES_TAC `b:real = a` THEN
    ASM_SIMP_TAC[REAL_LE_ANTISYM; REAL_LE_REFL; SING_GSPEC; FINITE_SING] THEN
    ASM_SIMP_TAC[REAL_ARITH
     `~(b:real = a) ==>
        (a <= x /\ x <= b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = a \/
        ~(b <= a) /\ x = b)`]] THEN
  ASM_REWRITE_TAC[FINITE_UNION; SET_RULE
   `{x | p x \/ q x} = {x | p x} UNION {x | q x}`] THEN
  ASM_CASES_TAC `b:real <= a` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY]);;

export_namedthm FINITE_REAL_INTERVAL "FINITE_REAL_INTERVAL";;

let real_INFINITE = prove 
 (`INFINITE(:real)`,
  REWRITE_TAC[INFINITE] THEN
  DISCH_THEN(MP_TAC o SPEC `{x:real | &0 <= x}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
  REWRITE_TAC[FINITE_REAL_INTERVAL; SUBSET_UNIV]);;

export_namedthm real_INFINITE "real_INFINITE";;

(* ------------------------------------------------------------------------- *)
(* Indexing of finite sets and enumeration of subsets of N in order.         *)
(* ------------------------------------------------------------------------- *)

export_theory "set-finite-index";;

let HAS_SIZE_INDEX = prove 
 (`!s n. s HAS_SIZE n
         ==> ?f:num->A. (!m. m < n ==> f(m) IN s) /\
                        (!x. x IN s ==> ?!m. m < n /\ (f m = x))`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  SIMP_TAC[HAS_SIZE_0; HAS_SIZE_SUC; LT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `s:A->bool` THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:A`) (MP_TAC o SPEC `a:A`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (a:A)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\m:num. if m < n then f(m) else a:A` THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[IN_DELETE]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN
  CONV_TAC(ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
  ASM_CASES_TAC `a:A = x` THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[LT_REFL; IN_DELETE]);;

export_namedthm HAS_SIZE_INDEX "HAS_SIZE_INDEX";;

let INFINITE_ENUMERATE = prove 
 (`!s:num->bool.
       INFINITE s
       ==> ?r:num->num. (!m n. m < n ==> r(m) < r(n)) /\
                        IMAGE r (:num) = s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n:num. ?x. n <= x /\ x IN s` MP_TAC THENL
   [ASM_MESON_TAC[INFINITE; num_FINITE; LT_IMP_LE; NOT_LE];
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [num_WOP]] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  REWRITE_TAC[TAUT `p ==> ~(q /\ r) <=> q /\ p ==> ~r`] THEN
  X_GEN_TAC `next:num->num` THEN STRIP_TAC THEN
  (MP_TAC o prove_recursive_functions_exist num_RECURSION)
   `(f(0) = next 0) /\ (!n. f(SUC n) = next(f n + 1))` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num->num` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LT] THEN
    ASM_MESON_TAC[ARITH_RULE `m <= n /\ n + 1 <= p ==> m < p`; LE_LT];
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; FORALL_IN_IMAGE; SUBSET] THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN CONJ_TAC THENL
   [INDUCT_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?m:num. m < n /\ m IN s` THENL
   [MP_TAC(SPEC `\m:num. m < n /\ m IN s` num_MAX) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
     `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
    CONJ_TAC THENL [MESON_TAC[LT_IMP_LE]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?q. p = (r:num->num) q` (CHOOSE_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[]; EXISTS_TAC `SUC q`] THEN
    ASM_REWRITE_TAC[GSYM LE_ANTISYM; GSYM NOT_LT] THEN
    ASM_MESON_TAC[NOT_LE; ARITH_RULE `r < p <=> r + 1 <= p`];
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[GSYM LE_ANTISYM; GSYM NOT_LT] THEN
    ASM_MESON_TAC[LE_0]]);;

export_namedthm INFINITE_ENUMERATE "INFINITE_ENUMERATE";;

let INFINITE_ENUMERATE_EQ = prove 
 (`!s:num->bool.
     INFINITE s <=> ?r. (!m n:num. m < n ==> r m < r n) /\ IMAGE r (:num) = s`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[INFINITE_ENUMERATE] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` (STRIP_ASSUME_TAC o GSYM)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INFINITE_IMAGE THEN
  REWRITE_TAC[num_INFINITE; IN_UNIV] THEN
  MATCH_MP_TAC WLOG_LT THEN ASM_MESON_TAC[LT_REFL]);;

export_namedthm INFINITE_ENUMERATE_EQ "INFINITE_ENUMERATE_EQ";;

(* ------------------------------------------------------------------------- *)
(* Mapping between finite sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

export_theory "set-finite-list";;

let set_of_list = new_recursive_definition list_RECURSION
  `(set_of_list ([]:A list) = {}) /\
   (set_of_list (CONS (h:A) t) = h INSERT (set_of_list t))`;;

export_namedthm set_of_list "set_of_list";;

let list_of_set = new_definition 
  `list_of_set s = @l. (set_of_list l = s) /\ (LENGTH l = CARD s)`;;

export_namedthm list_of_set "list_of_set";;

let LIST_OF_SET_PROPERTIES = prove 
 (`!s:A->bool. FINITE(s)
               ==> (set_of_list(list_of_set s) = s) /\
                   (LENGTH(list_of_set s) = CARD s)`,
  REWRITE_TAC[list_of_set] THEN
  CONV_TAC(BINDER_CONV(RAND_CONV SELECT_CONV)) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `[]:A list` THEN REWRITE_TAC[CARD_CLAUSES; LENGTH; set_of_list];
    EXISTS_TAC `CONS (x:A) l` THEN ASM_REWRITE_TAC[LENGTH] THEN
    ASM_REWRITE_TAC[set_of_list] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC
     [MATCH_MP (CONJUNCT2 CARD_CLAUSES) th]) THEN
    ASM_REWRITE_TAC[]]);;

export_namedthm LIST_OF_SET_PROPERTIES "LIST_OF_SET_PROPERTIES";;

let SET_OF_LIST_OF_SET = prove 
 (`!s. FINITE(s) ==> (set_of_list(list_of_set s) = s)`,
  MESON_TAC[LIST_OF_SET_PROPERTIES]);;

export_namedthm SET_OF_LIST_OF_SET "SET_OF_LIST_OF_SET";;

let LENGTH_LIST_OF_SET = prove 
 (`!s. FINITE(s) ==> (LENGTH(list_of_set s) = CARD s)`,
  MESON_TAC[LIST_OF_SET_PROPERTIES]);;

export_namedthm LENGTH_LIST_OF_SET "LENGTH_LIST_OF_SET";;

let MEM_LIST_OF_SET = prove 
 (`!s:A->bool. FINITE(s) ==> !x. MEM x (list_of_set s) <=> x IN s`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SET_OF_LIST_OF_SET) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (BINDER_CONV o funpow 2 RAND_CONV)
    [GSYM th]) THEN
  SPEC_TAC(`list_of_set(s:A->bool)`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; set_of_list; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

export_namedthm MEM_LIST_OF_SET "MEM_LIST_OF_SET";;

let FINITE_SET_OF_LIST = prove 
 (`!l. FINITE(set_of_list l)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[set_of_list; FINITE_RULES]);;

export_namedthm FINITE_SET_OF_LIST "FINITE_SET_OF_LIST";;

let IN_SET_OF_LIST = prove 
 (`!x l. x IN (set_of_list l) <=> MEM x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; MEM; set_of_list] THEN
  ASM_MESON_TAC[]);;

export_namedthm IN_SET_OF_LIST "IN_SET_OF_LIST";;

let SET_OF_LIST_APPEND = prove 
 (`!l1 l2. set_of_list(APPEND l1 l2) = set_of_list(l1) UNION set_of_list(l2)`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; IN_UNION; MEM_APPEND]);;

export_namedthm SET_OF_LIST_APPEND "SET_OF_LIST_APPEND";;

let SET_OF_LIST_MAP = prove 
 (`!f l. set_of_list(MAP f l) = IMAGE f (set_of_list l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[set_of_list; MAP; IMAGE_CLAUSES]);;

export_namedthm SET_OF_LIST_MAP "SET_OF_LIST_MAP";;

let SET_OF_LIST_EQ_EMPTY = prove 
 (`!l. set_of_list l = {} <=> l = []`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[set_of_list; NOT_CONS_NIL; NOT_INSERT_EMPTY]);;

export_namedthm SET_OF_LIST_EQ_EMPTY "SET_OF_LIST_EQ_EMPTY";;

let LIST_OF_SET_EMPTY = prove 
 (`list_of_set {} = []`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
  SIMP_TAC[LENGTH_LIST_OF_SET; FINITE_EMPTY; CARD_CLAUSES]);;

export_namedthm LIST_OF_SET_EMPTY "LIST_OF_SET_EMPTY";;

let LIST_OF_SET_SING = prove 
 (`!x:A. list_of_set {a} = [a]`,
  GEN_TAC THEN REWRITE_TAC[list_of_set] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  SIMP_TAC[LENGTH; CARD_CLAUSES; FINITE_EMPTY; NOT_IN_EMPTY; NOT_SUC] THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  SIMP_TAC[LENGTH; set_of_list; CONS_11; SUC_INJ; NOT_CONS_NIL; NOT_SUC] THEN
  SET_TAC[]);;

export_namedthm LIST_OF_SET_SING "LIST_OF_SET_SING";;

(* ------------------------------------------------------------------------- *)
(* Mappings from finite set enumerations to lists (no "setification").       *)
(* ------------------------------------------------------------------------- *)

let dest_setenum =
  let fn = splitlist (dest_binary "INSERT") in
  fun tm -> let l,n = fn tm in
            if is_const n && fst(dest_const n) = "EMPTY" then l
            else failwith "dest_setenum: not a finite set enumeration";;

let is_setenum = can dest_setenum;;

let mk_setenum =
  let insert_atm = `(INSERT):A->(A->bool)->(A->bool)`
  and nil_atm = `(EMPTY):A->bool` in
  fun (l,ty) ->
    let insert_tm = inst [ty,aty] insert_atm
    and nil_tm = inst [ty,aty] nil_atm in
    itlist (mk_binop insert_tm) l nil_tm;;

let mk_fset l = mk_setenum(l,type_of(hd l));;

(* ------------------------------------------------------------------------- *)
(* Pairwise property over sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

export_theory "set-pairwise";;

let pairwise = new_definition 
  `pairwise r s <=> !x y. x IN s /\ y IN s /\ ~(x = y) ==> r x y`;;

export_namedthm pairwise "pairwise";;

let PAIRWISE_EMPTY = prove 
 (`!r. pairwise r {} <=> T`,
  REWRITE_TAC[pairwise; NOT_IN_EMPTY] THEN MESON_TAC[]);;

export_namedthm PAIRWISE_EMPTY "PAIRWISE_EMPTY";;

let PAIRWISE_SING = prove 
 (`!r x. pairwise r {x} <=> T`,
  REWRITE_TAC[pairwise; IN_SING] THEN MESON_TAC[]);;

export_namedthm PAIRWISE_SING "PAIRWISE_SING";;

let PAIRWISE_IMP = prove 
 (`!P Q s:A->bool.
        pairwise P s /\
        (!x y. x IN s /\ y IN s /\ P x y /\ ~(x = y) ==> Q x y)
        ==> pairwise Q s`,
  REWRITE_TAC[pairwise] THEN SET_TAC[]);;

export_namedthm PAIRWISE_IMP "PAIRWISE_IMP";;

let PAIRWISE_MONO = prove 
 (`!r s t. pairwise r s /\ t SUBSET s ==> pairwise r t`,
  REWRITE_TAC[pairwise] THEN SET_TAC[]);;

export_namedthm PAIRWISE_MONO "PAIRWISE_MONO";;

let PAIRWISE_AND = prove 
 (`!R R' s. pairwise R s /\ pairwise R' s <=>
            pairwise (\x y. R x y /\ R' x y) s`,
  REWRITE_TAC[pairwise] THEN SET_TAC[]);;

export_namedthm PAIRWISE_AND "PAIRWISE_AND";;

let PAIRWISE_INSERT = prove 
 (`!r x s.
        pairwise r (x INSERT s) <=>
        (!y. y IN s /\ ~(y = x) ==> r x y /\ r y x) /\
        pairwise r s`,
  REWRITE_TAC[pairwise; IN_INSERT] THEN MESON_TAC[]);;

export_namedthm PAIRWISE_INSERT "PAIRWISE_INSERT";;

let PAIRWISE_INSERT_SYMMETRIC = prove 
 (`!r (x:A) s.
        (!y. y IN s ==> (r x y <=> r y x))
        ==> (pairwise r (x INSERT s) <=>
             (!y. y IN s /\ ~(y = x) ==> r x y) /\ pairwise r s)`,
  REWRITE_TAC[PAIRWISE_INSERT] THEN MESON_TAC[]);;

export_namedthm PAIRWISE_INSERT_SYMMETRIC "PAIRWISE_INSERT_SYMMETRIC";;

let PAIRWISE_IMAGE = prove 
 (`!r f. pairwise r (IMAGE f s) <=>
         pairwise (\x y. ~(f x = f y) ==> r (f x) (f y)) s`,
  REWRITE_TAC[pairwise; IN_IMAGE] THEN MESON_TAC[]);;

export_namedthm PAIRWISE_IMAGE "PAIRWISE_IMAGE";;

let PAIRWISE_UNION = prove 
 (`!R s t. pairwise R (s UNION t) <=>
           pairwise R s /\ pairwise R t /\
           (!x y. x IN s DIFF t /\ y IN t DIFF s ==> R x y /\ R y x)`,
  REWRITE_TAC[pairwise] THEN SET_TAC[]);;

export_namedthm PAIRWISE_UNION "PAIRWISE_UNION";;

let PAIRWISE_CHAIN_UNIONS = prove 
 (`!R:A->A->bool c.
        (!s. s IN c ==> pairwise R s) /\
        (!s t. s IN c /\ t IN c ==> s SUBSET t \/ t SUBSET s)
        ==> pairwise R (UNIONS c)`,
  REWRITE_TAC[pairwise] THEN SET_TAC[]);;

export_namedthm PAIRWISE_CHAIN_UNIONS "PAIRWISE_CHAIN_UNIONS";;

let DIFF_UNIONS_PAIRWISE_DISJOINT = prove 
 (`!s t:(A->bool)->bool.
        pairwise DISJOINT s /\ t SUBSET s
        ==> UNIONS s DIFF UNIONS t = UNIONS(s DIFF t)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `t UNION u = s /\ DISJOINT t u ==> s DIFF t = u`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM UNIONS_UNION] THEN AP_TERM_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
    REWRITE_TAC[DISJOINT; IN_DIFF] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN ASM_MESON_TAC[]]);;

export_namedthm DIFF_UNIONS_PAIRWISE_DISJOINT "DIFF_UNIONS_PAIRWISE_DISJOINT";;

let INTER_UNIONS_PAIRWISE_DISJOINT = prove 
 (`!s t:(A->bool)->bool.
        pairwise DISJOINT (s UNION t)
        ==> UNIONS s INTER UNIONS t = UNIONS(s INTER t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[INTER_UNIONS; SIMPLE_IMAGE; UNIONS_IMAGE] THEN
  GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
  REWRITE_TAC[pairwise; IN_UNIONS; IN_INTER; IN_ELIM_THM; IN_UNION] THEN
  DISCH_TAC THEN X_GEN_TAC `z:A` THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  EQ_TAC THENL [REWRITE_TAC[LEFT_IMP_EXISTS_THM]; MESON_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`u:A->bool`; `v:A->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:A->bool`; `v:A->bool`]) THEN
  ASM_CASES_TAC `u:A->bool = v` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ASM SET_TAC[]]);;

export_namedthm INTER_UNIONS_PAIRWISE_DISJOINT "INTER_UNIONS_PAIRWISE_DISJOINT";;

let PSUBSET_UNIONS_PAIRWISE_DISJOINT = prove 
 (`!u v:(A->bool)->bool.
        pairwise DISJOINT v /\ u PSUBSET (v DELETE {})
        ==> UNIONS u PSUBSET UNIONS v`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `u SUBSET v /\ ~(v DIFF u = {}) ==> u PSUBSET v`) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
      DIFF_UNIONS_PAIRWISE_DISJOINT o lhand o rand o snd) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EMPTY_UNIONS] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [PSUBSET_ALT]) THEN
  REWRITE_TAC[IN_DELETE; IN_DIFF] THEN MESON_TAC[]);;

export_namedthm PSUBSET_UNIONS_PAIRWISE_DISJOINT "PSUBSET_UNIONS_PAIRWISE_DISJOINT";;

(* ------------------------------------------------------------------------- *)
(* Useful idioms for being a suitable union/intersection of somethings.      *)
(* ------------------------------------------------------------------------- *)

export_theory "set-union-inter-misc";;

parse_as_infix("UNION_OF",(20,"right"));;
parse_as_infix("INTERSECTION_OF",(20,"right"));;

let UNION_OF = new_definition 
 `P UNION_OF Q =
   \s:A->bool. ?u. P u /\ (!c. c IN u ==> Q c) /\ UNIONS u = s`;;

export_namedthm UNION_OF "UNION_OF";;

let INTERSECTION_OF = new_definition 
 `P INTERSECTION_OF Q =
   \s:A->bool. ?u. P u /\ (!c. c IN u ==> Q c) /\ INTERS u = s`;;

export_namedthm INTERSECTION_OF "INTERSECTION_OF";;

let UNION_OF_INC = prove 
 (`!P Q s:A->bool. P {s} /\ Q s ==> (P UNION_OF Q) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNION_OF] THEN
  EXISTS_TAC `{s:A->bool}` THEN ASM_SIMP_TAC[UNIONS_1; IN_SING]);;

export_namedthm UNION_OF_INC "UNION_OF_INC";;

let INTERSECTION_OF_INC = prove 
 (`!P Q s:A->bool. P {s} /\ Q s ==> (P INTERSECTION_OF Q) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTERSECTION_OF] THEN
  EXISTS_TAC `{s:A->bool}` THEN ASM_SIMP_TAC[INTERS_1; IN_SING]);;

export_namedthm INTERSECTION_OF_INC "INTERSECTION_OF_INC";;

let UNION_OF_MONO = prove 
 (`!P Q Q' s:A->bool.
        (P UNION_OF Q) s /\ (!x. Q x ==> Q' x) ==> (P UNION_OF Q') s`,
  REWRITE_TAC[UNION_OF] THEN MESON_TAC[]);;

export_namedthm UNION_OF_MONO "UNION_OF_MONO";;

let INTERSECTION_OF_MONO = prove 
 (`!P Q Q' s:A->bool.
        (P INTERSECTION_OF Q) s /\ (!x. Q x ==> Q' x)
        ==> (P INTERSECTION_OF Q') s`,
  REWRITE_TAC[INTERSECTION_OF] THEN MESON_TAC[]);;

export_namedthm INTERSECTION_OF_MONO "INTERSECTION_OF_MONO";;

let FORALL_UNION_OF = prove 
 (`(!s. (P UNION_OF Q) s ==> R s) <=>
   (!t. P t /\ (!c. c IN t ==> Q c) ==> R(UNIONS t))`,
  REWRITE_TAC[UNION_OF] THEN MESON_TAC[]);;

export_namedthm FORALL_UNION_OF "FORALL_UNION_OF";;

let FORALL_INTERSECTION_OF = prove 
 (`(!s. (P INTERSECTION_OF Q) s ==> R s) <=>
   (!t. P t /\ (!c. c IN t ==> Q c) ==> R(INTERS t))`,
  REWRITE_TAC[INTERSECTION_OF] THEN MESON_TAC[]);;

export_namedthm FORALL_INTERSECTION_OF "FORALL_INTERSECTION_OF";;

let UNION_OF_EMPTY = prove 
 (`!P Q:(A->bool)->bool. P {} ==> (P UNION_OF Q) {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNION_OF] THEN
  EXISTS_TAC `{}:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[UNIONS_0; NOT_IN_EMPTY]);;

export_namedthm UNION_OF_EMPTY "UNION_OF_EMPTY";;

let INTERSECTION_OF_EMPTY = prove 
 (`!P Q:(A->bool)->bool. P {} ==> (P INTERSECTION_OF Q) UNIV`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTERSECTION_OF] THEN
  EXISTS_TAC `{}:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[INTERS_0; NOT_IN_EMPTY]);;

export_namedthm INTERSECTION_OF_EMPTY "INTERSECTION_OF_EMPTY";;

(* ------------------------------------------------------------------------- *)
(* The ARBITRARY and FINITE cases of UNION_OF / INTERSECTION_OF              *)
(* ------------------------------------------------------------------------- *)

export_theory "set-union-inter-misc";;

let ARBITRARY = new_definition 
 `ARBITRARY (s:(A->bool)->bool) <=> T`;;

export_namedthm ARBITRARY "ARBITRARY";;

let ARBITRARY_UNION_OF_ALT = prove 
 (`!B s:A->bool.
        (ARBITRARY UNION_OF B) s <=>
        !x. x IN s ==>  ?u. u IN B /\ x IN u /\ u SUBSET s`,
  GEN_TAC THEN REWRITE_TAC[FORALL_AND_THM; TAUT
   `(p <=> q) <=> (p ==> q) /\ (q ==> p)`] THEN
  REWRITE_TAC[FORALL_UNION_OF; ARBITRARY] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[ARBITRARY; UNION_OF] THEN
  EXISTS_TAC `{u:A->bool | u IN B /\ u SUBSET s}` THEN ASM SET_TAC[]);;

export_namedthm ARBITRARY_UNION_OF_ALT "ARBITRARY_UNION_OF_ALT";;

let ARBITRARY_UNION_OF_EMPTY = prove 
 (`!P:(A->bool)->bool. (ARBITRARY UNION_OF P) {}`,
  SIMP_TAC[UNION_OF_EMPTY; ARBITRARY]);;

export_namedthm ARBITRARY_UNION_OF_EMPTY "ARBITRARY_UNION_OF_EMPTY";;

let ARBITRARY_INTERSECTION_OF_EMPTY = prove 
 (`!P:(A->bool)->bool. (ARBITRARY INTERSECTION_OF P) UNIV`,
  SIMP_TAC[INTERSECTION_OF_EMPTY; ARBITRARY]);;

export_namedthm ARBITRARY_INTERSECTION_OF_EMPTY "ARBITRARY_INTERSECTION_OF_EMPTY";;

let ARBITRARY_UNION_OF_INC = prove 
 (`!P s:A->bool. P s ==> (ARBITRARY UNION_OF P) s`,
  SIMP_TAC[UNION_OF_INC; ARBITRARY]);;

export_namedthm ARBITRARY_UNION_OF_INC "ARBITRARY_UNION_OF_INC";;

let ARBITRARY_INTERSECTION_OF_INC = prove 
 (`!P s:A->bool. P s ==> (ARBITRARY INTERSECTION_OF P) s`,
  SIMP_TAC[INTERSECTION_OF_INC; ARBITRARY]);;

export_namedthm ARBITRARY_INTERSECTION_OF_INC "ARBITRARY_INTERSECTION_OF_INC";;

let ARBITRARY_UNION_OF_COMPLEMENT = prove 
 (`!P s. (ARBITRARY UNION_OF P) s <=>
         (ARBITRARY INTERSECTION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNION_OF; INTERSECTION_OF] THEN
  EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\c. (:A) DIFF c) u` THEN
  ASM_SIMP_TAC[ARBITRARY; FORALL_IN_IMAGE; COMPL_COMPL] THEN
  ONCE_REWRITE_TAC[UNIONS_INTERS; INTERS_UNIONS] THEN
  REWRITE_TAC[SET_RULE `{f y | y IN IMAGE g s} = IMAGE (\x. f(g x)) s`] THEN
  ASM_REWRITE_TAC[IMAGE_ID; COMPL_COMPL]);;

export_namedthm ARBITRARY_UNION_OF_COMPLEMENT "ARBITRARY_UNION_OF_COMPLEMENT";;

let ARBITRARY_INTERSECTION_OF_COMPLEMENT = prove 
 (`!P s. (ARBITRARY INTERSECTION_OF P) s <=>
         (ARBITRARY UNION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)`,
  REWRITE_TAC[ARBITRARY_UNION_OF_COMPLEMENT] THEN
  REWRITE_TAC[ETA_AX; COMPL_COMPL]);;

export_namedthm ARBITRARY_INTERSECTION_OF_COMPLEMENT "ARBITRARY_INTERSECTION_OF_COMPLEMENT";;

let ARBITRARY_UNION_OF_IDEMPOT = prove 
 (`!P:(A->bool)->bool.
        ARBITRARY UNION_OF ARBITRARY UNION_OF P = ARBITRARY UNION_OF P`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `s:A->bool` THEN
  EQ_TAC THEN REWRITE_TAC[ARBITRARY_UNION_OF_INC] THEN
  REWRITE_TAC[UNION_OF; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u:(A->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:(A->bool)->(A->bool)->bool` THEN DISCH_TAC THEN
  EXISTS_TAC
    `IMAGE SND {s,t | s IN u /\ t IN (f:(A->bool)->(A->bool)->bool) s}` THEN
  ASM_SIMP_TAC[ARBITRARY] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[UNIONS_IMAGE]] THEN
  REWRITE_TAC[EXISTS_IN_GSPEC] THEN ASM SET_TAC[]);;

export_namedthm ARBITRARY_UNION_OF_IDEMPOT "ARBITRARY_UNION_OF_IDEMPOT";;

let ARBITRARY_INTERSECTION_OF_IDEMPOT = prove 
 (`!P:(A->bool)->bool.
        ARBITRARY INTERSECTION_OF ARBITRARY INTERSECTION_OF P =
        ARBITRARY INTERSECTION_OF P`,
  REWRITE_TAC[COMPL_COMPL; ETA_AX; REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX]
              ARBITRARY_INTERSECTION_OF_COMPLEMENT] THEN
  REWRITE_TAC[ARBITRARY_UNION_OF_IDEMPOT]);;

export_namedthm ARBITRARY_INTERSECTION_OF_IDEMPOT "ARBITRARY_INTERSECTION_OF_IDEMPOT";;

let ARBITRARY_UNION_OF_UNIONS = prove 
 (`!P u:(A->bool)->bool.
        (!s. s IN u ==> (ARBITRARY UNION_OF P) s)
        ==> (ARBITRARY UNION_OF P) (UNIONS u)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ARBITRARY_UNION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC[UNION_OF] THEN REWRITE_TAC[] THEN
  EXISTS_TAC `u:(A->bool)->bool` THEN ASM_REWRITE_TAC[ARBITRARY]);;

export_namedthm ARBITRARY_UNION_OF_UNIONS "ARBITRARY_UNION_OF_UNIONS";;

let ARBITRARY_UNION_OF_UNION = prove 
 (`!P s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
           ==> (ARBITRARY UNION_OF P) (s UNION t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_2] THEN
  MATCH_MP_TAC ARBITRARY_UNION_OF_UNIONS THEN
  ASM_REWRITE_TAC[ARBITRARY; FORALL_IN_INSERT] THEN
  REWRITE_TAC[ARBITRARY; NOT_IN_EMPTY]);;

export_namedthm ARBITRARY_UNION_OF_UNION "ARBITRARY_UNION_OF_UNION";;

let ARBITRARY_INTERSECTION_OF_INTERS = prove 
 (`!P u:(A->bool)->bool.
        (!s. s IN u ==> (ARBITRARY INTERSECTION_OF P) s)
        ==> (ARBITRARY INTERSECTION_OF P) (INTERS u)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM ARBITRARY_INTERSECTION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC[INTERSECTION_OF] THEN REWRITE_TAC[] THEN
  EXISTS_TAC `u:(A->bool)->bool` THEN ASM_REWRITE_TAC[ARBITRARY]);;

export_namedthm ARBITRARY_INTERSECTION_OF_INTERS "ARBITRARY_INTERSECTION_OF_INTERS";;

let ARBITRARY_INTERSECTION_OF_INTER = prove 
 (`!P s t. (ARBITRARY INTERSECTION_OF P) s /\ (ARBITRARY INTERSECTION_OF P) t
           ==> (ARBITRARY INTERSECTION_OF P) (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC ARBITRARY_INTERSECTION_OF_INTERS THEN
  ASM_REWRITE_TAC[ARBITRARY; FORALL_IN_INSERT] THEN
  REWRITE_TAC[ARBITRARY; NOT_IN_EMPTY]);;

export_namedthm ARBITRARY_INTERSECTION_OF_INTER "ARBITRARY_INTERSECTION_OF_INTER";;

let ARBITRARY_UNION_OF_INTER_EQ = prove 
 (`!P:(A->bool)->bool.
        (!s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
               ==> (ARBITRARY UNION_OF P) (s INTER t)) <=>
        (!s t. P s /\ P t ==> (ARBITRARY UNION_OF P) (s INTER t))`,
  GEN_TAC THEN
  EQ_TAC THENL [MESON_TAC[ARBITRARY_UNION_OF_INC]; DISCH_TAC] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [UNION_OF] THEN
  REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[INTER_UNIONS] THEN
  REPLICATE_TAC 2
   (MATCH_MP_TAC ARBITRARY_UNION_OF_UNIONS THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; ARBITRARY; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC));;

export_namedthm ARBITRARY_UNION_OF_INTER_EQ "ARBITRARY_UNION_OF_INTER_EQ";;

let ARBITRARY_UNION_OF_INTER = prove 
 (`!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> (!s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
                   ==> (ARBITRARY UNION_OF P) (s INTER t))`,
  REWRITE_TAC[ARBITRARY_UNION_OF_INTER_EQ] THEN
  MESON_TAC[ARBITRARY_UNION_OF_INC]);;

export_namedthm ARBITRARY_UNION_OF_INTER "ARBITRARY_UNION_OF_INTER";;

let ARBITRARY_INTERSECTION_OF_UNION_EQ = prove 
 (`!P:(A->bool)->bool.
        (!s t. (ARBITRARY INTERSECTION_OF P) s /\
               (ARBITRARY INTERSECTION_OF P) t
               ==> (ARBITRARY INTERSECTION_OF P) (s UNION t)) <=>
        (!s t. P s /\ P t ==> (ARBITRARY INTERSECTION_OF P) (s UNION t))`,
  ONCE_REWRITE_TAC[ARBITRARY_INTERSECTION_OF_COMPLEMENT] THEN
  REWRITE_TAC[SET_RULE
    `UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)`] THEN
  REWRITE_TAC[MESON[COMPL_COMPL] `(!s. P(UNIV DIFF s)) <=> (!s. P s)`] THEN
  REWRITE_TAC[ARBITRARY_UNION_OF_INTER_EQ] THEN
  REWRITE_TAC[SET_RULE
   `s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))`] THEN
  REWRITE_TAC[MESON[COMPL_COMPL] `(!s. P(UNIV DIFF s)) <=> (!s. P s)`] THEN
  REWRITE_TAC[COMPL_COMPL]);;

export_namedthm ARBITRARY_INTERSECTION_OF_UNION_EQ "ARBITRARY_INTERSECTION_OF_UNION_EQ";;

let ARBITRARY_INTERSECTION_OF_UNION = prove 
 (`!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s UNION t))
        ==> (!s t. (ARBITRARY INTERSECTION_OF P) s /\
                   (ARBITRARY INTERSECTION_OF P) t
                   ==> (ARBITRARY INTERSECTION_OF P) (s UNION t))`,
  REWRITE_TAC[ARBITRARY_INTERSECTION_OF_UNION_EQ] THEN
  MESON_TAC[ARBITRARY_INTERSECTION_OF_INC]);;

export_namedthm ARBITRARY_INTERSECTION_OF_UNION "ARBITRARY_INTERSECTION_OF_UNION";;

let FINITE_UNION_OF_EMPTY = prove 
 (`!P:(A->bool)->bool. (FINITE UNION_OF P) {}`,
  SIMP_TAC[UNION_OF_EMPTY; FINITE_EMPTY]);;

export_namedthm FINITE_UNION_OF_EMPTY "FINITE_UNION_OF_EMPTY";;

let FINITE_INTERSECTION_OF_EMPTY = prove 
 (`!P:(A->bool)->bool. (FINITE INTERSECTION_OF P) UNIV`,
  SIMP_TAC[INTERSECTION_OF_EMPTY; FINITE_EMPTY]);;

export_namedthm FINITE_INTERSECTION_OF_EMPTY "FINITE_INTERSECTION_OF_EMPTY";;

let FINITE_UNION_OF_INC = prove 
 (`!P s:A->bool. P s ==> (FINITE UNION_OF P) s`,
  SIMP_TAC[UNION_OF_INC; FINITE_SING]);;

export_namedthm FINITE_UNION_OF_INC "FINITE_UNION_OF_INC";;

let FINITE_INTERSECTION_OF_INC = prove 
 (`!P s:A->bool. P s ==> (FINITE INTERSECTION_OF P) s`,
  SIMP_TAC[INTERSECTION_OF_INC; FINITE_SING]);;

export_namedthm FINITE_INTERSECTION_OF_INC "FINITE_INTERSECTION_OF_INC";;

let FINITE_UNION_OF_COMPLEMENT = prove 
 (`!P s. (FINITE UNION_OF P) s <=>
         (FINITE INTERSECTION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNION_OF; INTERSECTION_OF] THEN
  EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\c. (:A) DIFF c) u` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; COMPL_COMPL] THEN
  ONCE_REWRITE_TAC[UNIONS_INTERS; INTERS_UNIONS] THEN
  REWRITE_TAC[SET_RULE `{f y | y IN IMAGE g s} = IMAGE (\x. f(g x)) s`] THEN
  ASM_REWRITE_TAC[IMAGE_ID; COMPL_COMPL]);;

export_namedthm FINITE_UNION_OF_COMPLEMENT "FINITE_UNION_OF_COMPLEMENT";;

let FINITE_INTERSECTION_OF_COMPLEMENT = prove 
 (`!P s. (FINITE INTERSECTION_OF P) s <=>
         (FINITE UNION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)`,
  REWRITE_TAC[FINITE_UNION_OF_COMPLEMENT] THEN
  REWRITE_TAC[ETA_AX; COMPL_COMPL]);;

export_namedthm FINITE_INTERSECTION_OF_COMPLEMENT "FINITE_INTERSECTION_OF_COMPLEMENT";;

let FINITE_UNION_OF_IDEMPOT = prove 
 (`!P:(A->bool)->bool.
        FINITE UNION_OF FINITE UNION_OF P = FINITE UNION_OF P`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `s:A->bool` THEN
  EQ_TAC THEN REWRITE_TAC[FINITE_UNION_OF_INC] THEN
  REWRITE_TAC[UNION_OF; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u:(A->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:(A->bool)->(A->bool)->bool` THEN DISCH_TAC THEN
  EXISTS_TAC
    `IMAGE SND {s,t | s IN u /\ t IN (f:(A->bool)->(A->bool)->bool) s}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_PRODUCT_DEPENDENT] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[UNIONS_IMAGE]] THEN
  REWRITE_TAC[EXISTS_IN_GSPEC] THEN ASM SET_TAC[]);;

export_namedthm FINITE_UNION_OF_IDEMPOT "FINITE_UNION_OF_IDEMPOT";;

let FINITE_INTERSECTION_OF_IDEMPOT = prove 
 (`!P:(A->bool)->bool.
        FINITE INTERSECTION_OF FINITE INTERSECTION_OF P =
        FINITE INTERSECTION_OF P`,
  REWRITE_TAC[COMPL_COMPL; ETA_AX; REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX]
              FINITE_INTERSECTION_OF_COMPLEMENT] THEN
  REWRITE_TAC[FINITE_UNION_OF_IDEMPOT]);;

export_namedthm FINITE_INTERSECTION_OF_IDEMPOT "FINITE_INTERSECTION_OF_IDEMPOT";;

let FINITE_UNION_OF_UNIONS = prove 
 (`!P u:(A->bool)->bool.
        FINITE u /\ (!s. s IN u ==> (FINITE UNION_OF P) s)
        ==> (FINITE UNION_OF P) (UNIONS u)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM FINITE_UNION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC[UNION_OF] THEN REWRITE_TAC[] THEN
  EXISTS_TAC `u:(A->bool)->bool` THEN ASM_REWRITE_TAC[]);;

export_namedthm FINITE_UNION_OF_UNIONS "FINITE_UNION_OF_UNIONS";;

let FINITE_UNION_OF_UNION = prove 
 (`!P s t. (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
           ==> (FINITE UNION_OF P) (s UNION t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_2] THEN
  MATCH_MP_TAC FINITE_UNION_OF_UNIONS THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT] THEN
  REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY]);;

export_namedthm FINITE_UNION_OF_UNION "FINITE_UNION_OF_UNION";;

let FINITE_INTERSECTION_OF_INTERS = prove 
 (`!P u:(A->bool)->bool.
        FINITE u /\ (!s. s IN u ==> (FINITE INTERSECTION_OF P) s)
        ==> (FINITE INTERSECTION_OF P) (INTERS u)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM FINITE_INTERSECTION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC[INTERSECTION_OF] THEN REWRITE_TAC[] THEN
  EXISTS_TAC `u:(A->bool)->bool` THEN ASM_REWRITE_TAC[]);;

export_namedthm FINITE_INTERSECTION_OF_INTERS "FINITE_INTERSECTION_OF_INTERS";;

let FINITE_INTERSECTION_OF_INTER = prove 
 (`!P s t. (FINITE INTERSECTION_OF P) s /\ (FINITE INTERSECTION_OF P) t
           ==> (FINITE INTERSECTION_OF P) (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC FINITE_INTERSECTION_OF_INTERS THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT] THEN
  REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY]);;

export_namedthm FINITE_INTERSECTION_OF_INTER "FINITE_INTERSECTION_OF_INTER";;

let FINITE_UNION_OF_INTER_EQ = prove 
 (`!P:(A->bool)->bool.
        (!s t. (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
                   ==> (FINITE UNION_OF P) (s INTER t)) <=>
        (!s t. P s /\ P t ==> (FINITE UNION_OF P) (s INTER t))`,
  GEN_TAC THEN
  EQ_TAC THENL [MESON_TAC[FINITE_UNION_OF_INC]; DISCH_TAC] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [UNION_OF] THEN
  REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[INTER_UNIONS] THEN
  REPLICATE_TAC 2
   (MATCH_MP_TAC FINITE_UNION_OF_UNIONS THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC));;

export_namedthm FINITE_UNION_OF_INTER_EQ "FINITE_UNION_OF_INTER_EQ";;

let FINITE_UNION_OF_INTER = prove 
 (`!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> (!s t. (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
                   ==> (FINITE UNION_OF P) (s INTER t))`,
  REWRITE_TAC[FINITE_UNION_OF_INTER_EQ] THEN
  MESON_TAC[FINITE_UNION_OF_INC]);;

export_namedthm FINITE_UNION_OF_INTER "FINITE_UNION_OF_INTER";;

let FINITE_INTERSECTION_OF_UNION_EQ = prove 
 (`!P:(A->bool)->bool.
        (!s t. (FINITE INTERSECTION_OF P) s /\
               (FINITE INTERSECTION_OF P) t
               ==> (FINITE INTERSECTION_OF P) (s UNION t)) <=>
        (!s t. P s /\ P t ==> (FINITE INTERSECTION_OF P) (s UNION t))`,
  ONCE_REWRITE_TAC[FINITE_INTERSECTION_OF_COMPLEMENT] THEN
  REWRITE_TAC[SET_RULE
    `UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)`] THEN
  REWRITE_TAC[MESON[COMPL_COMPL] `(!s. P(UNIV DIFF s)) <=> (!s. P s)`] THEN
  REWRITE_TAC[FINITE_UNION_OF_INTER_EQ] THEN
  REWRITE_TAC[SET_RULE
   `s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))`] THEN
  REWRITE_TAC[MESON[COMPL_COMPL] `(!s. P(UNIV DIFF s)) <=> (!s. P s)`] THEN
  REWRITE_TAC[COMPL_COMPL]);;

export_namedthm FINITE_INTERSECTION_OF_UNION_EQ "FINITE_INTERSECTION_OF_UNION_EQ";;

let FINITE_INTERSECTION_OF_UNION = prove 
 (`!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s UNION t))
        ==> (!s t. (FINITE INTERSECTION_OF P) s /\
                   (FINITE INTERSECTION_OF P) t
                   ==> (FINITE INTERSECTION_OF P) (s UNION t))`,
  REWRITE_TAC[FINITE_INTERSECTION_OF_UNION_EQ] THEN
  MESON_TAC[FINITE_INTERSECTION_OF_INC]);;

export_namedthm FINITE_INTERSECTION_OF_UNION "FINITE_INTERSECTION_OF_UNION";;

(* ------------------------------------------------------------------------- *)
(* Some additional properties of "set_of_list".                              *)
(* ------------------------------------------------------------------------- *)

let CARD_SET_OF_LIST_LE = prove 
 (`!l. CARD(set_of_list l) <= LENGTH l`,
  LIST_INDUCT_TAC THEN
  SIMP_TAC[LENGTH; set_of_list; CARD_CLAUSES; FINITE_SET_OF_LIST] THEN
  ASM_ARITH_TAC);;

export_namedthm CARD_SET_OF_LIST_LE "CARD_SET_OF_LIST_LE";;

let HAS_SIZE_SET_OF_LIST = prove 
 (`!l. (set_of_list l) HAS_SIZE (LENGTH l) <=> PAIRWISE (\x y. ~(x = y)) l`,
  REWRITE_TAC[HAS_SIZE; FINITE_SET_OF_LIST] THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; LENGTH; set_of_list; PAIRWISE; ALL;
               FINITE_SET_OF_LIST; GSYM ALL_MEM; IN_SET_OF_LIST] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUC_INJ] THEN
  ASM_MESON_TAC[CARD_SET_OF_LIST_LE; ARITH_RULE `~(SUC n <= n)`]);;

export_namedthm HAS_SIZE_SET_OF_LIST "HAS_SIZE_SET_OF_LIST";;

(* ------------------------------------------------------------------------- *)
(* Classic result on function of finite set into itself.                     *)
(* ------------------------------------------------------------------------- *)

export_theory "set-finite-endo-function";;

let SURJECTIVE_IFF_INJECTIVE_GEN = prove 
 (`!s t f:A->B.
        FINITE s /\ FINITE t /\ (CARD s = CARD t) /\ (IMAGE f s) SUBSET t
        ==> ((!y. y IN t ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `x:A = y` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `CARD s <= CARD (IMAGE (f:A->B) (s DELETE y))` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DELETE] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_DELETE] THEN ASM_MESON_TAC[];
      REWRITE_TAC[NOT_LE] THEN MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `CARD(s DELETE (y:A))` THEN
      ASM_SIMP_TAC[CARD_IMAGE_LE; FINITE_DELETE] THEN
      ASM_SIMP_TAC[CARD_DELETE; ARITH_RULE `x - 1 < x <=> ~(x = 0)`] THEN
      ASM_MESON_TAC[CARD_EQ_0; MEMBER_NOT_EMPTY]];
    SUBGOAL_THEN `IMAGE (f:A->B) s = t` MP_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[EXTENSION; IN_IMAGE]] THEN
    ASM_MESON_TAC[CARD_SUBSET_EQ; CARD_IMAGE_INJ]]);;

export_namedthm SURJECTIVE_IFF_INJECTIVE_GEN "SURJECTIVE_IFF_INJECTIVE_GEN";;

let SURJECTIVE_IFF_INJECTIVE = prove 
 (`!s f:A->A.
        FINITE s /\ (IMAGE f s) SUBSET s
        ==> ((!y. y IN s ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`,
  SIMP_TAC[SURJECTIVE_IFF_INJECTIVE_GEN]);;

export_namedthm SURJECTIVE_IFF_INJECTIVE "SURJECTIVE_IFF_INJECTIVE";;

let IMAGE_IMP_INJECTIVE_GEN = prove 
 (`!s t f:A->B.
        FINITE s /\ (CARD s = CARD t) /\ (IMAGE f s = t)
        ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o GSYM) THEN
  MP_TAC(ISPECL [`s:A->bool`; `t:B->bool`; `f:A->B`]
                SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ASM_SIMP_TAC[SUBSET_REFL; FINITE_IMAGE] THEN
  ASM_MESON_TAC[EXTENSION; IN_IMAGE]);;

export_namedthm IMAGE_IMP_INJECTIVE_GEN "IMAGE_IMP_INJECTIVE_GEN";;

let IMAGE_IMP_INJECTIVE = prove 
 (`!s f. FINITE s /\ (IMAGE f s = s)
       ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  MESON_TAC[IMAGE_IMP_INJECTIVE_GEN]);;

export_namedthm IMAGE_IMP_INJECTIVE "IMAGE_IMP_INJECTIVE";;

(* ------------------------------------------------------------------------- *)
(* Converse relation between cardinality and injection.                      *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_INJ = prove 
 (`!s t. FINITE s /\ FINITE t /\ CARD s <= CARD t
   ==> ?f:A->B. (IMAGE f s) SUBSET t /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET; NOT_IN_EMPTY] THEN
  SIMP_TAC[CARD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[CARD_CLAUSES; LE; NOT_SUC] THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `t:B->bool`] THEN
  SIMP_TAC[CARD_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[LE_SUC] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:B->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:A. if z = x then (y:B) else f(z)` THEN
  REWRITE_TAC[IN_INSERT; SUBSET; IN_IMAGE] THEN
  ASM_MESON_TAC[SUBSET; IN_IMAGE]);;

export_namedthm CARD_LE_INJ "CARD_LE_INJ";;

(* ------------------------------------------------------------------------- *)
(* Occasionally handy rewrites.                                              *)
(* ------------------------------------------------------------------------- *)

export_theory "set-misc";;

let FORALL_IN_CLAUSES = prove 
 (`(!P. (!x. x IN {} ==> P x) <=> T) /\
   (!P a s. (!x. x IN (a INSERT s) ==> P x) <=> P a /\ (!x. x IN s ==> P x))`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

export_namedthm FORALL_IN_CLAUSES "FORALL_IN_CLAUSES";;

let EXISTS_IN_CLAUSES = prove 
 (`(!P. (?x. x IN {} /\ P x) <=> F) /\
   (!P a s. (?x. x IN (a INSERT s) /\ P x) <=> P a \/ (?x. x IN s /\ P x))`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

export_namedthm EXISTS_IN_CLAUSES "EXISTS_IN_CLAUSES";;

(* ------------------------------------------------------------------------- *)
(* Injectivity and surjectivity of image and preimage under a function.      *)
(* ------------------------------------------------------------------------- *)

export_theory "set-function-image";;

let INJECTIVE_ON_IMAGE = prove 
 (`!f:A->B u.
    (!s t. s SUBSET u /\ t SUBSET u /\ IMAGE f s = IMAGE f t ==> s = t) <=>
    (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [DISCH_TAC; SET_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`{x:A}`; `{y:A}`]) THEN
  ASM_REWRITE_TAC[SING_SUBSET; IMAGE_CLAUSES] THEN SET_TAC[]);;

export_namedthm INJECTIVE_ON_IMAGE "INJECTIVE_ON_IMAGE";;

let INJECTIVE_IMAGE = prove 
 (`!f:A->B.
    (!s t. IMAGE f s = IMAGE f t ==> s = t) <=> (!x y. f x = f y ==> x = y)`,
  GEN_TAC THEN MP_TAC(ISPECL [`f:A->B`; `(:A)`] INJECTIVE_ON_IMAGE) THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV]);;

export_namedthm INJECTIVE_IMAGE "INJECTIVE_IMAGE";;

let SURJECTIVE_ON_IMAGE = prove 
 (`!f:A->B u v.
        (!t. t SUBSET v ==> ?s. s SUBSET u /\ IMAGE f s = t) <=>
        (!y. y IN v ==> ?x. x IN u /\ f x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{y:B}`) THEN ASM SET_TAC[];
    DISCH_TAC THEN X_GEN_TAC `t:B->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `{x | x IN u /\ (f:A->B) x IN t}` THEN ASM SET_TAC[]]);;

export_namedthm SURJECTIVE_ON_IMAGE "SURJECTIVE_ON_IMAGE";;

let SURJECTIVE_IMAGE = prove 
 (`!f:A->B. (!t. ?s. IMAGE f s = t) <=> (!y. ?x. f x = y)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `(:A)`; `(:B)`] SURJECTIVE_ON_IMAGE) THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV]);;

export_namedthm SURJECTIVE_IMAGE "SURJECTIVE_IMAGE";;

let INJECTIVE_ON_PREIMAGE = prove 
 (`!f:A->B s u.
        (!t t'. t SUBSET u /\ t' SUBSET u /\
                {x | x IN s /\ f x IN t} = {x | x IN s /\ f x IN t'}
                ==> t = t') <=>
        u SUBSET IMAGE f s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:B` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`{y:B}`; `{}:B->bool`]) THEN ASM SET_TAC[]);;

export_namedthm INJECTIVE_ON_PREIMAGE "INJECTIVE_ON_PREIMAGE";;

let SURJECTIVE_ON_PREIMAGE = prove 
 (`!f:A->B s u.
        (!k. k SUBSET s
             ==> ?t. t SUBSET u /\ {x | x IN s /\ f x IN t} = k) <=>
        IMAGE f s SUBSET u /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `{x:A}`) THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `{x:A}`) THEN ASM SET_TAC[]];
    X_GEN_TAC `k:A->bool` THEN STRIP_TAC THEN
    EXISTS_TAC `IMAGE (f:A->B) k` THEN ASM SET_TAC[]]);;

export_namedthm SURJECTIVE_ON_PREIMAGE "SURJECTIVE_ON_PREIMAGE";;

let INJECTIVE_PREIMAGE = prove 
 (`!f:A->B.
        (!t t'. {x | f x IN t} = {x | f x IN t'} ==> t = t') <=>
        IMAGE f UNIV = UNIV`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `(:A)`; `(:B)`]
        INJECTIVE_ON_PREIMAGE) THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV] THEN SET_TAC[]);;

export_namedthm INJECTIVE_PREIMAGE "INJECTIVE_PREIMAGE";;

let SURJECTIVE_PREIMAGE = prove 
 (`!f:A->B. (!k. ?t. {x | f x IN t} = k) <=> (!x y. f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `(:A)`; `(:B)`]
        SURJECTIVE_ON_PREIMAGE) THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV] THEN SET_TAC[]);;

export_namedthm SURJECTIVE_PREIMAGE "SURJECTIVE_PREIMAGE";;

(* ------------------------------------------------------------------------- *)
(* Existence of bijections between two finite sets of same size.             *)
(* ------------------------------------------------------------------------- *)

export_theory "set-bijections";;

let CARD_EQ_BIJECTION = prove 
 (`!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?f:A->B. (!x. x IN s ==> f(x) IN t) /\
                (!y. y IN t ==> ?x. x IN s /\ f x = y) /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  MP_TAC CARD_LE_INJ THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[SURJECTIVE_IFF_INJECTIVE_GEN] THEN
  MESON_TAC[SUBSET; IN_IMAGE]);;

export_namedthm CARD_EQ_BIJECTION "CARD_EQ_BIJECTION";;

let CARD_EQ_BIJECTIONS = prove 
 (`!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?f:A->B g. (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
                  (!y. y IN t ==> g(y) IN s /\ f(g y) = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CARD_EQ_BIJECTION) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[SURJECTIVE_ON_RIGHT_INVERSE] THEN
  GEN_TAC THEN REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]);;

export_namedthm CARD_EQ_BIJECTIONS "CARD_EQ_BIJECTIONS";;

let BIJECTIONS_HAS_SIZE = prove 
 (`!s t f:A->B g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y) /\
        s HAS_SIZE n
        ==> t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `t = IMAGE (f:A->B) s` SUBST_ALL_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_MESON_TAC[]]);;

export_namedthm BIJECTIONS_HAS_SIZE "BIJECTIONS_HAS_SIZE";;

let BIJECTIONS_HAS_SIZE_EQ = prove 
 (`!s t f:A->B g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y)
        ==> !n. s HAS_SIZE n <=> t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE
  [TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`] BIJECTIONS_HAS_SIZE) THENL
   [MAP_EVERY EXISTS_TAC [`f:A->B`; `g:B->A`];
    MAP_EVERY EXISTS_TAC [`g:B->A`; `f:A->B`]] THEN
  ASM_MESON_TAC[]);;

export_namedthm BIJECTIONS_HAS_SIZE_EQ "BIJECTIONS_HAS_SIZE_EQ";;

let BIJECTIONS_CARD_EQ = prove 
 (`!s t f:A->B g.
        (FINITE s \/ FINITE t) /\
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y)
        ==> CARD s = CARD t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   MP_TAC (MP_TAC o MATCH_MP BIJECTIONS_HAS_SIZE_EQ)) THEN
  MESON_TAC[HAS_SIZE]);;

export_namedthm BIJECTIONS_CARD_EQ "BIJECTIONS_CARD_EQ";;

(* ------------------------------------------------------------------------- *)
(* Transitive relation with finitely many predecessors is wellfounded.       *)
(* ------------------------------------------------------------------------- *)

export_theory "set-wf";;

let WF_FINITE = prove 
 (`!(<<). (!x. ~(x << x)) /\ (!x y z. x << y /\ y << z ==> x << z) /\
          (!x:A. FINITE {y | y << x})
          ==> WF(<<)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WF_DCHAIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!m n. m < n ==> (s:num->A) n << s m` ASSUME_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:num->A` INFINITE_IMAGE_INJ) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[LT_CASES]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(:num)`) THEN
  REWRITE_TAC[num_INFINITE] THEN REWRITE_TAC[INFINITE] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `s(0) INSERT {y:A | y << s(0)}` THEN
  ASM_REWRITE_TAC[FINITE_INSERT] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_INSERT] THEN
  INDUCT_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[LT_0]);;

export_namedthm WF_FINITE "WF_FINITE";;

let WF_PSUBSET = prove 
 (`!s:A->bool. FINITE s ==> WF (\t1 t2. t1 PSUBSET t2 /\ t2 SUBSET s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WF_FINITE THEN SIMP_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [SET_TAC[]; X_GEN_TAC `t:A->bool`] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]);;

export_namedthm WF_PSUBSET "WF_PSUBSET";;

(* ------------------------------------------------------------------------- *)
(* Cardinal comparisons (more theory in Library/card.ml)                     *)
(* ------------------------------------------------------------------------- *)

export_theory "set-card-comp";;

let le_c = new_definition 
  `s <=_c t <=> ?f. (!x. x IN s ==> f(x) IN t) /\
                    (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y))`;;

export_namedthm le_c "le_c";;

let lt_c = new_definition 
  `s <_c t <=> s <=_c t /\ ~(t <=_c s)`;;

export_namedthm lt_c "lt_c";;

let eq_c = new_definition 
  `s =_c t <=> ?f. (!x. x IN s ==> f(x) IN t) /\
                   !y. y IN t ==> ?!x. x IN s /\ (f x = y)`;;

export_namedthm eq_c "eq_c";;

let ge_c = new_definition 
 `s >=_c t <=> t <=_c s`;;

export_namedthm ge_c "ge_c";;

let gt_c = new_definition 
 `s >_c t <=> t <_c s`;;

export_namedthm gt_c "gt_c";;

let LE_C = prove 
 (`!s t. s <=_c t <=> ?g. !x. x IN s ==> ?y. y IN t /\ (g y = x)`,
  REWRITE_TAC[le_c; INJECTIVE_ON_LEFT_INVERSE; SURJECTIVE_ON_RIGHT_INVERSE;
              RIGHT_IMP_EXISTS_THM; SKOLEM_THM; RIGHT_AND_EXISTS_THM] THEN
  MESON_TAC[]);;

export_namedthm LE_C "LE_C";;

let GE_C = prove 
 (`!s t. s >=_c t <=> ?f. !y. y IN t ==> ?x. x IN s /\ (y = f x)`,
  REWRITE_TAC[ge_c; LE_C] THEN MESON_TAC[]);;

export_namedthm GE_C "GE_C";;

let COUNTABLE = new_definition 
  `COUNTABLE t <=> (:num) >=_c t`;;

export_namedthm COUNTABLE "COUNTABLE";;

(* ------------------------------------------------------------------------- *)
(* Supremum and infimum.                                                     *)
(* ------------------------------------------------------------------------- *)

export_theory "set-sup-inf";;

let sup = new_definition 
  `sup s = @a:real. (!x. x IN s ==> x <= a) /\
                    !b. (!x. x IN s ==> x <= b) ==> a <= b`;;

export_namedthm sup "sup";;

let SUP_EQ = prove 
 (`!s t. (!b. (!x. x IN s ==> x <= b) <=> (!x. x IN t ==> x <= b))
         ==> sup s = sup t`,
  SIMP_TAC[sup]);;

export_namedthm SUP_EQ "SUP_EQ";;

let SUP = prove 
 (`!s. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b)
       ==> (!x. x IN s ==> x <= sup s) /\
           !b. (!x. x IN s ==> x <= b) ==> sup s <= b`,
  REWRITE_TAC[sup] THEN CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_COMPLETE THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY]);;

export_namedthm SUP "SUP";;

let SUP_FINITE_LEMMA = prove 
 (`!s. FINITE s /\ ~(s = {}) ==> ?b:real. b IN s /\ !x. x IN s ==> x <= b`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; IN_INSERT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_TRANS]);;

export_namedthm SUP_FINITE_LEMMA "SUP_FINITE_LEMMA";;

let SUP_FINITE = prove 
 (`!s. FINITE s /\ ~(s = {}) ==> (sup s) IN s /\ !x. x IN s ==> x <= sup s`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUP_FINITE_LEMMA) THEN
  ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_LE_TOTAL; SUP]);;

export_namedthm SUP_FINITE "SUP_FINITE";;

let REAL_LE_SUP_FINITE = prove 
 (`!s a. FINITE s /\ ~(s = {}) ==> (a <= sup s <=> ?x. x IN s /\ a <= x)`,
  MESON_TAC[SUP_FINITE; REAL_LE_TRANS]);;

export_namedthm REAL_LE_SUP_FINITE "REAL_LE_SUP_FINITE";;

let REAL_SUP_LE_FINITE = prove 
 (`!s a. FINITE s /\ ~(s = {}) ==> (sup s <= a <=> !x. x IN s ==> x <= a)`,
  MESON_TAC[SUP_FINITE; REAL_LE_TRANS]);;

export_namedthm REAL_SUP_LE_FINITE "REAL_SUP_LE_FINITE";;

let REAL_LT_SUP_FINITE = prove 
 (`!s a. FINITE s /\ ~(s = {}) ==> (a < sup s <=> ?x. x IN s /\ a < x)`,
  MESON_TAC[SUP_FINITE; REAL_LTE_TRANS]);;

export_namedthm REAL_LT_SUP_FINITE "REAL_LT_SUP_FINITE";;

let REAL_SUP_LT_FINITE = prove 
 (`!s a. FINITE s /\ ~(s = {}) ==> (sup s < a <=> !x. x IN s ==> x < a)`,
  MESON_TAC[SUP_FINITE; REAL_LET_TRANS]);;

export_namedthm REAL_SUP_LT_FINITE "REAL_SUP_LT_FINITE";;

let REAL_SUP_UNIQUE = prove 
 (`!s b. (!x. x IN s ==> x <= b) /\
         (!b'. b' < b ==> ?x. x IN s /\ b' < x)
         ==> sup s = b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sup] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  ASM_MESON_TAC[REAL_NOT_LE; REAL_LE_ANTISYM]);;

export_namedthm REAL_SUP_UNIQUE "REAL_SUP_UNIQUE";;

let REAL_SUP_LE = prove 
 (`!b. ~(s = {}) /\ (!x. x IN s ==> x <= b) ==> sup s <= b`,
  MESON_TAC[SUP]);;

export_namedthm REAL_SUP_LE "REAL_SUP_LE";;

let REAL_SUP_LE_SUBSET = prove 
 (`!s t. ~(s = {}) /\ s SUBSET t /\ (?b. !x. x IN t ==> x <= b)
         ==> sup s <= sup t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_LE THEN
  MP_TAC(SPEC `t:real->bool` SUP) THEN ASM SET_TAC[]);;

export_namedthm REAL_SUP_LE_SUBSET "REAL_SUP_LE_SUBSET";;

let REAL_SUP_BOUNDS = prove 
 (`!s a b. ~(s = {}) /\ (!x. x IN s ==> a <= x /\ x <= b)
           ==> a <= sup s /\ sup s <= b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` SUP) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

export_namedthm REAL_SUP_BOUNDS "REAL_SUP_BOUNDS";;

let REAL_ABS_SUP_LE = prove 
 (`!s a. ~(s = {}) /\ (!x. x IN s ==> abs(x) <= a) ==> abs(sup s) <= a`,
  REWRITE_TAC[GSYM REAL_BOUNDS_LE; REAL_SUP_BOUNDS]);;

export_namedthm REAL_ABS_SUP_LE "REAL_ABS_SUP_LE";;

let REAL_SUP_ASCLOSE = prove 
 (`!s l e. ~(s = {}) /\ (!x. x IN s ==> abs(x - l) <= e)
           ==> abs(sup s - l) <= e`,
  SIMP_TAC[REAL_ARITH `abs(x - l):real <= e <=> l - e <= x /\ x <= l + e`] THEN
  REWRITE_TAC[REAL_SUP_BOUNDS]);;

export_namedthm REAL_SUP_ASCLOSE "REAL_SUP_ASCLOSE";;

let SUP_UNIQUE_FINITE = prove 
 (`!s. FINITE s /\ ~(s = {})
       ==> (sup s = a <=> a IN s /\ !y. y IN s ==> y <= a)`,
   ASM_SIMP_TAC[GSYM REAL_LE_ANTISYM; REAL_LE_SUP_FINITE; REAL_SUP_LE_FINITE;
               NOT_INSERT_EMPTY; FINITE_INSERT; FINITE_EMPTY] THEN
   MESON_TAC[REAL_LE_REFL; REAL_LE_TRANS; REAL_LE_ANTISYM]);;

export_namedthm SUP_UNIQUE_FINITE "SUP_UNIQUE_FINITE";;

let SUP_INSERT_FINITE = prove 
 (`!x s. FINITE s ==> sup(x INSERT s) = if s = {} then x else max x (sup s)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SUP_UNIQUE_FINITE;  FINITE_INSERT; FINITE_EMPTY;
               NOT_INSERT_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_SING; REAL_LE_REFL] THEN
  REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SUP_FINITE; IN_INSERT; REAL_LE_REFL] THEN
  ASM_MESON_TAC[SUP_FINITE; REAL_LE_TOTAL; REAL_LE_TRANS]);;

export_namedthm SUP_INSERT_FINITE "SUP_INSERT_FINITE";;

let SUP_SING = prove 
 (`!a. sup {a} = a`,
  SIMP_TAC[SUP_INSERT_FINITE; FINITE_EMPTY]);;

export_namedthm SUP_SING "SUP_SING";;

let SUP_INSERT_INSERT = prove 
 (`!a b s. sup (b INSERT a INSERT s) = sup (max a b INSERT s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUP_EQ THEN
  X_GEN_TAC `c:real` THEN REWRITE_TAC[FORALL_IN_INSERT] THEN
  ASM_CASES_TAC `!x:real. x IN s ==> x <= c` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

export_namedthm SUP_INSERT_INSERT "SUP_INSERT_INSERT";;

let REAL_LE_SUP = prove 
 (`!s a b y. y IN s /\ a <= y /\ (!x. x IN s ==> x <= b) ==> a <= sup s`,
  MESON_TAC[SUP; MEMBER_NOT_EMPTY; REAL_LE_TRANS]);;

export_namedthm REAL_LE_SUP "REAL_LE_SUP";;

let REAL_SUP_LE_EQ = prove 
 (`!s y. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b)
         ==> (sup s <= y <=> !x. x IN s ==> x <= y)`,
  MESON_TAC[SUP; REAL_LE_TRANS]);;

export_namedthm REAL_SUP_LE_EQ "REAL_SUP_LE_EQ";;

let SUP_UNIQUE = prove 
 (`!s b. (!c. (!x. x IN s ==> x <= c) <=> b <= c) ==> sup s = b`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM SUP_SING] THEN
  MATCH_MP_TAC SUP_EQ THEN ASM SET_TAC[]);;

export_namedthm SUP_UNIQUE "SUP_UNIQUE";;

let SUP_UNION = prove 
 (`!s t. ~(s = {}) /\ ~(t = {}) /\
         (?b. !x. x IN s ==> x <= b) /\ (?c. !x. x IN t ==> x <= c)
         ==> sup(s UNION t) = max (sup s) (sup t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUP_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_UNION; REAL_MAX_LE] THEN
  ASM_MESON_TAC[SUP; REAL_LE_TRANS]);;

export_namedthm SUP_UNION "SUP_UNION";;

let ELEMENT_LE_SUP = prove 
 (`!s a. (?b. !x. x IN s ==> x <= b) /\ a IN s ==> a <= sup s`,
  MESON_TAC[REAL_LE_SUP; REAL_LE_REFL]);;

export_namedthm ELEMENT_LE_SUP "ELEMENT_LE_SUP";;

let SUP_APPROACH = prove 
 (`!s c. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b) /\ c < sup s
         ==> ?x. x IN s /\ c < x`,
  INTRO_TAC "!s c; npty bound lt" THEN
  REFUTE_THEN (LABEL_TAC "hp" o
    REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  REMOVE_THEN "lt" MP_TAC THEN REWRITE_TAC[REAL_NOT_LT] THEN
  HYP (MP_TAC o MATCH_MP SUP o end_itlist CONJ) "npty bound" [] THEN
  INTRO_TAC "_ sup" THEN REMOVE_THEN "sup" MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

export_namedthm SUP_APPROACH "SUP_APPROACH";;

let REAL_MAX_SUP = prove 
 (`!x y. max x y = sup {x,y}`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; REAL_SUP_LE_FINITE; REAL_LE_SUP_FINITE;
           FINITE_RULES; NOT_INSERT_EMPTY; REAL_MAX_LE; REAL_LE_MAX] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LE_TOTAL]);;

export_namedthm REAL_MAX_SUP "REAL_MAX_SUP";;

let inf = new_definition 
  `inf s = @a:real. (!x. x IN s ==> a <= x) /\
                    !b. (!x. x IN s ==> b <= x) ==> b <= a`;;

export_namedthm inf "inf";;

let INF_EQ = prove 
 (`!s t. (!a. (!x. x IN s ==> a <= x) <=> (!x. x IN t ==> a <= x))
         ==> inf s = inf t`,
  SIMP_TAC[inf]);;

export_namedthm INF_EQ "INF_EQ";;

let INF = prove 
 (`!s. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)
       ==> (!x. x IN s ==> inf s <= x) /\
           !b. (!x. x IN s ==> b <= x) ==> b <= inf s`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[inf] THEN
  CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_NEG2] THEN
  EXISTS_TAC `--(sup (IMAGE (--) s))` THEN
  MP_TAC(SPEC `IMAGE (--) (s:real->bool)` SUP) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  ABBREV_TAC `a = sup (IMAGE (--) s)` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_IMAGE] THEN
  ASM_MESON_TAC[REAL_NEG_NEG; MEMBER_NOT_EMPTY; REAL_LE_NEG2]);;

export_namedthm INF "INF";;

let INF_FINITE_LEMMA = prove 
 (`!s. FINITE s /\ ~(s = {}) ==> ?b:real. b IN s /\ !x. x IN s ==> b <= x`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; IN_INSERT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_TRANS]);;

export_namedthm INF_FINITE_LEMMA "INF_FINITE_LEMMA";;

let INF_FINITE = prove 
 (`!s. FINITE s /\ ~(s = {}) ==> (inf s) IN s /\ !x. x IN s ==> inf s <= x`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INF_FINITE_LEMMA) THEN
  ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_LE_TOTAL; INF]);;

export_namedthm INF_FINITE "INF_FINITE";;

let REAL_LE_INF_FINITE = prove 
(`!s a. FINITE s /\ ~(s = {}) ==> (a <= inf s <=> !x. x IN s ==> a <= x)`,
  MESON_TAC[INF_FINITE; REAL_LE_TRANS]);;

export_namedthm REAL_LE_INF_FINITE "REAL_LE_INF_FINITE";;

let REAL_INF_LE_FINITE = prove 
 (`!s a. FINITE s /\ ~(s = {}) ==> (inf s <= a <=> ?x. x IN s /\ x <= a)`,
  MESON_TAC[INF_FINITE; REAL_LE_TRANS]);;

export_namedthm REAL_INF_LE_FINITE "REAL_INF_LE_FINITE";;

let REAL_LT_INF_FINITE = prove 
 (`!s a. FINITE s /\ ~(s = {}) ==> (a < inf s <=> !x. x IN s ==> a < x)`,
  MESON_TAC[INF_FINITE; REAL_LTE_TRANS]);;

export_namedthm REAL_LT_INF_FINITE "REAL_LT_INF_FINITE";;

let REAL_INF_LT_FINITE = prove 
 (`!s a. FINITE s /\ ~(s = {}) ==> (inf s < a <=> ?x. x IN s /\ x < a)`,
  MESON_TAC[INF_FINITE; REAL_LET_TRANS]);;

export_namedthm REAL_INF_LT_FINITE "REAL_INF_LT_FINITE";;

let REAL_INF_UNIQUE = prove 
 (`!s b. (!x. x IN s ==> b <= x) /\
         (!b'. b < b' ==> ?x. x IN s /\ x < b')
         ==> inf s = b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inf] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  ASM_MESON_TAC[REAL_NOT_LE; REAL_LE_ANTISYM]);;

export_namedthm REAL_INF_UNIQUE "REAL_INF_UNIQUE";;

let REAL_LE_INF = prove 
 (`!b. ~(s = {}) /\ (!x. x IN s ==> b <= x) ==> b <= inf s`,
  MESON_TAC[INF]);;

export_namedthm REAL_LE_INF "REAL_LE_INF";;

let REAL_LE_INF_SUBSET = prove 
 (`!s t. ~(t = {}) /\ t SUBSET s /\ (?b. !x. x IN s ==> b <= x)
         ==> inf s <= inf t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INF THEN
  MP_TAC(SPEC `s:real->bool` INF) THEN ASM SET_TAC[]);;

export_namedthm REAL_LE_INF_SUBSET "REAL_LE_INF_SUBSET";;

let REAL_INF_BOUNDS = prove 
 (`!s a b. ~(s = {}) /\ (!x. x IN s ==> a <= x /\ x <= b)
           ==> a <= inf s /\ inf s <= b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` INF) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

export_namedthm REAL_INF_BOUNDS "REAL_INF_BOUNDS";;

let REAL_ABS_INF_LE = prove 
 (`!s a. ~(s = {}) /\ (!x. x IN s ==> abs(x) <= a) ==> abs(inf s) <= a`,
  REWRITE_TAC[GSYM REAL_BOUNDS_LE; REAL_INF_BOUNDS]);;

export_namedthm REAL_ABS_INF_LE "REAL_ABS_INF_LE";;

let REAL_INF_ASCLOSE = prove 
 (`!s l e. ~(s = {}) /\ (!x. x IN s ==> abs(x - l) <= e)
           ==> abs(inf s - l) <= e`,
  SIMP_TAC[REAL_ARITH `abs(x - l):real <= e <=> l - e <= x /\ x <= l + e`] THEN
  REWRITE_TAC[REAL_INF_BOUNDS]);;

export_namedthm REAL_INF_ASCLOSE "REAL_INF_ASCLOSE";;

let INF_UNIQUE_FINITE = prove 
 (`!s. FINITE s /\ ~(s = {})
       ==> (inf s = a <=> a IN s /\ !y. y IN s ==> a <= y)`,
   ASM_SIMP_TAC[GSYM REAL_LE_ANTISYM; REAL_LE_INF_FINITE; REAL_INF_LE_FINITE;
               NOT_INSERT_EMPTY; FINITE_INSERT; FINITE_EMPTY] THEN
   MESON_TAC[REAL_LE_REFL; REAL_LE_TRANS; REAL_LE_ANTISYM]);;

export_namedthm INF_UNIQUE_FINITE "INF_UNIQUE_FINITE";;

let INF_INSERT_FINITE = prove 
 (`!x s. FINITE s ==> inf(x INSERT s) = if s = {} then x else min x (inf s)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[INF_UNIQUE_FINITE;  FINITE_INSERT; FINITE_EMPTY;
               NOT_INSERT_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_SING; REAL_LE_REFL] THEN
  REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[INF_FINITE; IN_INSERT; REAL_LE_REFL] THEN
  ASM_MESON_TAC[INF_FINITE; REAL_LE_TOTAL; REAL_LE_TRANS]);;

export_namedthm INF_INSERT_FINITE "INF_INSERT_FINITE";;

let INF_SING = prove 
 (`!a. inf {a} = a`,
  SIMP_TAC[INF_INSERT_FINITE; FINITE_EMPTY]);;

export_namedthm INF_SING "INF_SING";;

let INF_INSERT_INSERT = prove 
 (`!a b s. inf (b INSERT a INSERT s) = inf (min a b INSERT s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INF_EQ THEN
  X_GEN_TAC `c:real` THEN REWRITE_TAC[FORALL_IN_INSERT] THEN
  ASM_CASES_TAC `!x:real. x IN s ==> c <= x` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

export_namedthm INF_INSERT_INSERT "INF_INSERT_INSERT";;

let REAL_SUP_EQ_INF = prove 
 (`!s. ~(s = {}) /\ (?B. !x. x IN s ==> abs(x) <= B)
       ==> (sup s = inf s <=> ?a. s = {a})`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `sup s` THEN MATCH_MP_TAC
     (SET_RULE `~(s = {}) /\ (!x. x IN s ==> x = a) ==> s = {a}`) THEN
    ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    ASM_MESON_TAC[SUP; REAL_ABS_BOUNDS; INF];
    STRIP_TAC THEN
    ASM_SIMP_TAC[SUP_INSERT_FINITE; INF_INSERT_FINITE; FINITE_EMPTY]]);;

export_namedthm REAL_SUP_EQ_INF "REAL_SUP_EQ_INF";;

let REAL_INF_LE = prove 
 (`!s a b y. y IN s /\ y <= b /\ (!x. x IN s ==> a <= x) ==> inf s <= b`,
  MESON_TAC[INF; MEMBER_NOT_EMPTY; REAL_LE_TRANS]);;

export_namedthm REAL_INF_LE "REAL_INF_LE";;

let REAL_LE_INF_EQ = prove 
 (`!s t. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)
         ==> (y <= inf s <=> !x. x IN s ==> y <= x)`,
  MESON_TAC[INF; REAL_LE_TRANS]);;

export_namedthm REAL_LE_INF_EQ "REAL_LE_INF_EQ";;

let INF_UNIQUE = prove 
 (`!s b. (!c. (!x. x IN s ==> c <= x) <=> c <= b) ==> inf s = b`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM INF_SING] THEN
  MATCH_MP_TAC INF_EQ THEN ASM SET_TAC[]);;

export_namedthm INF_UNIQUE "INF_UNIQUE";;

let INF_UNION = prove 
 (`!s t. ~(s = {}) /\ ~(t = {}) /\
         (?b. !x. x IN s ==> b <= x) /\ (?c. !x. x IN t ==> c <= x)
         ==> inf(s UNION t) = min (inf s) (inf t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INF_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_UNION; REAL_LE_MIN] THEN
  ASM_MESON_TAC[INF; REAL_LE_TRANS]);;

export_namedthm INF_UNION "INF_UNION";;

let INF_LE_ELEMENT = prove 
 (`!s a. (?b. !x. x IN s ==> b <= x) /\ a IN s ==> inf s <= a`,
  MESON_TAC[REAL_INF_LE; REAL_LE_REFL]);;

export_namedthm INF_LE_ELEMENT "INF_LE_ELEMENT";;

let INF_APPROACH = prove 
 (`!s c. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x) /\ inf s < c
         ==> ?x. x IN s /\ x < c`,
  INTRO_TAC "!s c; npty bound lt" THEN
  REFUTE_THEN (LABEL_TAC "hp" o
    REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  REMOVE_THEN "lt" MP_TAC THEN REWRITE_TAC[REAL_NOT_LT] THEN
  HYP (MP_TAC o MATCH_MP INF o end_itlist CONJ) "npty bound" [] THEN
  INTRO_TAC "_ inf" THEN REMOVE_THEN "inf" MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

export_namedthm INF_APPROACH "INF_APPROACH";;

let REAL_MIN_INF = prove 
 (`!x y. min x y = inf {x,y}`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; REAL_INF_LE_FINITE; REAL_LE_INF_FINITE;
           FINITE_RULES; NOT_INSERT_EMPTY; REAL_MIN_LE; REAL_LE_MIN] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LE_TOTAL]);;

export_namedthm REAL_MIN_INF "REAL_MIN_INF";;

(* ------------------------------------------------------------------------- *)
(* Relational counterparts of sup and inf.                                   *)
(* ------------------------------------------------------------------------- *)

export_theory "set-sup-inf-rel";;

parse_as_infix ("has_inf",(12,"right"));;
parse_as_infix ("has_sup",(12,"right"));;

let has_inf = new_definition 
  `s has_inf b <=> (!c. (!x:real. x IN s ==> c <= x) <=> c <= b)`;;

export_namedthm has_inf "has_inf";;

let has_sup = new_definition 
  `s has_sup b <=> (!c. (!x:real. x IN s ==> x <= c) <=> b <= c)`;;

export_namedthm has_sup "has_sup";;

let HAS_INF_LBOUND = prove 
 (`!s b x. s has_inf b /\ x IN s ==> b <= x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_inf] THEN MESON_TAC[REAL_LE_REFL]);;

export_namedthm HAS_INF_LBOUND "HAS_INF_LBOUND";;

let HAS_SUP_UBOUND = prove 
 (`!s b x. s has_sup b /\ x IN s ==> x <= b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_sup] THEN MESON_TAC[REAL_LE_REFL]);;

export_namedthm HAS_SUP_UBOUND "HAS_SUP_UBOUND";;

let HAS_INF_INF = prove 
 (`!s l. s has_inf l <=>
         ~(s = {}) /\
         (?b. !x. x IN s ==> b <= x) /\
         inf s = l`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[has_inf] THEN
  EQ_TAC THEN STRIP_TAC THENL
  [CONJ_TAC THENL
   [REFUTE_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_IN_EMPTY; NOT_FORALL_THM] THEN
    EXISTS_TAC `l + &1:real` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
   MATCH_MP_TAC INF_UNIQUE THEN ASM_REWRITE_TAC[];
   GEN_TAC THEN MP_TAC (SPEC `s:real->bool` INF) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   POP_ASSUM SUBST_ALL_TAC THEN STRIP_TAC THEN EQ_TAC THEN
   ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   TRANS_TAC REAL_LE_TRANS `l:real` THEN ASM_SIMP_TAC[]]);;

export_namedthm HAS_INF_INF "HAS_INF_INF";;

let HAS_SUP_SUP = prove 
 (`!s l. s has_sup l <=>
         ~(s = {}) /\
         (?b. !x. x IN s ==> x <= b) /\
         sup s = l`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[has_sup] THEN
  EQ_TAC THEN STRIP_TAC THENL
  [CONJ_TAC THENL
   [REFUTE_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_IN_EMPTY; NOT_FORALL_THM] THEN
    EXISTS_TAC `l - &1:real` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
   MATCH_MP_TAC SUP_UNIQUE THEN ASM_REWRITE_TAC[];
   GEN_TAC THEN MP_TAC (SPEC `s:real->bool` SUP) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   POP_ASSUM SUBST_ALL_TAC THEN STRIP_TAC THEN EQ_TAC THEN
   ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   TRANS_TAC REAL_LE_TRANS `l:real` THEN ASM_SIMP_TAC[]]);;

export_namedthm HAS_SUP_SUP "HAS_SUP_SUP";;

let INF_EXISTS = prove 
 (`!s. (?l. s has_inf l) <=> ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)`,
  MESON_TAC[HAS_INF_INF]);;

export_namedthm INF_EXISTS "INF_EXISTS";;

let SUP_EXISTS = prove 
 (`!s. (?l. s has_sup l) <=> ~(s = {}) /\ (?b. !x. x IN s ==> x <= b)`,
  MESON_TAC[HAS_SUP_SUP]);;

export_namedthm SUP_EXISTS "SUP_EXISTS";;

let HAS_INF_APPROACH = prove 
 (`!s l c. s has_inf l /\ l < c ==> ?x. x IN s /\ x < c`,
  REWRITE_TAC[HAS_INF_INF] THEN MESON_TAC[INF_APPROACH]);;

export_namedthm HAS_INF_APPROACH "HAS_INF_APPROACH";;

let HAS_SUP_APPROACH = prove 
 (`!s l c. s has_sup l /\ c < l ==> ?x. x IN s /\ c < x`,
  REWRITE_TAC[HAS_SUP_SUP] THEN MESON_TAC[SUP_APPROACH]);;

export_namedthm HAS_SUP_APPROACH "HAS_SUP_APPROACH";;

let HAS_INF = prove 
 (`!s l. s has_inf l <=>
         ~(s = {}) /\
         (!x. x IN s ==> l <= x) /\
         (!c. l < c ==> ?x. x IN s /\ x < c)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [INTRO_TAC "hp" THEN CONJ_TAC THENL
   [HYP_TAC "hp" (REWRITE_RULE[HAS_INF_INF]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[HAS_INF_LBOUND]; ASM_MESON_TAC[HAS_INF_APPROACH]];
   ALL_TAC] THEN
  INTRO_TAC "ne bound approach" THEN ASM_REWRITE_TAC[has_inf] THEN
  GEN_TAC THEN EQ_TAC THENL
  [INTRO_TAC "hp" THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN INTRO_TAC "lc" THEN
   REMOVE_THEN "approach" (MP_TAC o SPEC `(l + c) / &2`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; INTRO_TAC "@x0. x0 +"] THEN
   USE_THEN "x0" (HYP_TAC "hp" o C MATCH_MP) THEN ASM_REAL_ARITH_TAC;
   INTRO_TAC "hp; !x; x" THEN TRANS_TAC REAL_LE_TRANS `l:real` THEN
   ASM_SIMP_TAC[]]);;

export_namedthm HAS_INF "HAS_INF";;

let HAS_SUP = prove 
 (`!s l. s has_sup l <=>
         ~(s = {}) /\
         (!x. x IN s ==> x <= l) /\
         (!c. c < l ==> ?x. x IN s /\ c < x)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [INTRO_TAC "hp" THEN CONJ_TAC THENL
   [HYP_TAC "hp" (REWRITE_RULE[HAS_SUP_SUP]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[HAS_SUP_UBOUND]; ASM_MESON_TAC[HAS_SUP_APPROACH]];
   ALL_TAC] THEN
  INTRO_TAC "ne bound approach" THEN ASM_REWRITE_TAC[has_sup] THEN
  GEN_TAC THEN EQ_TAC THENL
  [INTRO_TAC "hp" THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN INTRO_TAC "lc" THEN
   REMOVE_THEN "approach" (MP_TAC o SPEC `(l + c) / &2`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; INTRO_TAC "@x0. x0 +"] THEN
   USE_THEN "x0" (HYP_TAC "hp" o C MATCH_MP) THEN ASM_REAL_ARITH_TAC;
   INTRO_TAC "hp; !x; x" THEN TRANS_TAC REAL_LE_TRANS `l:real` THEN
   ASM_SIMP_TAC[]]);;

export_namedthm HAS_SUP "HAS_SUP";;

let HAS_INF_LE = prove 
 (`!s t l m. s has_inf l /\ t has_inf m /\
             (!y. y IN t ==> ?x. x IN s /\ x <= y)
             ==> l <= m`,
  INTRO_TAC "!s t l m; l m le" THEN
  HYP_TAC "l: s l1 l2" (REWRITE_RULE[HAS_INF]) THEN
  HYP_TAC "m: t m1 m2" (REWRITE_RULE[HAS_INF]) THEN
  REFUTE_THEN (LABEL_TAC "lt" o REWRITE_RULE[REAL_NOT_LE]) THEN
  CLAIM_TAC "@c. c1 c2" `?c:real. m < c /\ c < l` THENL
  [EXISTS_TAC `(l + m) / &2` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  HYP_TAC "m2: +" (SPEC `c:real`) THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  INTRO_TAC "!x; x xc" THEN
  CLAIM_TAC "@y. y yx" `?y:real. y IN s /\ y <= x` THENL
  [HYP MESON_TAC "le x" []; ALL_TAC] THEN
  HYP_TAC "l1: +" (SPEC `y:real`) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

export_namedthm HAS_INF_LE "HAS_INF_LE";;

let HAS_SUP_LE = prove 
 (`!s t l m. s has_sup l /\ t has_sup m /\
             (!y. y IN t ==> ?x. x IN s /\ y <= x)
             ==> m <= l`,
  INTRO_TAC "!s t l m; l m le" THEN
  HYP_TAC "l: s l1 l2" (REWRITE_RULE[HAS_SUP]) THEN
  HYP_TAC "m: t m1 m2" (REWRITE_RULE[HAS_SUP]) THEN
  REFUTE_THEN (LABEL_TAC "lt" o REWRITE_RULE[REAL_NOT_LE]) THEN
  CLAIM_TAC "@c. c1 c2" `?c:real. l < c /\ c < m` THENL
  [EXISTS_TAC `(l + m) / &2` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  HYP_TAC "m2: +" (SPEC `c:real`) THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  INTRO_TAC "!x; x xc" THEN
  CLAIM_TAC "@y. y yx" `?y:real. y IN s /\ x <= y` THENL
  [HYP MESON_TAC "le x" []; ALL_TAC] THEN
  HYP_TAC "l1: +" (SPEC `y:real`) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

export_namedthm HAS_SUP_LE "HAS_SUP_LE";;

(* ------------------------------------------------------------------------- *)
(* Inductive definition of sets, by reducing them to inductive relations.    *)
(* ------------------------------------------------------------------------- *)

let new_inductive_set =
  let const_of_var v = mk_mconst(name_of v,type_of v) in
  let comb_all =
    let rec f (n:int) (tm:term) : hol_type list -> term = function
      | [] -> tm
      | ty::tys ->
          let v = variant (variables tm) (mk_var("x"^string_of_int n,ty)) in
          f (n+1) (mk_comb(tm,v)) tys in
    fun tm -> let tys = fst (splitlist dest_fun_ty (type_of tm)) in
              f 0 tm tys in
  let mk_eqin = REWR_CONV (GSYM IN) o comb_all in
  let transf conv = rhs o concl o conv in
  let remove_in_conv ptm : conv =
    let rconv = REWR_CONV(SYM(mk_eqin ptm)) in
    fun tm -> let htm = fst(strip_comb(snd(dest_binary "IN" tm))) in
              if htm = ptm then rconv tm else fail() in
  let remove_in_transf =
    transf o ONCE_DEPTH_CONV o FIRST_CONV o map remove_in_conv in
  let rule_head tm =
    let tm = snd(strip_forall tm) in
    let tm = snd(splitlist(dest_binop `(==>)`) tm) in
    let tm = snd(dest_binary "IN" tm) in
    fst(strip_comb tm) in
  let find_pvars = setify o map rule_head o binops `(/\)` in
  fun tm ->
    let pvars = find_pvars tm in
    let dtm = remove_in_transf pvars tm in
    let th_rules, th_induct, th_cases = new_inductive_definition dtm in
    let insert_in_rule = REWRITE_RULE(map (mk_eqin o const_of_var) pvars) in
    insert_in_rule th_rules,
    insert_in_rule th_induct,
    insert_in_rule th_cases;;
