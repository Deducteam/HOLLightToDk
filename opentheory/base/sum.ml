(* ========================================================================= *)
(* SUM TYPES                                                                 *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Properties of sum types.                                                  *)
(* ------------------------------------------------------------------------- *)

export_theory "sum-thm";;

let sum_distinct = prove
 (`!(a : A) (b : B). ~(INL a = INR b)`,
  MATCH_ACCEPT_TAC (prove_constructors_distinct sum_RECURSION));;

export_namedthm sum_distinct "sum_distinct";;

let (inl_inj,inr_inj) = (CONJ_PAIR o prove)
 (`(!a b. (INL a : A + B) = INL b <=> a = b) /\
   (!a b. (INR a : A + B) = INR b <=> a = b)`,
  MATCH_ACCEPT_TAC (prove_constructors_injective sum_RECURSION));;

export_namedthm inl_inj "inl_inj";;
export_namedthm inr_inj "inr_inj";;

let sum_inj = CONJ inl_inj inr_inj;;

let sum_CASES = prove
 (`!x : A + B. (?a. x = INL a) \/ (?b. x = INR b)`,
  MATCH_MP_TAC sum_INDUCT THEN
  REPEAT STRIP_TAC THENL
  [DISJ1_TAC THEN
   EXISTS_TAC `a : A` THEN
   REFL_TAC;
   DISJ2_TAC THEN
   EXISTS_TAC `b : B` THEN
   REFL_TAC]);;

export_namedthm sum_CASES "sum_CASES";;

let case_sum_id = prove
 (`!(x : A + B). case_sum INL INR x = x`,
  GEN_TAC THEN
  MP_TAC (SPEC `x : A + B` sum_CASES) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_sum_def]);;

export_namedthm case_sum_id "case_sum_id";;

let ISL_case_sum = prove
 (`!(f : A -> C) (g : B -> C) x. ISL x ==> case_sum f g x = f (OUTL x)`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPEC `x : A + B` sum_CASES) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_sum_def; ISL_def; OUTL]);;

export_namedthm ISL_case_sum "ISL_case_sum";;

let ISR_case_sum = prove
 (`!(f : A -> C) (g : B -> C) x. ISR x ==> case_sum f g x = g (OUTR x)`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPEC `x : A + B` sum_CASES) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_sum_def; ISR_def; OUTR]);;

export_namedthm ISR_case_sum "ISR_case_sum";;
