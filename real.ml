
(* ========================================================================= *)
(* More basic properties of the reals.                                       *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

needs "realarith.ml";;

(* ------------------------------------------------------------------------- *)
(* Additional commutativity properties of the inclusion map.                 *)
(* ------------------------------------------------------------------------- *)

export_theory "real-of-num-commutativity";;

let REAL_OF_NUM_LT = prove 
 (`!m n. &m < &n <=> m < n`,
  REWRITE_TAC[real_lt; GSYM NOT_LE; REAL_OF_NUM_LE]);;

export_namedthm REAL_OF_NUM_LT "REAL_OF_NUM_LT";;

let REAL_OF_NUM_GE = prove 
 (`!m n. &m >= &n <=> m >= n`,
  REWRITE_TAC[GE; real_ge; REAL_OF_NUM_LE]);;

export_namedthm REAL_OF_NUM_GE "REAL_OF_NUM_GE";;

let REAL_OF_NUM_GT = prove 
 (`!m n. &m > &n <=> m > n`,
  REWRITE_TAC[GT; real_gt; REAL_OF_NUM_LT]);;

export_namedthm REAL_OF_NUM_GT "REAL_OF_NUM_GT";;

let REAL_OF_NUM_MAX = prove 
 (`!m n. max (&m) (&n) = &(MAX m n)`,
  REWRITE_TAC[REAL_OF_NUM_LE; MAX; real_max; GSYM COND_RAND]);;

export_namedthm REAL_OF_NUM_MAX "REAL_OF_NUM_MAX";;

let REAL_OF_NUM_MIN = prove 
 (`!m n. min (&m) (&n) = &(MIN m n)`,
  REWRITE_TAC[REAL_OF_NUM_LE; MIN; real_min; GSYM COND_RAND]);;

export_namedthm REAL_OF_NUM_MIN "REAL_OF_NUM_MIN";;

let REAL_OF_NUM_SUC = prove 
 (`!n. &n + &1 = &(SUC n)`,
  REWRITE_TAC[ADD1; REAL_OF_NUM_ADD]);;

export_namedthm REAL_OF_NUM_SUC "REAL_OF_NUM_SUC";;

let REAL_OF_NUM_SUB = prove 
 (`!m n. m <= n ==> (&n - &m = &(n - m))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ADD_SUB2] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[real_sub; GSYM REAL_ADD_ASSOC] THEN
  MESON_TAC[REAL_ADD_LINV; REAL_ADD_SYM; REAL_ADD_LID]);;

export_namedthm REAL_OF_NUM_SUB "REAL_OF_NUM_SUB";;

let REAL_OF_NUM_SUB_CASES = prove 
 (`!m n. &m - &n = if n <= m then &(m - n) else -- &(n - m)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_OF_NUM_SUB] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_NEG_SUB] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REAL_OF_NUM_SUB THEN ASM_MESON_TAC[LE_CASES]);;

export_namedthm REAL_OF_NUM_SUB_CASES "REAL_OF_NUM_SUB_CASES";;

(* ------------------------------------------------------------------------- *)
(* A few theorems we need to prove explicitly for later.                     *)
(* ------------------------------------------------------------------------- *)

export_theory "real-misc";;

let REAL_MUL_AC = prove 
 (`(m * n = n * m) /\
   ((m * n) * p = m * (n * p)) /\
   (m * (n * p) = n * (m * p))`,
  REWRITE_TAC[REAL_MUL_ASSOC; EQT_INTRO(SPEC_ALL REAL_MUL_SYM)] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM);;

export_namedthm REAL_MUL_AC "REAL_MUL_AC";;

let REAL_ADD_RDISTRIB = prove 
 (`!x y z. (x + y) * z = x * z + y * z`,
  MESON_TAC[REAL_MUL_SYM; REAL_ADD_LDISTRIB]);;

export_namedthm REAL_ADD_RDISTRIB "REAL_ADD_RDISTRIB";;

let REAL_LT_LADD_IMP = prove 
 (`!x y z. y < z ==> x + y < x + z`,
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[real_lt] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LADD_IMP) THEN
  DISCH_THEN(MP_TAC o SPEC `--x`) THEN
  REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_LID]);;

export_namedthm REAL_LT_LADD_IMP "REAL_LT_LADD_IMP";;

let REAL_LT_MUL = prove 
 (`!x y. &0 < x /\ &0 < y ==> &0 < x * y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ENTIRE] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]);;

export_namedthm REAL_LT_MUL "REAL_LT_MUL";;

(* ------------------------------------------------------------------------- *)
(* Tactic version of REAL_ARITH.                                             *)
(* ------------------------------------------------------------------------- *)

let REAL_ARITH_TAC = CONV_TAC REAL_ARITH;;

(* ------------------------------------------------------------------------- *)
(* Prove all the linear theorems we can blow away automatically.             *)
(* ------------------------------------------------------------------------- *)

export_theory "real-linear";;

let REAL_EQ_ADD_LCANCEL_0 = prove 
 (`!x y. (x + y = x) <=> (y = &0)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_EQ_ADD_LCANCEL_0 "REAL_EQ_ADD_LCANCEL_0";;

let REAL_EQ_ADD_RCANCEL_0 = prove 
 (`!x y. (x + y = y) <=> (x = &0)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_EQ_ADD_RCANCEL_0 "REAL_EQ_ADD_RCANCEL_0";;

let REAL_LNEG_UNIQ = prove 
 (`!x y. (x + y = &0) <=> (x = --y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LNEG_UNIQ "REAL_LNEG_UNIQ";;

let REAL_RNEG_UNIQ = prove 
 (`!x y. (x + y = &0) <=> (y = --x)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_RNEG_UNIQ "REAL_RNEG_UNIQ";;

let REAL_NEG_LMUL = prove 
 (`!x y. --(x * y) = (--x) * y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_NEG_LMUL "REAL_NEG_LMUL";;

let REAL_NEG_RMUL = prove 
 (`!x y. --(x * y) = x * (--y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_NEG_RMUL "REAL_NEG_RMUL";;

let REAL_NEG_MUL2 = prove 
 (`!x y. (--x) * (--y) = x * y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_NEG_MUL2 "REAL_NEG_MUL2";;

let REAL_LT_LADD = prove 
 (`!x y z. (x + y) < (x + z) <=> y < z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_LADD "REAL_LT_LADD";;

let REAL_LT_RADD = prove 
 (`!x y z. (x + z) < (y + z) <=> x < y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_RADD "REAL_LT_RADD";;

let REAL_LT_ANTISYM = prove 
 (`!x y. ~(x < y /\ y < x)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_ANTISYM "REAL_LT_ANTISYM";;

let REAL_LT_GT = prove 
 (`!x y. x < y ==> ~(y < x)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_GT "REAL_LT_GT";;

let REAL_NOT_EQ = prove 
 (`!x y. ~(x = y) <=> x < y \/ y < x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_NOT_EQ "REAL_NOT_EQ";;

let REAL_NOT_LE = prove 
 (`!x y. ~(x <= y) <=> y < x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_NOT_LE "REAL_NOT_LE";;

let REAL_LET_ANTISYM = prove 
 (`!x y. ~(x <= y /\ y < x)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LET_ANTISYM "REAL_LET_ANTISYM";;

let REAL_NEG_LT0 = prove 
 (`!x. (--x) < &0 <=> &0 < x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_NEG_LT0 "REAL_NEG_LT0";;

let REAL_NEG_GT0 = prove 
 (`!x. &0 < (--x) <=> x < &0`,
  REAL_ARITH_TAC);;

export_namedthm REAL_NEG_GT0 "REAL_NEG_GT0";;

export_theory "real-linear";;

let REAL_NEG_LE0 = prove 
 (`!x. (--x) <= &0 <=> &0 <= x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_NEG_LE0 "REAL_NEG_LE0";;

let REAL_NEG_GE0 = prove 
 (`!x. &0 <= (--x) <=> x <= &0`,
  REAL_ARITH_TAC);;

export_namedthm REAL_NEG_GE0 "REAL_NEG_GE0";;

let REAL_LT_TOTAL = prove 
 (`!x y. (x = y) \/ x < y \/ y < x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_TOTAL "REAL_LT_TOTAL";;

let REAL_LT_NEGTOTAL = prove 
 (`!x. (x = &0) \/ (&0 < x) \/ (&0 < --x)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_NEGTOTAL "REAL_LT_NEGTOTAL";;

let REAL_LE_01 = prove 
 (`&0 <= &1`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LE_01 "REAL_LE_01";;

let REAL_LT_01 = prove 
 (`&0 < &1`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_01 "REAL_LT_01";;

let REAL_LE_LADD = prove 
 (`!x y z. (x + y) <= (x + z) <=> y <= z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LE_LADD "REAL_LE_LADD";;

let REAL_LE_RADD = prove 
 (`!x y z. (x + z) <= (y + z) <=> x <= y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LE_RADD "REAL_LE_RADD";;

let REAL_LT_ADD2 = prove 
 (`!w x y z. w < x /\ y < z ==> (w + y) < (x + z)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_ADD2 "REAL_LT_ADD2";;

let REAL_LE_ADD2 = prove 
 (`!w x y z. w <= x /\ y <= z ==> (w + y) <= (x + z)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LE_ADD2 "REAL_LE_ADD2";;

let REAL_LT_LNEG = prove 
 (`!x y. --x < y <=> &0 < x + y`,
  REWRITE_TAC[real_lt; REAL_LE_RNEG; REAL_ADD_AC]);;

export_namedthm REAL_LT_LNEG "REAL_LT_LNEG";;

let REAL_LT_RNEG = prove 
 (`!x y. x < --y <=> x + y < &0`,
  REWRITE_TAC[real_lt; REAL_LE_LNEG; REAL_ADD_AC]);;

export_namedthm REAL_LT_RNEG "REAL_LT_RNEG";;

let REAL_LT_ADDNEG = prove 
 (`!x y z. y < (x + (--z)) <=> (y + z) < x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_ADDNEG "REAL_LT_ADDNEG";;

export_theory "real-linear";;

let REAL_LT_ADDNEG2 = prove 
 (`!x y z. (x + (--y)) < z <=> x < (z + y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_ADDNEG2 "REAL_LT_ADDNEG2";;

let REAL_LT_ADD1 = prove 
 (`!x y. x <= y ==> x < (y + &1)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_ADD1 "REAL_LT_ADD1";;

let REAL_SUB_ADD = prove 
 (`!x y. (x - y) + y = x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_ADD "REAL_SUB_ADD";;

let REAL_SUB_ADD2 = prove 
 (`!x y. y + (x - y) = x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_ADD2 "REAL_SUB_ADD2";;

let REAL_SUB_REFL = prove 
 (`!x. x - x = &0`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_REFL "REAL_SUB_REFL";;

let REAL_LE_DOUBLE = prove 
 (`!x. &0 <= x + x <=> &0 <= x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LE_DOUBLE "REAL_LE_DOUBLE";;

let REAL_LE_NEGL = prove 
 (`!x. (--x <= x) <=> (&0 <= x)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LE_NEGL "REAL_LE_NEGL";;

let REAL_LE_NEGR = prove 
 (`!x. (x <= --x) <=> (x <= &0)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LE_NEGR "REAL_LE_NEGR";;

let REAL_NEG_EQ_0 = prove 
 (`!x. (--x = &0) <=> (x = &0)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_NEG_EQ_0 "REAL_NEG_EQ_0";;

let REAL_ADD_SUB = prove 
 (`!x y. (x + y) - x = y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ADD_SUB "REAL_ADD_SUB";;

let REAL_NEG_EQ = prove 
 (`!x y. (--x = y) <=> (x = --y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_NEG_EQ "REAL_NEG_EQ";;

let REAL_NEG_MINUS1 = prove 
 (`!x. --x = (--(&1)) * x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_NEG_MINUS1 "REAL_NEG_MINUS1";;

let REAL_LT_IMP_NE = prove 
 (`!x y. x < y ==> ~(x = y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_IMP_NE "REAL_LT_IMP_NE";;

let REAL_LE_ADDR = prove 
 (`!x y. x <= x + y <=> &0 <= y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LE_ADDR "REAL_LE_ADDR";;

let REAL_LE_ADDL = prove 
 (`!x y. y <= x + y <=> &0 <= x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LE_ADDL "REAL_LE_ADDL";;

export_theory "real-linear";;

let REAL_LT_ADDR = prove 
 (`!x y. x < x + y <=> &0 < y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_ADDR "REAL_LT_ADDR";;

let REAL_LT_ADDL = prove 
 (`!x y. y < x + y <=> &0 < x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_ADDL "REAL_LT_ADDL";;

let REAL_SUB_SUB = prove 
 (`!x y. (x - y) - x = --y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_SUB "REAL_SUB_SUB";;

let REAL_LT_ADD_SUB = prove 
 (`!x y z. (x + y) < z <=> x < (z - y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_ADD_SUB "REAL_LT_ADD_SUB";;

let REAL_LT_SUB_RADD = prove 
 (`!x y z. (x - y) < z <=> x < z + y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_SUB_RADD "REAL_LT_SUB_RADD";;

let REAL_LT_SUB_LADD = prove 
 (`!x y z. x < (y - z) <=> (x + z) < y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_SUB_LADD "REAL_LT_SUB_LADD";;

let REAL_LE_SUB_LADD = prove 
 (`!x y z. x <= (y - z) <=> (x + z) <= y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LE_SUB_LADD "REAL_LE_SUB_LADD";;

let REAL_LE_SUB_RADD = prove 
 (`!x y z. (x - y) <= z <=> x <= z + y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LE_SUB_RADD "REAL_LE_SUB_RADD";;

let REAL_ADD2_SUB2 = prove 
 (`!a b c d. (a + b) - (c + d) = (a - c) + (b - d)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ADD2_SUB2 "REAL_ADD2_SUB2";;

let REAL_SUB_LZERO = prove 
 (`!x. &0 - x = --x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_LZERO "REAL_SUB_LZERO";;

let REAL_SUB_RZERO = prove 
 (`!x. x - &0 = x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_RZERO "REAL_SUB_RZERO";;

let REAL_LET_ADD2 = prove 
 (`!w x y z. w <= x /\ y < z ==> (w + y) < (x + z)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LET_ADD2 "REAL_LET_ADD2";;

let REAL_LTE_ADD2 = prove 
 (`!w x y z. w < x /\ y <= z ==> w + y < x + z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LTE_ADD2 "REAL_LTE_ADD2";;

let REAL_SUB_LNEG = prove 
 (`!x y. (--x) - y = --(x + y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_LNEG "REAL_SUB_LNEG";;

let REAL_SUB_RNEG = prove 
 (`!x y. x - (--y) = x + y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_RNEG "REAL_SUB_RNEG";;

let REAL_SUB_NEG2 = prove 
 (`!x y. (--x) - (--y) = y - x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_NEG2 "REAL_SUB_NEG2";;

let REAL_SUB_TRIANGLE = prove 
 (`!a b c. (a - b) + (b - c) = a - c`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_TRIANGLE "REAL_SUB_TRIANGLE";;

export_theory "real-linear";;

let REAL_EQ_SUB_LADD = prove 
 (`!x y z. (x = y - z) <=> (x + z = y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_EQ_SUB_LADD "REAL_EQ_SUB_LADD";;

let REAL_EQ_SUB_RADD = prove 
 (`!x y z. (x - y = z) <=> (x = z + y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_EQ_SUB_RADD "REAL_EQ_SUB_RADD";;

let REAL_SUB_SUB2 = prove 
 (`!x y. x - (x - y) = y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_SUB2 "REAL_SUB_SUB2";;

let REAL_ADD_SUB2 = prove 
 (`!x y. x - (x + y) = --y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ADD_SUB2 "REAL_ADD_SUB2";;

let REAL_EQ_IMP_LE = prove 
 (`!x y. (x = y) ==> x <= y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_EQ_IMP_LE "REAL_EQ_IMP_LE";;

let REAL_LT_IMP_NZ = prove 
 (`!x. &0 < x ==> ~(x = &0)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_IMP_NZ "REAL_LT_IMP_NZ";;

let REAL_DIFFSQ = prove 
 (`!x y. (x + y) * (x - y) = (x * x) - (y * y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_DIFFSQ "REAL_DIFFSQ";;

let REAL_EQ_NEG2 = prove 
 (`!x y. (--x = --y) <=> (x = y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_EQ_NEG2 "REAL_EQ_NEG2";;

let REAL_LT_NEG2 = prove 
 (`!x y. --x < --y <=> y < x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_NEG2 "REAL_LT_NEG2";;

let REAL_SUB_LDISTRIB = prove 
 (`!x y z. x * (y - z) = x * y - x * z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_LDISTRIB "REAL_SUB_LDISTRIB";;

let REAL_SUB_RDISTRIB = prove 
 (`!x y z. (x - y) * z = x * z - y * z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_RDISTRIB "REAL_SUB_RDISTRIB";;

(* ------------------------------------------------------------------------- *)
(* Theorems about "abs".                                                     *)
(* ------------------------------------------------------------------------- *)

export_theory "real-abs";;

let REAL_ABS_ZERO = prove 
 (`!x. (abs(x) = &0) <=> (x = &0)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_ZERO "REAL_ABS_ZERO";;

let REAL_ABS_0 = prove 
 (`abs(&0) = &0`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_0 "REAL_ABS_0";;

let REAL_ABS_1 = prove 
 (`abs(&1) = &1`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_1 "REAL_ABS_1";;

export_theory "real-abs-triangle";;

let REAL_ABS_TRIANGLE = prove 
 (`!x y. abs(x + y) <= abs(x) + abs(y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_TRIANGLE "REAL_ABS_TRIANGLE";;

let REAL_ABS_TRIANGLE_LE = prove 
 (`!x y z.abs(x) + abs(y - x) <= z ==> abs(y) <= z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_TRIANGLE_LE "REAL_ABS_TRIANGLE_LE";;

let REAL_ABS_TRIANGLE_LT = prove 
 (`!x y z.abs(x) + abs(y - x) < z ==> abs(y) < z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_TRIANGLE_LT "REAL_ABS_TRIANGLE_LT";;

export_theory "real-abs";;

let REAL_ABS_POS = prove 
 (`!x. &0 <= abs(x)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_POS "REAL_ABS_POS";;

let REAL_ABS_SUB = prove 
 (`!x y. abs(x - y) = abs(y - x)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_SUB "REAL_ABS_SUB";;

let REAL_ABS_NZ = prove 
 (`!x. ~(x = &0) <=> &0 < abs(x)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_NZ "REAL_ABS_NZ";;

let REAL_ABS_ABS = prove 
 (`!x. abs(abs(x)) = abs(x)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_ABS "REAL_ABS_ABS";;

let REAL_ABS_LE = prove 
 (`!x. x <= abs(x)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_LE "REAL_ABS_LE";;

let REAL_ABS_REFL = prove 
 (`!x. (abs(x) = x) <=> &0 <= x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_REFL "REAL_ABS_REFL";;

let REAL_ABS_BETWEEN = prove 
 (`!x y d. &0 < d /\ ((x - d) < y) /\ (y < (x + d)) <=> abs(y - x) < d`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_BETWEEN "REAL_ABS_BETWEEN";;

let REAL_ABS_BOUND = prove 
 (`!x y d. abs(x - y) < d ==> y < (x + d)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_BOUND "REAL_ABS_BOUND";;

let REAL_ABS_STILLNZ = prove 
 (`!x y. abs(x - y) < abs(y) ==> ~(x = &0)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_STILLNZ "REAL_ABS_STILLNZ";;

let REAL_ABS_CASES = prove 
 (`!x. (x = &0) \/ &0 < abs(x)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_CASES "REAL_ABS_CASES";;

let REAL_ABS_BETWEEN1 = prove 
 (`!x y z. x < z /\ (abs(y - x)) < (z - x) ==> y < z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_BETWEEN1 "REAL_ABS_BETWEEN1";;

let REAL_ABS_SIGN = prove 
 (`!x y. abs(x - y) < y ==> &0 < x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_SIGN "REAL_ABS_SIGN";;

let REAL_ABS_SIGN2 = prove 
 (`!x y. abs(x - y) < --y ==> x < &0`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_SIGN2 "REAL_ABS_SIGN2";;

let REAL_ABS_CIRCLE = prove 
 (`!x y h. abs(h) < (abs(y) - abs(x)) ==> abs(x + h) < abs(y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_CIRCLE "REAL_ABS_CIRCLE";;

let REAL_SUB_ABS = prove 
 (`!x y. (abs(x) - abs(y)) <= abs(x - y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_SUB_ABS "REAL_SUB_ABS";;

let REAL_ABS_SUB_ABS = prove 
 (`!x y. abs(abs(x) - abs(y)) <= abs(x - y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_SUB_ABS "REAL_ABS_SUB_ABS";;

let REAL_ABS_BETWEEN2 = prove 
 (`!x0 x y0 y. x0 < y0 /\ &2 * abs(x - x0) < (y0 - x0) /\
                          &2 * abs(y - y0) < (y0 - x0)
        ==> x < y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_BETWEEN2 "REAL_ABS_BETWEEN2";;

export_theory "real-abs-bounds";;

let REAL_ABS_BOUNDS = prove 
 (`!x k. abs(x) <= k <=> --k <= x /\ x <= k`,
  REAL_ARITH_TAC);;

export_namedthm REAL_ABS_BOUNDS "REAL_ABS_BOUNDS";;

let REAL_BOUNDS_LE = prove 
 (`!x k. --k <= x /\ x <= k <=> abs(x) <= k`,
  REAL_ARITH_TAC);;

export_namedthm REAL_BOUNDS_LE "REAL_BOUNDS_LE";;

let REAL_BOUNDS_LT = prove 
 (`!x k. --k < x /\ x < k <=> abs(x) < k`,
  REAL_ARITH_TAC);;

export_namedthm REAL_BOUNDS_LT "REAL_BOUNDS_LT";;

(* ------------------------------------------------------------------------- *)
(* Theorems about max and min.                                               *)
(* ------------------------------------------------------------------------- *)

export_theory "real-min-max";;

let REAL_MIN_MAX = prove 
 (`!x y. min x y = --(max (--x) (--y))`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MIN_MAX "REAL_MIN_MAX";;

let REAL_MAX_MIN = prove 
 (`!x y. max x y = --(min (--x) (--y))`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MAX_MIN "REAL_MAX_MIN";;

let REAL_MAX_MAX = prove 
 (`!x y. x <= max x y /\ y <= max x y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MAX_MAX "REAL_MAX_MAX";;

let REAL_MIN_MIN = prove 
 (`!x y. min x y <= x /\ min x y <= y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MIN_MIN "REAL_MIN_MIN";;

let REAL_MAX_SYM = prove 
 (`!x y. max x y = max y x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MAX_SYM "REAL_MAX_SYM";;

let REAL_MIN_SYM = prove 
 (`!x y. min x y = min y x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MIN_SYM "REAL_MIN_SYM";;

export_theory "real-min-max-order";;

let REAL_LE_MAX = prove 
 (`!x y z. z <= max x y <=> z <= x \/ z <= y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LE_MAX "REAL_LE_MAX";;

let REAL_LE_MIN = prove 
 (`!x y z. z <= min x y <=> z <= x /\ z <= y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LE_MIN "REAL_LE_MIN";;

let REAL_LT_MAX = prove 
 (`!x y z. z < max x y <=> z < x \/ z < y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_MAX "REAL_LT_MAX";;

let REAL_LT_MIN = prove 
 (`!x y z. z < min x y <=> z < x /\ z < y`,
  REAL_ARITH_TAC);;

export_namedthm REAL_LT_MIN "REAL_LT_MIN";;

let REAL_MAX_LE = prove 
 (`!x y z. max x y <= z <=> x <= z /\ y <= z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MAX_LE "REAL_MAX_LE";;

let REAL_MIN_LE = prove 
 (`!x y z. min x y <= z <=> x <= z \/ y <= z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MIN_LE "REAL_MIN_LE";;

let REAL_MAX_LT = prove 
 (`!x y z. max x y < z <=> x < z /\ y < z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MAX_LT "REAL_MAX_LT";;

let REAL_MIN_LT = prove 
 (`!x y z. min x y < z <=> x < z \/ y < z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MIN_LT "REAL_MIN_LT";;

export_theory "real-min-max-assoc";;

let REAL_MAX_ASSOC = prove 
 (`!x y z. max x (max y z) = max (max x y) z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MAX_ASSOC "REAL_MAX_ASSOC";;

let REAL_MIN_ASSOC = prove 
 (`!x y z. min x (min y z) = min (min x y) z`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MIN_ASSOC "REAL_MIN_ASSOC";;

export_theory "real-min-max-aci";;

let REAL_MAX_ACI = prove 
 (`(max x y = max y x) /\
   (max (max x y) z = max x (max y z)) /\
   (max x (max y z) = max y (max x z)) /\
   (max x x = x) /\
   (max x (max x y) = max x y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MAX_ACI "REAL_MAX_ACI";;

let REAL_MIN_ACI = prove 
 (`(min x y = min y x) /\
   (min (min x y) z = min x (min y z)) /\
   (min x (min y z) = min y (min x z)) /\
   (min x x = x) /\
   (min x (min x y) = min x y)`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MIN_ACI "REAL_MIN_ACI";;

(* ------------------------------------------------------------------------- *)
(* To simplify backchaining, just as in the natural number case.             *)
(* ------------------------------------------------------------------------- *)

let REAL_LE_IMP =
  let pth = PURE_ONCE_REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS in
  fun th -> GEN_ALL(MATCH_MP pth (SPEC_ALL th));;

let REAL_LET_IMP =
  let pth = PURE_ONCE_REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS in
  fun th -> GEN_ALL(MATCH_MP pth (SPEC_ALL th));;

(* ------------------------------------------------------------------------- *)
(* Now a bit of nonlinear stuff.                                             *)
(* ------------------------------------------------------------------------- *)

export_theory "real-nonlinear";;

let REAL_ABS_MUL = prove 
 (`!x y. abs(x * y) = abs(x) * abs(y)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC (SPEC `x:real` REAL_LE_NEGTOTAL) THENL
   [ALL_TAC;
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM REAL_ABS_NEG]] THEN
  (DISJ_CASES_TAC (SPEC `y:real` REAL_LE_NEGTOTAL) THENL
    [ALL_TAC;
     GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_ABS_NEG]]) THEN
  ASSUM_LIST(MP_TAC o MATCH_MP REAL_LE_MUL o end_itlist CONJ o rev) THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN DISCH_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ABS_NEG];
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ABS_NEG];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[real_abs; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]);;

export_namedthm REAL_ABS_MUL "REAL_ABS_MUL";;

export_theory "real-nonlinear-pow";;

let REAL_POW_LE = prove 
 (`!x n. &0 <= x ==> &0 <= x pow n`,
  REPEAT STRIP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[real_pow; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]);;

export_namedthm REAL_POW_LE "REAL_POW_LE";;

let REAL_POW_LT = prove 
 (`!x n. &0 < x ==> &0 < x pow n`,
  REPEAT STRIP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[real_pow; REAL_LT_01] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]);;

export_namedthm REAL_POW_LT "REAL_POW_LT";;

let REAL_ABS_POW = prove 
 (`!x n. abs(x pow n) = abs(x) pow n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[real_pow; REAL_ABS_NUM; REAL_ABS_MUL]);;

export_namedthm REAL_ABS_POW "REAL_ABS_POW";;

export_theory "real-nonlinear-order";;

let REAL_LE_LMUL = prove 
 (`!x y z. &0 <= x /\ y <= z ==> x * y <= x * z`,
  ONCE_REWRITE_TAC[REAL_ARITH `x <= y <=> &0 <= y - x`] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_SUB_RZERO; REAL_LE_MUL]);;

export_namedthm REAL_LE_LMUL "REAL_LE_LMUL";;

let REAL_LE_RMUL = prove 
 (`!x y z. x <= y /\ &0 <= z ==> x * z <= y * z`,
  MESON_TAC[REAL_MUL_SYM; REAL_LE_LMUL]);;

export_namedthm REAL_LE_RMUL "REAL_LE_RMUL";;

let REAL_LT_LMUL = prove 
 (`!x y z. &0 < x /\ y < z ==> x * y < x * z`,
  ONCE_REWRITE_TAC[REAL_ARITH `x < y <=> &0 < y - x`] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_SUB_RZERO; REAL_LT_MUL]);;

export_namedthm REAL_LT_LMUL "REAL_LT_LMUL";;

let REAL_LT_RMUL = prove 
 (`!x y z. x < y /\ &0 < z ==> x * z < y * z`,
  MESON_TAC[REAL_MUL_SYM; REAL_LT_LMUL]);;

export_namedthm REAL_LT_RMUL "REAL_LT_RMUL";;

export_theory "real-nonlinear-mul";;

let REAL_EQ_MUL_LCANCEL = prove 
 (`!x y z. (x * y = x * z) <=> (x = &0) \/ (y = z)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(x = y) <=> (x - y = &0)`] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ENTIRE; REAL_SUB_RZERO]);;

export_namedthm REAL_EQ_MUL_LCANCEL "REAL_EQ_MUL_LCANCEL";;

let REAL_EQ_MUL_RCANCEL = prove 
 (`!x y z. (x * z = y * z) <=> (x = y) \/ (z = &0)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN
  MESON_TAC[]);;

export_namedthm REAL_EQ_MUL_RCANCEL "REAL_EQ_MUL_RCANCEL";;

let REAL_MUL_LINV_UNIQ = prove 
 (`!x y. (x * y = &1) ==> (inv(y) = x)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `y = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP REAL_MUL_LINV) THEN
  ASM_REWRITE_TAC[REAL_EQ_MUL_RCANCEL] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

export_namedthm REAL_MUL_LINV_UNIQ "REAL_MUL_LINV_UNIQ";;

let REAL_MUL_RINV_UNIQ = prove 
 (`!x y. (x * y = &1) ==> (inv(x) = y)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_MUL_LINV_UNIQ);;

export_namedthm REAL_MUL_RINV_UNIQ "REAL_MUL_RINV_UNIQ";;

export_theory "real-nonlinear-inv";;

let REAL_INV_INV = prove 
 (`!x. inv(inv x) = x`,
  GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
  ASM_REWRITE_TAC[REAL_INV_0] THEN
  MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN
  ASM_REWRITE_TAC[]);;

export_namedthm REAL_INV_INV "REAL_INV_INV";;

let REAL_EQ_INV2 = prove 
 (`!x y. inv(x) = inv(y) <=> x = y`,
  MESON_TAC[REAL_INV_INV]);;

export_namedthm REAL_EQ_INV2 "REAL_EQ_INV2";;

let REAL_INV_EQ_0 = prove 
 (`!x. inv(x) = &0 <=> x = &0`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[REAL_INV_0] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INV_INV] THEN ASM_REWRITE_TAC[REAL_INV_0]);;

export_namedthm REAL_INV_EQ_0 "REAL_INV_EQ_0";;

let REAL_LT_INV = prove 
 (`!x. &0 < x ==> &0 < inv(x)`,
  GEN_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC `inv(x)` REAL_LT_NEGTOTAL) THEN
  ASM_REWRITE_TAC[] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_INV_EQ_0]) THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN SUBGOAL_THEN `&0 < --(inv x) * x` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_MUL_LNEG]]] THEN
  SUBGOAL_THEN `inv(x) * x = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN
    UNDISCH_TAC `&0 < x` THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LT_RNEG; REAL_ADD_LID; REAL_OF_NUM_LT; ARITH]]);;

export_namedthm REAL_LT_INV "REAL_LT_INV";;

let REAL_LT_INV_EQ = prove 
 (`!x. &0 < inv x <=> &0 < x`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[REAL_LT_INV] THEN
  GEN_REWRITE_TAC (funpow 2 RAND_CONV) [GSYM REAL_INV_INV] THEN
  REWRITE_TAC[REAL_LT_INV]);;

export_namedthm REAL_LT_INV_EQ "REAL_LT_INV_EQ";;

let REAL_INV_NEG = prove 
 (`!x. inv(--x) = --(inv x)`,
  GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
  ASM_REWRITE_TAC[REAL_NEG_0; REAL_INV_0] THEN
  MATCH_MP_TAC REAL_MUL_LINV_UNIQ THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]);;

export_namedthm REAL_INV_NEG "REAL_INV_NEG";;

let REAL_LE_INV_EQ = prove 
 (`!x. &0 <= inv x <=> &0 <= x`,
  REWRITE_TAC[REAL_LE_LT; REAL_LT_INV_EQ; REAL_INV_EQ_0] THEN
  MESON_TAC[REAL_INV_EQ_0]);;

export_namedthm REAL_LE_INV_EQ "REAL_LE_INV_EQ";;

let REAL_LE_INV = prove 
 (`!x. &0 <= x ==> &0 <= inv(x)`,
  REWRITE_TAC[REAL_LE_INV_EQ]);;

export_namedthm REAL_LE_INV "REAL_LE_INV";;

let REAL_MUL_RINV = prove 
 (`!x. ~(x = &0) ==> (x * inv(x) = &1)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_MUL_LINV]);;

export_namedthm REAL_MUL_RINV "REAL_MUL_RINV";;

let REAL_INV_1 = prove 
 (`inv(&1) = &1`,
  MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN
  REWRITE_TAC[REAL_MUL_LID]);;

export_namedthm REAL_INV_1 "REAL_INV_1";;

let REAL_INV_EQ_1 = prove 
 (`!x. inv(x) = &1 <=> x = &1`,
  MESON_TAC[REAL_INV_INV; REAL_INV_1]);;

export_namedthm REAL_INV_EQ_1 "REAL_INV_EQ_1";;

export_theory "real-nonlinear-div";;

let REAL_DIV_1 = prove 
 (`!x. x / &1 = x`,
  REWRITE_TAC[real_div; REAL_INV_1; REAL_MUL_RID]);;

export_namedthm REAL_DIV_1 "REAL_DIV_1";;

let REAL_DIV_REFL = prove 
 (`!x. ~(x = &0) ==> (x / x = &1)`,
  GEN_TAC THEN REWRITE_TAC[real_div; REAL_MUL_RINV]);;

export_namedthm REAL_DIV_REFL "REAL_DIV_REFL";;

let REAL_DIV_RMUL = prove 
 (`!x y. ~(y = &0) ==> ((x / y) * y = x)`,
  SIMP_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RID]);;

export_namedthm REAL_DIV_RMUL "REAL_DIV_RMUL";;

let REAL_DIV_LMUL = prove 
 (`!x y. ~(y = &0) ==> (y * (x / y) = x)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_DIV_RMUL]);;

export_namedthm REAL_DIV_LMUL "REAL_DIV_LMUL";;

let REAL_DIV_EQ_1 = prove 
 (`!x y:real. x / y = &1 <=> x = y /\ ~(x = &0) /\ ~(y = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  ASM_CASES_TAC `y = &0` THEN ASM_REWRITE_TAC[REAL_INV_0; REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH] THEN
  EQ_TAC THEN ASM_SIMP_TAC[GSYM real_div; REAL_DIV_REFL] THEN
  DISCH_THEN(MP_TAC o AP_TERM `( * ) (y:real)`) THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_MUL_RID]);;

export_namedthm REAL_DIV_EQ_1 "REAL_DIV_EQ_1";;

export_theory "real-nonlinear-abs";;

let REAL_ABS_INV = prove 
 (`!x. abs(inv x) = inv(abs x)`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[REAL_INV_0; REAL_ABS_0] THEN
  MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
  POP_ASSUM(SUBST1_TAC o MATCH_MP REAL_MUL_RINV) THEN
  REWRITE_TAC[REAL_ABS_1]);;

export_namedthm REAL_ABS_INV "REAL_ABS_INV";;

let REAL_ABS_DIV = prove 
 (`!x y. abs(x / y) = abs(x) / abs(y)`,
  REWRITE_TAC[real_div; REAL_ABS_INV; REAL_ABS_MUL]);;

export_namedthm REAL_ABS_DIV "REAL_ABS_DIV";;

export_theory "real-nonlinear";;

let REAL_INV_MUL = prove 
 (`!x y. inv(x * y) = inv(x) * inv(y)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`x = &0`; `y = &0`] THEN
  ASM_REWRITE_TAC[REAL_INV_0; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  MATCH_MP_TAC REAL_MUL_LINV_UNIQ THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b) * (c * d) = (a * c) * (b * d)`] THEN
  EVERY_ASSUM(SUBST1_TAC o MATCH_MP REAL_MUL_LINV) THEN
  REWRITE_TAC[REAL_MUL_LID]);;

export_namedthm REAL_INV_MUL "REAL_INV_MUL";;

let REAL_INV_DIV = prove 
 (`!x y. inv(x / y) = y / x`,
  REWRITE_TAC[real_div; REAL_INV_INV; REAL_INV_MUL] THEN
  MATCH_ACCEPT_TAC REAL_MUL_SYM);;

export_namedthm REAL_INV_DIV "REAL_INV_DIV";;

let REAL_POW_MUL = prove 
 (`!x y n. (x * y) pow n = (x pow n) * (y pow n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[real_pow; REAL_MUL_LID; REAL_MUL_AC]);;

export_namedthm REAL_POW_MUL "REAL_POW_MUL";;

let REAL_POW_INV = prove 
 (`!x n. (inv x) pow n = inv(x pow n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[real_pow; REAL_INV_1; REAL_INV_MUL]);;

export_namedthm REAL_POW_INV "REAL_POW_INV";;

let REAL_INV_POW = prove 
 (`!x n. inv(x pow n) = (inv x) pow n`,
  REWRITE_TAC[REAL_POW_INV]);;

export_namedthm REAL_INV_POW "REAL_INV_POW";;

let REAL_POW_DIV = prove 
 (`!x y n. (x / y) pow n = (x pow n) / (y pow n)`,
  REWRITE_TAC[real_div; REAL_POW_MUL; REAL_POW_INV]);;

export_namedthm REAL_POW_DIV "REAL_POW_DIV";;

let REAL_DIV_EQ_0 = prove 
 (`!x y. x / y = &0 <=> x = &0 \/ y = &0`,
  REWRITE_TAC[real_div; REAL_INV_EQ_0; REAL_ENTIRE]);;

export_namedthm REAL_DIV_EQ_0 "REAL_DIV_EQ_0";;

let REAL_POW_ADD = prove 
 (`!x m n. x pow (m + n) = x pow m * x pow n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; real_pow; REAL_MUL_LID; REAL_MUL_ASSOC]);;

export_namedthm REAL_POW_ADD "REAL_POW_ADD";;

let REAL_POW_NZ = prove 
 (`!x n. ~(x = &0) ==> ~(x pow n = &0)`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[real_pow; REAL_OF_NUM_EQ; ARITH] THEN
  ASM_MESON_TAC[REAL_ENTIRE]);;

export_namedthm REAL_POW_NZ "REAL_POW_NZ";;

let REAL_POW_SUB = prove 
 (`!x m n. ~(x = &0) /\ m <= n ==> (x pow (n - m) = x pow n / x pow m)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[ADD_SUB2] THEN REWRITE_TAC[REAL_POW_ADD] THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_LINV THEN
  MATCH_MP_TAC REAL_POW_NZ THEN ASM_REWRITE_TAC[]);;

export_namedthm REAL_POW_SUB "REAL_POW_SUB";;

export_theory "real-nonlinear-order";;

let REAL_LT_LCANCEL_IMP = prove 
 (`!x y z. &0 < x /\ x * y < x * z ==> y < z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN MP_TAC th) THEN DISCH_THEN
   (MP_TAC o uncurry CONJ o (MATCH_MP REAL_LT_INV F_F I) o CONJ_PAIR) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_LMUL) THEN
  POP_ASSUM(ASSUME_TAC o MATCH_MP REAL_MUL_LINV o MATCH_MP REAL_LT_IMP_NZ) THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID]);;

export_namedthm REAL_LT_LCANCEL_IMP "REAL_LT_LCANCEL_IMP";;

let REAL_LT_RCANCEL_IMP = prove 
 (`!x y z. &0 < z /\ x * z < y * z ==> x < y`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_LT_LCANCEL_IMP]);;

export_namedthm REAL_LT_RCANCEL_IMP "REAL_LT_RCANCEL_IMP";;

let REAL_LE_LCANCEL_IMP = prove 
 (`!x y z. &0 < x /\ x * y <= x * z ==> y <= z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT; REAL_EQ_MUL_LCANCEL] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
  EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[]);;

export_namedthm REAL_LE_LCANCEL_IMP "REAL_LE_LCANCEL_IMP";;

let REAL_LE_RCANCEL_IMP = prove 
 (`!x y z. &0 < z /\ x * z <= y * z ==> x <= y`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_LE_LCANCEL_IMP]);;

export_namedthm REAL_LE_RCANCEL_IMP "REAL_LE_RCANCEL_IMP";;

let REAL_LE_RMUL_EQ = prove 
 (`!x y z. &0 < z ==> (x * z <= y * z <=> x <= y)`,
  MESON_TAC[REAL_LE_RMUL; REAL_LE_RCANCEL_IMP; REAL_LT_IMP_LE]);;

export_namedthm REAL_LE_RMUL_EQ "REAL_LE_RMUL_EQ";;

let REAL_LE_LMUL_EQ = prove 
 (`!x y z. &0 < z ==> (z * x <= z * y <=> x <= y)`,
  MESON_TAC[REAL_LE_RMUL_EQ; REAL_MUL_SYM]);;

export_namedthm REAL_LE_LMUL_EQ "REAL_LE_LMUL_EQ";;

let REAL_LT_RMUL_EQ = prove 
 (`!x y z. &0 < z ==> (x * z < y * z <=> x < y)`,
  SIMP_TAC[GSYM REAL_NOT_LE; REAL_LE_RMUL_EQ]);;

export_namedthm REAL_LT_RMUL_EQ "REAL_LT_RMUL_EQ";;

let REAL_LT_LMUL_EQ = prove 
 (`!x y z. &0 < z ==> (z * x < z * y <=> x < y)`,
  SIMP_TAC[GSYM REAL_NOT_LE; REAL_LE_LMUL_EQ]);;

export_namedthm REAL_LT_LMUL_EQ "REAL_LT_LMUL_EQ";;

let REAL_LE_MUL_EQ = prove 
 (`(!x y. &0 < x ==> (&0 <= x * y <=> &0 <= y)) /\
   (!x y. &0 < y ==> (&0 <= x * y <=> &0 <= x))`,
  MESON_TAC[REAL_LE_LMUL_EQ; REAL_LE_RMUL_EQ; REAL_MUL_LZERO; REAL_MUL_RZERO]);;

export_namedthm REAL_LE_MUL_EQ "REAL_LE_MUL_EQ";;

let REAL_LT_MUL_EQ = prove 
 (`(!x y. &0 < x ==> (&0 < x * y <=> &0 < y)) /\
   (!x y. &0 < y ==> (&0 < x * y <=> &0 < x))`,
  MESON_TAC[REAL_LT_LMUL_EQ; REAL_LT_RMUL_EQ; REAL_MUL_LZERO; REAL_MUL_RZERO]);;

export_namedthm REAL_LT_MUL_EQ "REAL_LT_MUL_EQ";;

let REAL_MUL_POS_LT = prove 
 (`!x y. &0 < x * y <=> &0 < x /\ &0 < y \/ x < &0 /\ y < &0`,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC(SPEC `x:real` REAL_LT_NEGTOTAL) THEN
  STRIP_ASSUME_TAC(SPEC `y:real` REAL_LT_NEGTOTAL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL] THEN
  ASSUM_LIST(MP_TAC o MATCH_MP REAL_LT_MUL o end_itlist CONJ) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

export_namedthm REAL_MUL_POS_LT "REAL_MUL_POS_LT";;

let REAL_MUL_POS_LE = prove 
 (`!x y. &0 <= x * y <=>
         x = &0 \/ y = &0 \/ &0 < x /\ &0 < y \/ x < &0 /\ y < &0`,
  REWRITE_TAC[REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
  REWRITE_TAC[REAL_MUL_POS_LT; REAL_ENTIRE] THEN REAL_ARITH_TAC);;

export_namedthm REAL_MUL_POS_LE "REAL_MUL_POS_LE";;

let REAL_LE_RDIV_EQ = prove 
 (`!x y z. &0 < z ==> (x <= y / z <=> x * z <= y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP REAL_LE_RMUL_EQ th)]) THEN
  ASM_SIMP_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_MUL_LINV;
               REAL_MUL_RID; REAL_LT_IMP_NZ]);;

export_namedthm REAL_LE_RDIV_EQ "REAL_LE_RDIV_EQ";;

let REAL_LE_LDIV_EQ = prove 
 (`!x y z. &0 < z ==> (x / z <= y <=> x <= y * z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP REAL_LE_RMUL_EQ th)]) THEN
  ASM_SIMP_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_MUL_LINV;
               REAL_MUL_RID; REAL_LT_IMP_NZ]);;

export_namedthm REAL_LE_LDIV_EQ "REAL_LE_LDIV_EQ";;

let REAL_LT_RDIV_EQ = prove 
 (`!x y z. &0 < z ==> (x < y / z <=> x * z < y)`,
  SIMP_TAC[GSYM REAL_NOT_LE; REAL_LE_LDIV_EQ]);;

export_namedthm REAL_LT_RDIV_EQ "REAL_LT_RDIV_EQ";;

let REAL_LT_LDIV_EQ = prove 
 (`!x y z. &0 < z ==> (x / z < y <=> x < y * z)`,
  SIMP_TAC[GSYM REAL_NOT_LE; REAL_LE_RDIV_EQ]);;

export_namedthm REAL_LT_LDIV_EQ "REAL_LT_LDIV_EQ";;

export_theory "real-nonlinear";;

let REAL_EQ_RDIV_EQ = prove 
 (`!x y z. &0 < z ==> ((x = y / z) <=> (x * z = y))`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ]);;

export_namedthm REAL_EQ_RDIV_EQ "REAL_EQ_RDIV_EQ";;

let REAL_EQ_LDIV_EQ = prove 
 (`!x y z. &0 < z ==> ((x / z = y) <=> (x = y * z))`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ]);;

export_namedthm REAL_EQ_LDIV_EQ "REAL_EQ_LDIV_EQ";;

let REAL_LT_DIV2_EQ = prove 
 (`!x y z. &0 < z ==> (x / z < y / z <=> x < y)`,
  SIMP_TAC[real_div; REAL_LT_RMUL_EQ; REAL_LT_INV_EQ]);;

export_namedthm REAL_LT_DIV2_EQ "REAL_LT_DIV2_EQ";;

let REAL_LE_DIV2_EQ = prove 
 (`!x y z. &0 < z ==> (x / z <= y / z <=> x <= y)`,
  SIMP_TAC[real_div; REAL_LE_RMUL_EQ; REAL_LT_INV_EQ]);;

export_namedthm REAL_LE_DIV2_EQ "REAL_LE_DIV2_EQ";;

let REAL_MUL_2 = prove 
 (`!x. &2 * x = x + x`,
  REAL_ARITH_TAC);;

export_namedthm REAL_MUL_2 "REAL_MUL_2";;

let REAL_POW_EQ_0 = prove 
 (`!x n. (x pow n = &0) <=> (x = &0) /\ ~(n = 0)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NOT_SUC; real_pow; REAL_ENTIRE] THENL
   [REAL_ARITH_TAC;
    CONV_TAC TAUT]);;

export_namedthm REAL_POW_EQ_0 "REAL_POW_EQ_0";;

export_theory "real-nonlinear-order";;

let REAL_LE_MUL2 = prove 
 (`!w x y z. &0 <= w /\ w <= x /\ &0 <= y /\ y <= z
             ==> w * y <= x * z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `w * z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL; MATCH_MP_TAC REAL_LE_RMUL] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `y:real` THEN
  ASM_REWRITE_TAC[]);;

export_namedthm REAL_LE_MUL2 "REAL_LE_MUL2";;

let REAL_LT_MUL2 = prove 
 (`!w x y z. &0 <= w /\ w < x /\ &0 <= y /\ y < z
             ==> w * y < x * z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `w * z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL; MATCH_MP_TAC REAL_LT_RMUL] THEN
  ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `y:real` THEN
    ASM_REWRITE_TAC[]]);;

export_namedthm REAL_LT_MUL2 "REAL_LT_MUL2";;

let REAL_LT_SQUARE = prove 
 (`!x. (&0 < x * x) <=> ~(x = &0)`,
  GEN_TAC THEN REWRITE_TAC[REAL_LT_LE; REAL_LE_SQUARE] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [EQ_SYM_EQ] THEN
  REWRITE_TAC[REAL_ENTIRE]);;

export_namedthm REAL_LT_SQUARE "REAL_LT_SQUARE";;

let REAL_POW_1 = prove 
 (`!x. x pow 1 = x`,
  REWRITE_TAC[num_CONV `1`] THEN
  REWRITE_TAC[real_pow; REAL_MUL_RID]);;

export_namedthm REAL_POW_1 "REAL_POW_1";;

let REAL_POW_ONE = prove 
 (`!n. &1 pow n = &1`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[real_pow; REAL_MUL_LID]);;

export_namedthm REAL_POW_ONE "REAL_POW_ONE";;

let REAL_LT_INV2 = prove 
 (`!x y. &0 < x /\ x < y ==> inv(y) < inv(x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN
  EXISTS_TAC `x * y` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `(inv x * x = &1) /\ (inv y * y = &1)` ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
      ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_RID]]]);;

export_namedthm REAL_LT_INV2 "REAL_LT_INV2";;

let REAL_LE_INV2 = prove 
 (`!x y. &0 < x /\ x <= y ==> inv(y) <= inv(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  ASM_CASES_TAC `x:real = y` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_INV2 THEN
  ASM_REWRITE_TAC[]);;

export_namedthm REAL_LE_INV2 "REAL_LE_INV2";;

let REAL_LT_LINV = prove 
 (`!x y. &0 < y /\ inv y < x ==> inv x < y`,
  REPEAT STRIP_TAC THEN MP_TAC (SPEC `y:real` REAL_LT_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (SPECL [`(inv y:real)`; `x:real`] REAL_LT_INV2) THEN
  ASM_REWRITE_TAC[REAL_INV_INV]);;

export_namedthm REAL_LT_LINV "REAL_LT_LINV";;

let REAL_LT_RINV = prove 
 (`!x y. &0 < x /\ x < inv y ==> y < inv x`,
  REPEAT STRIP_TAC THEN MP_TAC (SPEC `x:real` REAL_LT_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (SPECL [`x:real`; `inv y:real`] REAL_LT_INV2) THEN
  ASM_REWRITE_TAC[REAL_INV_INV]);;

export_namedthm REAL_LT_RINV "REAL_LT_RINV";;

let REAL_LE_LINV = prove 
 (`!x y. &0 < y /\ inv y <= x ==> inv x <= y`,
  REPEAT STRIP_TAC THEN MP_TAC (SPEC `y:real` REAL_LT_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (SPECL [`(inv y:real)`; `x:real`] REAL_LE_INV2) THEN
  ASM_REWRITE_TAC[REAL_INV_INV]);;

export_namedthm REAL_LE_LINV "REAL_LE_LINV";;

let REAL_LE_RINV = prove 
 (`!x y. &0 < x /\ x <= inv y ==> y <= inv x`,
  REPEAT STRIP_TAC THEN MP_TAC (SPEC `x:real` REAL_LT_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (SPECL [`x:real`; `inv y:real`] REAL_LE_INV2) THEN
  ASM_REWRITE_TAC[REAL_INV_INV]);;

export_namedthm REAL_LE_RINV "REAL_LE_RINV";;

let REAL_INV_LE_1 = prove 
 (`!x. &1 <= x ==> inv(x) <= &1`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_INV_1] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_LT_01]);;

export_namedthm REAL_INV_LE_1 "REAL_INV_LE_1";;

let REAL_INV_1_LE = prove 
 (`!x. &0 < x /\ x <= &1 ==> &1 <= inv(x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_INV_1] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_LT_01]);;

export_namedthm REAL_INV_1_LE "REAL_INV_1_LE";;

let REAL_INV_LT_1 = prove 
 (`!x. &1 < x ==> inv(x) < &1`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_INV_1] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_LT_01]);;

export_namedthm REAL_INV_LT_1 "REAL_INV_LT_1";;

let REAL_INV_1_LT = prove 
 (`!x. &0 < x /\ x < &1 ==> &1 < inv(x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_INV_1] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_LT_01]);;

export_namedthm REAL_INV_1_LT "REAL_INV_1_LT";;

export_theory "real-nonlinear";;

let REAL_SUB_INV = prove 
 (`!x y. ~(x = &0) /\ ~(y = &0) ==> (inv(x) - inv(y) = (y - x) / (x * y))`,
  REWRITE_TAC[real_div; REAL_SUB_RDISTRIB; REAL_INV_MUL] THEN
  SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[REAL_DIV_LMUL]);;

export_namedthm REAL_SUB_INV "REAL_SUB_INV";;

let REAL_DOWN = prove 
 (`!d. &0 < d ==> ?e. &0 < e /\ e < d`,
  GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `d / &2` THEN
  ASSUME_TAC(REAL_ARITH `&0 < &2`) THEN
  ASSUME_TAC(MATCH_MP REAL_MUL_LINV (REAL_ARITH `~(&2 = &0)`)) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `&2` THEN
  ASM_REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_MUL_RID] THEN
  UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC);;

export_namedthm REAL_DOWN "REAL_DOWN";;

let REAL_DOWN2 = prove 
 (`!d1 d2. &0 < d1 /\ &0 < d2 ==> ?e. &0 < e /\ e < d1 /\ e < d2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(SPECL [`d1:real`; `d2:real`] REAL_LE_TOTAL) THENL
   [MP_TAC(SPEC `d1:real` REAL_DOWN);
    MP_TAC(SPEC `d2:real` REAL_DOWN)] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REAL_ARITH_TAC);;

export_namedthm REAL_DOWN2 "REAL_DOWN2";;

export_theory "real-nonlinear-pow";;

let REAL_POW_LE2 = prove 
 (`!n x y. &0 <= x /\ x <= y ==> x pow n <= y pow n`,
  INDUCT_TAC THEN REWRITE_TAC[real_pow; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

export_namedthm REAL_POW_LE2 "REAL_POW_LE2";;

let REAL_POW_LE_1 = prove 
 (`!n x. &1 <= x ==> &1 <= x pow n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `&1`; `x:real`] REAL_POW_LE2) THEN
  ASM_REWRITE_TAC[REAL_POW_ONE; REAL_POS]);;

export_namedthm REAL_POW_LE_1 "REAL_POW_LE_1";;

let REAL_POW_1_LE = prove 
 (`!n x. &0 <= x /\ x <= &1 ==> x pow n <= &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `x:real`; `&1`] REAL_POW_LE2) THEN
  ASM_REWRITE_TAC[REAL_POW_ONE]);;

export_namedthm REAL_POW_1_LE "REAL_POW_1_LE";;

let REAL_POW_MONO = prove 
 (`!m n x. &1 <= x /\ m <= n ==> x pow m <= x pow n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[REAL_POW_ADD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]]);;

export_namedthm REAL_POW_MONO "REAL_POW_MONO";;

let REAL_POW_LT2 = prove 
 (`!n x y. ~(n = 0) /\ &0 <= x /\ x < y ==> x pow n < y pow n`,
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; real_pow] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[real_pow; REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

export_namedthm REAL_POW_LT2 "REAL_POW_LT2";;

let REAL_POW_LT_1 = prove 
 (`!n x. ~(n = 0) /\ &1 < x ==> &1 < x pow n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `&1`; `x:real`] REAL_POW_LT2) THEN
  ASM_REWRITE_TAC[REAL_POW_ONE; REAL_POS]);;

export_namedthm REAL_POW_LT_1 "REAL_POW_LT_1";;

let REAL_POW_1_LT = prove 
 (`!n x. ~(n = 0) /\ &0 <= x /\ x < &1 ==> x pow n < &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `x:real`; `&1`] REAL_POW_LT2) THEN
  ASM_REWRITE_TAC[REAL_POW_ONE]);;

export_namedthm REAL_POW_1_LT "REAL_POW_1_LT";;

let REAL_POW_MONO_LT = prove 
 (`!m n x. &1 < x /\ m < n ==> x pow m < x pow n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LT_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[REAL_POW_ADD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; ARITH];
    SPEC_TAC(`d:num`,`d:num`) THEN
    INDUCT_TAC THEN ONCE_REWRITE_TAC[real_pow] THENL
     [ASM_REWRITE_TAC[real_pow; REAL_MUL_RID]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE; ARITH]]);;

export_namedthm REAL_POW_MONO_LT "REAL_POW_MONO_LT";;

let REAL_POW_POW = prove 
 (`!x m n. (x pow m) pow n = x pow (m * n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[real_pow; MULT_CLAUSES; REAL_POW_ADD]);;

export_namedthm REAL_POW_POW "REAL_POW_POW";;

let REAL_EQ_RCANCEL_IMP = prove 
 (`!x y z. ~(z = &0) /\ (x * z = y * z) ==> (x = y)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  REWRITE_TAC[REAL_SUB_RZERO; GSYM REAL_SUB_RDISTRIB; REAL_ENTIRE] THEN
  CONV_TAC TAUT);;

export_namedthm REAL_EQ_RCANCEL_IMP "REAL_EQ_RCANCEL_IMP";;

let REAL_EQ_LCANCEL_IMP = prove 
 (`!x y z. ~(z = &0) /\ (z * x = z * y) ==> (x = y)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_EQ_RCANCEL_IMP);;

export_namedthm REAL_EQ_LCANCEL_IMP "REAL_EQ_LCANCEL_IMP";;

let REAL_LT_DIV = prove 
 (`!x y. &0 < x /\ &0 < y ==> &0 < x / y`,
  SIMP_TAC[REAL_LT_MUL; REAL_LT_INV_EQ; real_div]);;

export_namedthm REAL_LT_DIV "REAL_LT_DIV";;

let REAL_LE_DIV = prove 
 (`!x y. &0 <= x /\ &0 <= y ==> &0 <= x / y`,
  SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; real_div]);;

export_namedthm REAL_LE_DIV "REAL_LE_DIV";;

let REAL_DIV_POW2 = prove 
 (`!x m n. ~(x = &0)
           ==> (x pow m / x pow n = if n <= m then x pow (m - n)
                                    else inv(x pow (n - m)))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_POW_SUB] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_INV_DIV] THEN
  UNDISCH_TAC `~(n:num <= m)` THEN REWRITE_TAC[NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LT_IMP_LE) THEN
  ASM_SIMP_TAC[REAL_POW_SUB]);;

export_namedthm REAL_DIV_POW2 "REAL_DIV_POW2";;

let REAL_DIV_POW2_ALT = prove 
 (`!x m n. ~(x = &0)
           ==> (x pow m / x pow n = if n < m then x pow (m - n)
                                    else inv(x pow (n - m)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
  ONCE_REWRITE_TAC[REAL_INV_DIV] THEN
  ASM_SIMP_TAC[GSYM NOT_LE; REAL_DIV_POW2] THEN
  ASM_CASES_TAC `m <= n:num` THEN
  ASM_REWRITE_TAC[REAL_INV_INV]);;

export_namedthm REAL_DIV_POW2_ALT "REAL_DIV_POW2_ALT";;

let REAL_LT_POW2 = prove 
 (`!n. &0 < &2 pow n`,
  SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH]);;

export_namedthm REAL_LT_POW2 "REAL_LT_POW2";;

let REAL_LE_POW2 = prove 
 (`!n. &1 <= &2 pow n`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow 0` THEN
  SIMP_TAC[REAL_POW_MONO; LE_0; REAL_OF_NUM_LE; ARITH] THEN
  REWRITE_TAC[real_pow; REAL_LE_REFL]);;

export_namedthm REAL_LE_POW2 "REAL_LE_POW2";;

let REAL_POW2_ABS = prove 
 (`!x. abs(x) pow 2 = x pow 2`,
  GEN_TAC THEN REWRITE_TAC[real_abs] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_POW_NEG; ARITH_EVEN]);;

export_namedthm REAL_POW2_ABS "REAL_POW2_ABS";;

export_theory "real-nonlinear-square";;

let REAL_LE_SQUARE_ABS = prove 
 (`!x y. abs(x) <= abs(y) <=> x pow 2 <= y pow 2`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MESON_TAC[REAL_POW_LE2; REAL_ABS_POS; NUM_EQ_CONV `2 = 0`;
            REAL_POW_LT2; REAL_NOT_LE]);;

export_namedthm REAL_LE_SQUARE_ABS "REAL_LE_SQUARE_ABS";;

let REAL_LT_SQUARE_ABS = prove 
 (`!x y. abs(x) < abs(y) <=> x pow 2 < y pow 2`,
  REWRITE_TAC[GSYM REAL_NOT_LE; REAL_LE_SQUARE_ABS]);;

export_namedthm REAL_LT_SQUARE_ABS "REAL_LT_SQUARE_ABS";;

let REAL_EQ_SQUARE_ABS = prove 
 (`!x y. abs x = abs y <=> x pow 2 = y pow 2`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; REAL_LE_SQUARE_ABS]);;

export_namedthm REAL_EQ_SQUARE_ABS "REAL_EQ_SQUARE_ABS";;

export_theory "real-nonlinear-pow";;

let REAL_LE_POW_2 = prove 
 (`!x. &0 <= x pow 2`,
  REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]);;

export_namedthm REAL_LE_POW_2 "REAL_LE_POW_2";;

let REAL_LT_POW_2 = prove 
 (`!x. &0 < x pow 2 <=> ~(x = &0)`,
  REWRITE_TAC[REAL_LE_POW_2; REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
  REWRITE_TAC[REAL_POW_EQ_0; ARITH]);;

export_namedthm REAL_LT_POW_2 "REAL_LT_POW_2";;

let REAL_SOS_EQ_0 = prove 
 (`!x y. x pow 2 + y pow 2 = &0 <=> x = &0 /\ y = &0`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_ADD_LID] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `x + y = &0 ==> &0 <= x /\ &0 <= y ==> x = &0 /\ y = &0`)) THEN
  REWRITE_TAC[REAL_LE_SQUARE; REAL_ENTIRE]);;

export_namedthm REAL_SOS_EQ_0 "REAL_SOS_EQ_0";;

let REAL_POW_ZERO = prove 
 (`!n. &0 pow n = if n = 0 then &1 else &0`,
  INDUCT_TAC THEN REWRITE_TAC[real_pow; NOT_SUC; REAL_MUL_LZERO]);;

export_namedthm REAL_POW_ZERO "REAL_POW_ZERO";;

let REAL_POW_MONO_INV = prove 
 (`!m n x. &0 <= x /\ x <= &1 /\ n <= m ==> x pow m <= x pow n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[REAL_POW_ZERO] THEN
    REPEAT(COND_CASES_TAC THEN REWRITE_TAC[REAL_POS; REAL_LE_REFL]) THEN
    UNDISCH_TAC `n:num <= m` THEN ASM_REWRITE_TAC[LE];
    GEN_REWRITE_TAC BINOP_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[GSYM REAL_POW_INV] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_LT_INV_EQ];
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_INV_1_LE] THEN
    ASM_REWRITE_TAC[REAL_LT_LE]]);;

export_namedthm REAL_POW_MONO_INV "REAL_POW_MONO_INV";;

let REAL_POW_LE2_REV = prove 
 (`!n x y. ~(n = 0) /\ &0 <= y /\ x pow n <= y pow n ==> x <= y`,
  MESON_TAC[REAL_POW_LT2; REAL_NOT_LE]);;

export_namedthm REAL_POW_LE2_REV "REAL_POW_LE2_REV";;

let REAL_POW_LT2_REV = prove 
 (`!n x y. &0 <= y /\ x pow n < y pow n ==> x < y`,
  MESON_TAC[REAL_POW_LE2; REAL_NOT_LE]);;

export_namedthm REAL_POW_LT2_REV "REAL_POW_LT2_REV";;

let REAL_POW_EQ = prove 
 (`!n x y. ~(n = 0) /\ &0 <= x /\ &0 <= y /\ x pow n = y pow n ==> x = y`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN MESON_TAC[REAL_POW_LE2_REV]);;

export_namedthm REAL_POW_EQ "REAL_POW_EQ";;

let REAL_POW_EQ_ABS = prove 
 (`!n x y. ~(n = 0) /\ x pow n = y pow n ==> abs x = abs y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; GSYM REAL_ABS_POW]);;

export_namedthm REAL_POW_EQ_ABS "REAL_POW_EQ_ABS";;

let REAL_POW_EQ_1_IMP = prove 
 (`!x n. ~(n = 0) /\ x pow n = &1 ==> abs(x) = &1`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_POW_EQ_ABS THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[REAL_POW_ONE]);;

export_namedthm REAL_POW_EQ_1_IMP "REAL_POW_EQ_1_IMP";;

let REAL_POW_EQ_1 = prove 
 (`!x n. x pow n = &1 <=> abs(x) = &1 /\ (x < &0 ==> EVEN(n)) \/ n = 0`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[real_pow] THEN
  ASM_CASES_TAC `abs(x) = &1` THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_POW_EQ_1_IMP]] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (REAL_ARITH
   `abs x = a ==> x = a \/ x = --a`)) THEN
  ASM_REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

export_namedthm REAL_POW_EQ_1 "REAL_POW_EQ_1";;

let REAL_POW_LT2_ODD = prove 
 (`!n x y. x < y /\ ODD n ==> x pow n < y pow n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
  DISJ_CASES_TAC(SPEC `y:real` REAL_LE_NEGTOTAL) THENL
   [DISJ_CASES_TAC(REAL_ARITH `&0 <= x \/ &0 < --x`) THEN
    ASM_SIMP_TAC[REAL_POW_LT2] THEN
    SUBGOAL_THEN `&0 < --x pow n /\ &0 <= y pow n` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE; REAL_POW_LT];
      ASM_REWRITE_TAC[REAL_POW_NEG; GSYM NOT_ODD] THEN REAL_ARITH_TAC];
    SUBGOAL_THEN `--y pow n < --x pow n` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_POW_NEG; GSYM NOT_ODD]] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC]);;

export_namedthm REAL_POW_LT2_ODD "REAL_POW_LT2_ODD";;

let REAL_POW_LE2_ODD = prove 
 (`!n x y. x <= y /\ ODD n ==> x pow n <= y pow n`,
  REWRITE_TAC[REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_POW_LT2_ODD]);;

export_namedthm REAL_POW_LE2_ODD "REAL_POW_LE2_ODD";;

let REAL_POW_LT2_ODD_EQ = prove 
 (`!n x y. ODD n ==> (x pow n < y pow n <=> x < y)`,
  MESON_TAC[REAL_POW_LT2_ODD; REAL_POW_LE2_ODD; REAL_NOT_LE]);;

export_namedthm REAL_POW_LT2_ODD_EQ "REAL_POW_LT2_ODD_EQ";;

let REAL_POW_LE2_ODD_EQ = prove 
 (`!n x y. ODD n ==> (x pow n <= y pow n <=> x <= y)`,
  MESON_TAC[REAL_POW_LT2_ODD; REAL_POW_LE2_ODD; REAL_NOT_LE]);;

export_namedthm REAL_POW_LE2_ODD_EQ "REAL_POW_LE2_ODD_EQ";;

let REAL_POW_EQ_ODD_EQ = prove 
 (`!n x y. ODD n ==> (x pow n = y pow n <=> x = y)`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; REAL_POW_LE2_ODD_EQ]);;

export_namedthm REAL_POW_EQ_ODD_EQ "REAL_POW_EQ_ODD_EQ";;

let REAL_POW_EQ_ODD = prove 
 (`!n x y. ODD n /\ x pow n = y pow n ==> x = y`,
  MESON_TAC[REAL_POW_EQ_ODD_EQ]);;

export_namedthm REAL_POW_EQ_ODD "REAL_POW_EQ_ODD";;

let REAL_POW_EQ_EQ = prove 
 (`!n x y. x pow n = y pow n <=>
           if EVEN n then n = 0 \/ abs x = abs y else x = y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[real_pow; ARITH] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[REAL_POW_EQ_ODD_EQ; GSYM NOT_EVEN] THEN
  EQ_TAC THENL [ASM_MESON_TAC[REAL_POW_EQ_ABS]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EQ_SQUARE_ABS] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
    REWRITE_RULE[EVEN_EXISTS]) THEN ASM_REWRITE_TAC[GSYM REAL_POW_POW]);;

export_namedthm REAL_POW_EQ_EQ "REAL_POW_EQ_EQ";;

(* ------------------------------------------------------------------------- *)
(* Bounds on convex combinations.                                            *)
(* ------------------------------------------------------------------------- *)

export_theory "real-convex-bounds";;

let REAL_CONVEX_BOUND2_LT = prove 
 (`!x y a u v. x < a /\ y < b /\ &0 <= u /\ &0 <= v /\ u + v = &1
               ==> u * x + v * y < u * a + v * b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `u = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN REPEAT STRIP_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_ADD2 THEN
    ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE]] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

export_namedthm REAL_CONVEX_BOUND2_LT "REAL_CONVEX_BOUND2_LT";;

let REAL_CONVEX_BOUND2_LE = prove 
 (`!x y a u v. x <= a /\ y <= b /\ &0 <= u /\ &0 <= v /\ u + v = &1
               ==> u * x + v * y <= u * a + v * b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

export_namedthm REAL_CONVEX_BOUND2_LE "REAL_CONVEX_BOUND2_LE";;

let REAL_CONVEX_BOUND_LT = prove 
 (`!x y a u v. x < a /\ y < a /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
               ==> u * x + v * y < a`,
  MESON_TAC[REAL_CONVEX_BOUND2_LT; MESON[REAL_MUL_LID; REAL_ADD_RDISTRIB]
   `u + v = &1 ==> u * a + v * a = a`]);;

export_namedthm REAL_CONVEX_BOUND_LT "REAL_CONVEX_BOUND_LT";;

let REAL_CONVEX_BOUND_LE = prove 
 (`!x y a u v. x <= a /\ y <= a /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
               ==> u * x + v * y <= a`,
  MESON_TAC[REAL_CONVEX_BOUND2_LE; MESON[REAL_MUL_LID; REAL_ADD_RDISTRIB]
   `u + v = &1 ==> u * a + v * a = a`]);;

export_namedthm REAL_CONVEX_BOUND_LE "REAL_CONVEX_BOUND_LE";;

let REAL_CONVEX_BOUND_GT = prove 
 (`!x y a u v.
        a < x /\ a < y /\ &0 <= u /\ &0 <= v /\ u + v = &1
        ==> a < u * x + v * y`,
  MESON_TAC[REAL_CONVEX_BOUND2_LT; MESON[REAL_MUL_LID; REAL_ADD_RDISTRIB]
   `u + v = &1 ==> u * a + v * a = a`]);;

export_namedthm REAL_CONVEX_BOUND_GT "REAL_CONVEX_BOUND_GT";;

let REAL_CONVEX_BOUND_GE = prove 
 (`!x y a u v.
        a <= x /\ a <= y /\ &0 <= u /\ &0 <= v /\ u + v = &1
        ==> a <= u * x + v * y`,
  MESON_TAC[REAL_CONVEX_BOUND2_LE; MESON[REAL_MUL_LID; REAL_ADD_RDISTRIB]
   `u + v = &1 ==> u * a + v * a = a`]);;

export_namedthm REAL_CONVEX_BOUND_GE "REAL_CONVEX_BOUND_GE";;

let REAL_CONVEX_BOUNDS_LE = prove 
 (`!x y a b u v.
        a <= x /\ x <= b /\ a <= y /\ y <= b /\
        &0 <= u /\ &0 <= v /\ u + v = &1
        ==> a <= u * x + v * y /\ u * x + v * y <= b`,
  MESON_TAC[REAL_CONVEX_BOUND2_LE; MESON[REAL_MUL_LID; REAL_ADD_RDISTRIB]
   `u + v = &1 ==> u * a + v * a = a`]);;

export_namedthm REAL_CONVEX_BOUNDS_LE "REAL_CONVEX_BOUNDS_LE";;

let REAL_CONVEX_BOUNDS_LT = prove 
 (`!x y a b u v.
        a < x /\ x < b /\ a < y /\ y < b /\
        &0 <= u /\ &0 <= v /\ u + v = &1
        ==> a < u * x + v * y /\ u * x + v * y < b`,
  MESON_TAC[REAL_CONVEX_BOUND2_LT; MESON[REAL_MUL_LID; REAL_ADD_RDISTRIB]
   `u + v = &1 ==> u * a + v * a = a`]);;

export_namedthm REAL_CONVEX_BOUNDS_LT "REAL_CONVEX_BOUNDS_LT";;

(* ------------------------------------------------------------------------- *)
(* Some basic forms of the Archimedian property.                             *)
(* ------------------------------------------------------------------------- *)

export_theory "real-archimedian";;

let REAL_ARCH_SIMPLE = prove 
 (`!x. ?n. x <= &n`,
  let lemma = prove(`(!x. (?n. x = &n) ==> P x) <=> !n. P(&n)`,MESON_TAC[]) in
  MP_TAC(SPEC `\y. ?n. y = &n` REAL_COMPLETE) THEN REWRITE_TAC[lemma] THEN
  MESON_TAC[REAL_LE_SUB_LADD; REAL_OF_NUM_ADD; REAL_LE_TOTAL;
            REAL_ARITH `~(M <= M - &1)`]);;

export_namedthm REAL_ARCH_SIMPLE "REAL_ARCH_SIMPLE";;

let REAL_ARCH_LT = prove 
 (`!x. ?n. x < &n`,
  MESON_TAC[REAL_ARCH_SIMPLE; REAL_OF_NUM_ADD;
            REAL_ARITH `x <= n ==> x < n + &1`]);;

export_namedthm REAL_ARCH_LT "REAL_ARCH_LT";;

let REAL_ARCH = prove 
 (`!x. &0 < x ==> !y. ?n. y < &n * x`,
  MESON_TAC[REAL_ARCH_LT; REAL_LT_LDIV_EQ]);;

export_namedthm REAL_ARCH "REAL_ARCH";;

let REAL_ARCH_INV = prove 
 (`!e. &0 < e <=> ?n. ~(n = 0) /\ &0 < inv(&n) /\ inv(&n) < e`,
  GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[REAL_LT_TRANS]] THEN
  DISCH_TAC THEN MP_TAC(SPEC `inv(e)` REAL_ARCH_LT) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[REAL_LT_INV2; REAL_INV_INV; REAL_LT_INV_EQ; REAL_LT_TRANS;
                REAL_LT_ANTISYM]);;

export_namedthm REAL_ARCH_INV "REAL_ARCH_INV";;

let REAL_POW_LBOUND = prove 
 (`!x n. &0 <= x ==> &1 + &n * x <= (&1 + x) pow n`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  REWRITE_TAC[real_pow; REAL_MUL_LZERO; REAL_ADD_RID; REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + x) * (&1 + &n * x)` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_ARITH
   `&1 + (n + &1) * x <= (&1 + x) * (&1 + n * x) <=> &0 <= n * x * x`]);;

export_namedthm REAL_POW_LBOUND "REAL_POW_LBOUND";;

let REAL_ARCH_POW = prove 
 (`!x y. &1 < x ==> ?n. y < x pow n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x - &1` REAL_ARCH) THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real`) THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `&1 + &n * (x - &1)` THEN
  ASM_SIMP_TAC[REAL_ARITH `x < y ==> x < &1 + y`] THEN
  ASM_MESON_TAC[REAL_POW_LBOUND; REAL_SUB_ADD2; REAL_ARITH
    `&1 < x ==> &0 <= x - &1`]);;

export_namedthm REAL_ARCH_POW "REAL_ARCH_POW";;

let REAL_ARCH_POW2 = prove 
 (`!x. ?n. x < &2 pow n`,
  SIMP_TAC[REAL_ARCH_POW; REAL_OF_NUM_LT; ARITH]);;

export_namedthm REAL_ARCH_POW2 "REAL_ARCH_POW2";;

let REAL_ARCH_POW_INV = prove 
 (`!x y. &0 < y /\ x < &1 ==> ?n. x pow n < y`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 < x` THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_POW_1; REAL_LET_TRANS; REAL_NOT_LT]] THEN
  SUBGOAL_THEN `inv(&1) < inv(x)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV2]; REWRITE_TAC[REAL_INV_1]] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(y)` o MATCH_MP REAL_ARCH_POW) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [GSYM REAL_INV_INV] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_INV; REAL_LT_INV; REAL_LT_INV2]);;

export_namedthm REAL_ARCH_POW_INV "REAL_ARCH_POW_INV";;

(* ------------------------------------------------------------------------- *)
(* The sign of a real number, as a real number.                              *)
(* ------------------------------------------------------------------------- *)

export_theory "real-sign-def";;

let real_sgn = new_definition
 `(real_sgn:real->real) x =
        if &0 < x then &1 else if x < &0 then -- &1 else &0`;;

export_namedthm real_sgn "real_sgn";;

export_theory "real-sign";;

let REAL_SGN_0 = prove 
 (`real_sgn(&0) = &0`,
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC);;

export_namedthm REAL_SGN_0 "REAL_SGN_0";;

let REAL_SGN_NEG = prove 
 (`!x. real_sgn(--x) = --(real_sgn x)`,
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC);;

export_namedthm REAL_SGN_NEG "REAL_SGN_NEG";;

export_theory "real-sign-abs";;

let REAL_SGN_ABS = prove 
 (`!x. real_sgn(x) * abs(x) = x`,
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC);;

export_namedthm REAL_SGN_ABS "REAL_SGN_ABS";;

let REAL_SGN_ABS_ALT = prove 
 (`!x. real_sgn x * x = abs x`,
  GEN_TAC THEN REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC);;

export_namedthm REAL_SGN_ABS_ALT "REAL_SGN_ABS_ALT";;

let REAL_EQ_SGN_ABS = prove 
 (`!x y:real. x = y <=> real_sgn x = real_sgn y /\ abs x = abs y`,
  MESON_TAC[REAL_SGN_ABS]);;

export_namedthm REAL_EQ_SGN_ABS "REAL_EQ_SGN_ABS";;

let REAL_ABS_SGN = prove 
 (`!x. abs(real_sgn x) = real_sgn(abs x)`,
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC);;

export_namedthm REAL_ABS_SGN "REAL_ABS_SGN";;

export_theory "real-sign";;

let REAL_SGN = prove 
 (`!x. real_sgn x = x / abs x`,
  GEN_TAC THEN ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_SGN_0];
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM REAL_SGN_ABS] THEN
    ASM_SIMP_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_ABS_ZERO;
                 REAL_MUL_RINV; REAL_MUL_RID]]);;

export_namedthm REAL_SGN "REAL_SGN";;

let REAL_SGN_MUL = prove 
 (`!x y. real_sgn(x * y) = real_sgn(x) * real_sgn(y)`,
  REWRITE_TAC[REAL_SGN; REAL_ABS_MUL; real_div; REAL_INV_MUL] THEN
  REAL_ARITH_TAC);;

export_namedthm REAL_SGN_MUL "REAL_SGN_MUL";;

let REAL_SGN_INV = prove 
 (`!x. real_sgn(inv x) = real_sgn x`,
  REWRITE_TAC[real_sgn; REAL_LT_INV_EQ; GSYM REAL_INV_NEG;
              REAL_ARITH `x < &0 <=> &0 < --x`]);;

export_namedthm REAL_SGN_INV "REAL_SGN_INV";;

let REAL_SGN_DIV = prove 
 (`!x y. real_sgn(x / y) = real_sgn(x) / real_sgn(y)`,
  REWRITE_TAC[REAL_SGN; REAL_ABS_DIV] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN
  REAL_ARITH_TAC);;

export_namedthm REAL_SGN_DIV "REAL_SGN_DIV";;

let REAL_SGN_EQ = prove 
 (`(!x. real_sgn x = &0 <=> x = &0) /\
   (!x. real_sgn x = &1 <=> x > &0) /\
   (!x. real_sgn x = -- &1 <=> x < &0)`,
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC);;

export_namedthm REAL_SGN_EQ "REAL_SGN_EQ";;

let REAL_SGN_CASES = prove 
 (`!x. real_sgn x = &0 \/ real_sgn x = &1 \/ real_sgn x = -- &1`,
  REWRITE_TAC[real_sgn] THEN MESON_TAC[]);;

export_namedthm REAL_SGN_CASES "REAL_SGN_CASES";;

let REAL_SGN_INEQS = prove 
 (`(!x. &0 <= real_sgn x <=> &0 <= x) /\
   (!x. &0 < real_sgn x <=> &0 < x) /\
   (!x. &0 >= real_sgn x <=> &0 >= x) /\
   (!x. &0 > real_sgn x <=> &0 > x) /\
   (!x. &0 = real_sgn x <=> &0 = x) /\
   (!x. real_sgn x <= &0 <=> x <= &0) /\
   (!x. real_sgn x < &0 <=> x < &0) /\
   (!x. real_sgn x >= &0 <=> x >= &0) /\
   (!x. real_sgn x > &0 <=> x > &0) /\
   (!x. real_sgn x = &0 <=> x = &0)`,
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC);;

export_namedthm REAL_SGN_INEQS "REAL_SGN_INEQS";;

export_theory "real-sign-nl";;

let REAL_SGN_POW = prove 
 (`!x n. real_sgn(x pow n) = real_sgn(x) pow n`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[REAL_SGN_MUL; real_pow] THEN
  REWRITE_TAC[real_sgn; REAL_LT_01]);;

export_namedthm REAL_SGN_POW "REAL_SGN_POW";;

let REAL_SGN_POW_2 = prove 
 (`!x. real_sgn(x pow 2) = real_sgn(abs x)`,
  REWRITE_TAC[real_sgn] THEN
  SIMP_TAC[GSYM REAL_NOT_LE; REAL_ABS_POS; REAL_LE_POW_2;
           REAL_ARITH `&0 <= x ==> (x <= &0 <=> x = &0)`] THEN
  REWRITE_TAC[REAL_POW_EQ_0; REAL_ABS_ZERO; ARITH]);;

export_namedthm REAL_SGN_POW_2 "REAL_SGN_POW_2";;

let REAL_SGN_REAL_SGN = prove 
 (`!x. real_sgn(real_sgn x) = real_sgn x`,
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC);;

export_namedthm REAL_SGN_REAL_SGN "REAL_SGN_REAL_SGN";;

let REAL_INV_SGN = prove 
 (`!x. real_inv(real_sgn x) = real_sgn x`,
  GEN_TAC THEN REWRITE_TAC[real_sgn] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[REAL_INV_0; REAL_INV_1; REAL_INV_NEG]);;

export_namedthm REAL_INV_SGN "REAL_INV_SGN";;

export_theory "real-sign-eq";;

let REAL_SGN_EQ_INEQ = prove 
 (`!x y. real_sgn x = real_sgn y <=>
         x = y \/ abs(x - y) < max (abs x) (abs y)`,
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC);;

export_namedthm REAL_SGN_EQ_INEQ "REAL_SGN_EQ_INEQ";;

let REAL_SGNS_EQ = prove 
 (`!x y. real_sgn x = real_sgn y <=>
         (x = &0 <=> y = &0) /\
         (x > &0 <=> y > &0) /\
         (x < &0 <=> y < &0)`,
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC);;

export_namedthm REAL_SGNS_EQ "REAL_SGNS_EQ";;

let REAL_SGNS_EQ_ALT = prove 
 (`!x y. real_sgn x = real_sgn y <=>
         (x = &0 ==> y = &0) /\
         (x > &0 ==> y > &0) /\
         (x < &0 ==> y < &0)`,
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC);;

export_namedthm REAL_SGNS_EQ_ALT "REAL_SGNS_EQ_ALT";;

(* ------------------------------------------------------------------------- *)
(* Useful "without loss of generality" lemmas.                               *)
(* ------------------------------------------------------------------------- *)

export_theory "real-wlog";;

let REAL_WLOG_LE = prove 
 (`(!x y. P x y <=> P y x) /\ (!x y. x <= y ==> P x y) ==> !x y. P x y`,
  MESON_TAC[REAL_LE_TOTAL]);;

export_namedthm REAL_WLOG_LE "REAL_WLOG_LE";;

let REAL_WLOG_LT = prove 
 (`(!x. P x x) /\ (!x y. P x y <=> P y x) /\ (!x y. x < y ==> P x y)
   ==> !x y. P x y`,
  MESON_TAC[REAL_LT_TOTAL]);;

export_namedthm REAL_WLOG_LT "REAL_WLOG_LT";;

let REAL_WLOG_LE_3 = prove 
 (`!P. (!x y z. P x y z ==> P y x z /\ P x z y) /\
       (!x y z:real. x <= y /\ y <= z ==> P x y z)
       ==> !x y z. P x y z`,
  MESON_TAC[REAL_LE_TOTAL]);;

export_namedthm REAL_WLOG_LE_3 "REAL_WLOG_LE_3";;

(* ------------------------------------------------------------------------- *)
(* Square roots. The existence derivation is laborious but independent of    *)
(* any analytic or topological machinery, just using completeness directly.  *)
(* We totalize by making sqrt(-x) = -sqrt(x), which looks rather unnatural   *)
(* but allows many convenient properties to be used without sideconditions.  *)
(* ------------------------------------------------------------------------- *)

export_theory "real-sqrt-def";;

let sqrt = new_definition
 `sqrt(x) = @y. real_sgn y = real_sgn x /\ y pow 2 = abs x`;;

export_namedthm sqrt "sqrt";;

export_theory "real-sqrt-unique";;

let SQRT_UNIQUE = prove 
 (`!x y. &0 <= y /\ y pow 2 = x ==> sqrt(x) = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sqrt] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_SGN_POW_2; REAL_ABS_POW] THEN
  X_GEN_TAC `z:real` THEN ASM_REWRITE_TAC[real_abs] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_SUB_0; REAL_ARITH
    `x pow 2 = y pow 2 <=> (x - y) * (x - --y) = &0`] THEN
  REWRITE_TAC[real_sgn] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  REAL_ARITH_TAC);;

export_namedthm SQRT_UNIQUE "SQRT_UNIQUE";;

export_theory "real-sqrt";;

let POW_2_SQRT = prove 
 (`!x. &0 <= x ==> sqrt(x pow 2) = x`,
  MESON_TAC[SQRT_UNIQUE]);;

export_namedthm POW_2_SQRT "POW_2_SQRT";;

let SQRT_0 = prove 
 (`sqrt(&0) = &0`,
  MESON_TAC[SQRT_UNIQUE; REAL_POW_2; REAL_MUL_LZERO; REAL_POS]);;

export_namedthm SQRT_0 "SQRT_0";;

let SQRT_1 = prove 
 (`sqrt(&1) = &1`,
   MESON_TAC[SQRT_UNIQUE; REAL_POW_2; REAL_MUL_LID; REAL_POS]);;

export_namedthm SQRT_1 "SQRT_1";;

let POW_2_SQRT_ABS = prove 
 (`!x. sqrt(x pow 2) = abs(x)`,
  GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE THEN
  REWRITE_TAC[REAL_ABS_POS; REAL_POW_2; GSYM REAL_ABS_MUL] THEN
  REWRITE_TAC[real_abs; REAL_LE_SQUARE]);;

export_namedthm POW_2_SQRT_ABS "POW_2_SQRT_ABS";;

export_theory "real-sqrt-works";;

let SQRT_WORKS_GEN = prove 
 (`!x. real_sgn(sqrt x) = real_sgn x /\ sqrt(x) pow 2 = abs x`,
  let lemma = prove
   (`!x y. x pow 2 < y ==> ?x'. x < x' /\ x' pow 2 < y`,
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `abs x + min (&1) ((y - x pow 2) / (&2 * abs x + &2))` THEN
    ASSUME_TAC(REAL_ARITH `&0 < &2 * abs x + &1 /\ &0 < &2 * abs x + &2`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_ARITH
      `&0 < y ==> x < abs x + min (&1) y`] THEN
    REWRITE_TAC[REAL_ARITH `(x + e) pow 2 = e * (&2 * x + e) + x pow 2`] THEN
    REWRITE_TAC[REAL_POW2_ABS; GSYM REAL_LT_SUB_LADD] THEN
    TRANS_TAC REAL_LET_TRANS
      `(y - x pow 2) / (&2 * abs x + &2) * (&2 * abs x + &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[REAL_LE_MIN; REAL_POS; REAL_MIN_LE; REAL_LE_REFL] THEN
      ASM_SIMP_TAC[REAL_LE_ADD; REAL_POS; REAL_LE_MUL; REAL_ABS_POS;
                   REAL_LT_IMP_LE; REAL_LT_DIV; REAL_SUB_LT; REAL_LE_MIN] THEN
      REWRITE_TAC[REAL_LE_LADD; REAL_MIN_LE; REAL_LE_REFL];
      SIMP_TAC[real_div; REAL_ARITH `(a * inv b) * c = (a * c) * inv b`] THEN
      REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_LMUL_EQ; REAL_SUB_LT] THEN
      REAL_ARITH_TAC]) in
  let lemma' = prove
   (`!x y. &0 < x /\ &0 < y /\ y < x pow 2
           ==> ?x'. x' < x /\ &0 < x' /\ y < x' pow 2`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`inv(abs x):real`; `inv y:real`] lemma) THEN
    ASM_SIMP_TAC[REAL_POW_INV; REAL_POW2_ABS; REAL_LT_INV2] THEN
    REWRITE_TAC[GSYM REAL_ABS_INV] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inv x':real` THEN REWRITE_TAC[REAL_POW_INV] THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV];
      CONJ_TAC THENL [REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV]] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN
    (CONJ_TAC THENL
      [ALL_TAC; REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC]) THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_LT_POW_2] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC) in
  let main_lemma = prove
   (`!y. &0 < y ==> ?x. x pow 2 = y`,
    REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
    MP_TAC(ISPEC `\x. &0 <= x /\ x pow 2 <= y` REAL_COMPLETE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [EXISTS_TAC `&0` THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXISTS_TAC `y + &1` THEN X_GEN_TAC `x:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
      TRANS_TAC REAL_LET_TRANS `(y + &1) pow 2` THEN
      ASM_SIMP_TAC[GSYM REAL_LT_SQUARE_ABS; REAL_POW_LT; REAL_ARITH
       `&0 < y /\ &0 < y pow 2 ==> y <= (y + &1) pow 2`] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real` THEN STRIP_TAC] THEN
    REWRITE_TAC[GSYM REAL_LE_ANTISYM; GSYM REAL_NOT_LT] THEN
    REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`s:real`; `y:real`] lemma') THEN
      ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
       [UNDISCH_TAC `y:real < s pow 2` THEN
        ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN
        REWRITE_TAC[REAL_POW_ZERO] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC[REAL_NOT_LE] THEN
        STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `&0 < y` THEN REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `z:real`
         (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
        REWRITE_TAC[REAL_NOT_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        X_GEN_TAC `x:real` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
        REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
        TRANS_TAC REAL_LTE_TRANS `(z:real) pow 2` THEN
        ASM_REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC];
      MP_TAC(ISPECL [`s:real`; `y:real`] lemma) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real`
       (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
      MATCH_MP_TAC(REAL_ARITH `abs z <= s ==> s < z ==> F`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_ABS_POS; REAL_POW2_ABS; REAL_LT_IMP_LE]]) in
  GEN_TAC THEN REWRITE_TAC[sqrt] THEN CONV_TAC SELECT_CONV THEN
  SUBGOAL_THEN `!x. &0 < x ==> ?y. &0 < y /\ y pow 2 = x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(SPEC `x:real` main_lemma) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `y:real` THEN
    STRIP_TAC THEN EXISTS_TAC `abs y:real` THEN
    ASM_REWRITE_TAC[REAL_POW2_ABS; GSYM REAL_ABS_NZ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
    ASM_CASES_TAC `x = &0` THEN
    ASM_REWRITE_TAC[REAL_SGN_0; REAL_SGN_EQ; UNWIND_THM2] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ZERO; ARITH] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `abs x`) THEN
    ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `real_sgn x * y` THEN
    ASM_REWRITE_TAC[REAL_POW_MUL; GSYM REAL_SGN_POW; REAL_SGN_POW_2] THEN
    REWRITE_TAC[REAL_SGN_MUL; REAL_SGN_REAL_SGN] THEN
    ASM_SIMP_TAC[real_sgn; REAL_ARITH `&0 < abs x <=> ~(x = &0)`] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID]]);;

export_namedthm SQRT_WORKS_GEN "SQRT_WORKS_GEN";;

export_theory "real-sqrt-thm";;

let SQRT_UNIQUE_GEN = prove 
 (`!x y. real_sgn y = real_sgn x /\ y pow 2 = abs x ==> sqrt x = y`,
  REPEAT GEN_TAC THEN
  MP_TAC(GSYM(SPEC `x:real` SQRT_WORKS_GEN)) THEN
  SIMP_TAC[REAL_ENTIRE; REAL_SUB_0; REAL_ARITH
    `x pow 2 = y pow 2 <=> (x:real - y) * (x - --y) = &0`] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[IMP_CONJ_ALT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_SGN_NEG] THEN
  SIMP_TAC[REAL_ARITH `--x = x <=> x = &0`; REAL_SGN_EQ; REAL_NEG_0; SQRT_0]);;

export_namedthm SQRT_UNIQUE_GEN "SQRT_UNIQUE_GEN";;

export_theory "real-sqrt-thm";;

let SQRT_NEG = prove 
 (`!x. sqrt(--x) = --sqrt(x)`,
  GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
  REWRITE_TAC[REAL_SGN_NEG; REAL_POW_NEG; REAL_ABS_NEG; ARITH] THEN
  REWRITE_TAC[SQRT_WORKS_GEN]);;

export_namedthm SQRT_NEG "SQRT_NEG";;

let REAL_SGN_SQRT = prove 
 (`!x. real_sgn(sqrt x) = real_sgn x`,
  REWRITE_TAC[SQRT_WORKS_GEN]);;

export_namedthm REAL_SGN_SQRT "REAL_SGN_SQRT";;

let SQRT_WORKS = prove 
 (`!x. &0 <= x ==> &0 <= sqrt(x) /\ sqrt(x) pow 2 = x`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `x:real` SQRT_WORKS_GEN) THEN
  REWRITE_TAC[real_sgn] THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

export_namedthm SQRT_WORKS "SQRT_WORKS";;

let REAL_POS_EQ_SQUARE = prove 
 (`!x. &0 <= x <=> ?y. y pow 2 = x`,
  MESON_TAC[REAL_LE_POW_2; SQRT_WORKS]);;

export_namedthm REAL_POS_EQ_SQUARE "REAL_POS_EQ_SQUARE";;

let SQRT_POS_LE = prove 
 (`!x. &0 <= x ==> &0 <= sqrt(x)`,
  MESON_TAC[SQRT_WORKS]);;

export_namedthm SQRT_POS_LE "SQRT_POS_LE";;

export_theory "real-sqrt-nl";;

let SQRT_POW_2 = prove 
 (`!x. &0 <= x ==> sqrt(x) pow 2 = x`,
  MESON_TAC[SQRT_WORKS]);;

export_namedthm SQRT_POW_2 "SQRT_POW_2";;

let SQRT_POW2 = prove 
 (`!x. sqrt(x) pow 2 = x <=> &0 <= x`,
  MESON_TAC[REAL_POW_2; REAL_LE_SQUARE; SQRT_POW_2]);;

export_namedthm SQRT_POW2 "SQRT_POW2";;

let SQRT_MUL = prove 
 (`!x y. sqrt(x * y) = sqrt x * sqrt y`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
  REWRITE_TAC[REAL_SGN_MUL; REAL_POW_MUL; SQRT_WORKS_GEN; REAL_ABS_MUL]);;

export_namedthm SQRT_MUL "SQRT_MUL";;

let SQRT_INV = prove 
 (`!x. sqrt (inv x) = inv(sqrt x)`,
  GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
  REWRITE_TAC[REAL_SGN_INV; REAL_POW_INV; REAL_ABS_INV; SQRT_WORKS_GEN]);;

export_namedthm SQRT_INV "SQRT_INV";;

let SQRT_DIV = prove 
 (`!x y. sqrt (x / y) = sqrt x / sqrt y`,
  REWRITE_TAC[real_div; SQRT_MUL; SQRT_INV]);;

export_namedthm SQRT_DIV "SQRT_DIV";;

export_theory "real-sqrt-order";;

let SQRT_LT_0 = prove 
 (`!x. &0 < sqrt x <=> &0 < x`,
  REWRITE_TAC[GSYM real_gt; GSYM REAL_SGN_EQ; REAL_SGN_SQRT]);;

export_namedthm SQRT_LT_0 "SQRT_LT_0";;

let SQRT_EQ_0 = prove 
 (`!x. sqrt x = &0 <=> x = &0`,
  ONCE_REWRITE_TAC[GSYM REAL_SGN_EQ] THEN REWRITE_TAC[REAL_SGN_SQRT]);;

export_namedthm SQRT_EQ_0 "SQRT_EQ_0";;

let SQRT_LE_0 = prove 
 (`!x. &0 <= sqrt x <=> &0 <= x`,
  REWRITE_TAC[REAL_ARITH `&0 <= x <=> &0 < x \/ x = &0`] THEN
  REWRITE_TAC[SQRT_LT_0; SQRT_EQ_0]);;

export_namedthm SQRT_LE_0 "SQRT_LE_0";;

let REAL_ABS_SQRT = prove 
 (`!x. abs(sqrt x) = sqrt(abs x)`,
  GEN_TAC THEN REWRITE_TAC[real_abs; SQRT_LE_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SQRT_NEG]);;

export_namedthm REAL_ABS_SQRT "REAL_ABS_SQRT";;

export_theory "real-sqrt-mono";;

let SQRT_MONO_LT = prove 
 (`!x y. x < y ==> sqrt(x) < sqrt(y)`,
  SUBGOAL_THEN `!x y. &0 <= x /\ x < y ==> sqrt x < sqrt y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT2_REV THEN
    EXISTS_TAC `2` THEN ASM_REWRITE_TAC[SQRT_WORKS_GEN; SQRT_LE_0] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= x` THEN ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `&0 <= y` THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[GSYM REAL_NOT_LE; SQRT_LE_0];
      FIRST_X_ASSUM(MP_TAC o SPECL [`--y:real`; `--x:real`]) THEN
      REWRITE_TAC[SQRT_NEG] THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC]]);;

export_namedthm SQRT_MONO_LT "SQRT_MONO_LT";;

let SQRT_MONO_LE = prove 
 (`!x y. x <= y ==> sqrt(x) <= sqrt(y)`,
  MESON_TAC[REAL_LE_LT; SQRT_MONO_LT]);;

export_namedthm SQRT_MONO_LE "SQRT_MONO_LE";;

let SQRT_MONO_LT_EQ = prove 
 (`!x y. sqrt(x) < sqrt(y) <=> x < y`,
  MESON_TAC[REAL_NOT_LT; SQRT_MONO_LT; SQRT_MONO_LE]);;

export_namedthm SQRT_MONO_LT_EQ "SQRT_MONO_LT_EQ";;

let SQRT_MONO_LE_EQ = prove 
 (`!x y. sqrt(x) <= sqrt(y) <=> x <= y`,
  MESON_TAC[REAL_NOT_LT; SQRT_MONO_LT; SQRT_MONO_LE]);;

export_namedthm SQRT_MONO_LE_EQ "SQRT_MONO_LE_EQ";;

export_theory "real-sqrt-thm";;

let SQRT_INJ = prove 
 (`!x y. sqrt(x) = sqrt(y) <=> x = y`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; SQRT_MONO_LE_EQ]);;

export_namedthm SQRT_INJ "SQRT_INJ";;

let SQRT_EQ_1 = prove 
 (`!x. sqrt x = &1 <=> x = &1`,
  MESON_TAC[SQRT_INJ; SQRT_1]);;

export_namedthm SQRT_EQ_1 "SQRT_EQ_1";;

export_theory "real-sqrt-order";;

let SQRT_POS_LT = prove 
 (`!x. &0 < x ==> &0 < sqrt(x)`,
  MESON_TAC[REAL_LT_LE; SQRT_POS_LE; SQRT_EQ_0]);;

export_namedthm SQRT_POS_LT "SQRT_POS_LT";;

let REAL_LE_LSQRT = prove 
 (`!x y. &0 <= y /\ x <= y pow 2 ==> sqrt(x) <= y`,
  MESON_TAC[SQRT_MONO_LE; REAL_POW_LE; POW_2_SQRT]);;

export_namedthm REAL_LE_LSQRT "REAL_LE_LSQRT";;

let REAL_LE_RSQRT = prove 
 (`!x y. x pow 2 <= y ==> x <= sqrt(y)`,
  MESON_TAC[REAL_LE_TOTAL; SQRT_MONO_LE; SQRT_POS_LE; REAL_POW_2;
            REAL_LE_SQUARE; REAL_LE_TRANS; POW_2_SQRT]);;

export_namedthm REAL_LE_RSQRT "REAL_LE_RSQRT";;

let REAL_LT_LSQRT = prove 
 (`!x y. &0 <= y /\ x < y pow 2 ==> sqrt x < y`,
  MESON_TAC[SQRT_MONO_LT; REAL_POW_LE; POW_2_SQRT]);;

export_namedthm REAL_LT_LSQRT "REAL_LT_LSQRT";;

let REAL_LT_RSQRT = prove 
 (`!x y. x pow 2 < y ==> x < sqrt(y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `abs x < a ==> x < a`) THEN
  REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN MATCH_MP_TAC SQRT_MONO_LT THEN
  ASM_REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]);;

export_namedthm REAL_LT_RSQRT "REAL_LT_RSQRT";;

export_theory "real-sqrt-nl";;

let SQRT_EVEN_POW2 = prove 
 (`!n. EVEN n ==> (sqrt(&2 pow n) = &2 pow (n DIV 2))`,
  SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM; DIV_MULT; ARITH_EQ] THEN
  MESON_TAC[SQRT_UNIQUE; REAL_POW_POW; MULT_SYM; REAL_POW_LE; REAL_POS]);;

export_namedthm SQRT_EVEN_POW2 "SQRT_EVEN_POW2";;

let REAL_DIV_SQRT = prove 
 (`!x. &0 <= x ==> x / sqrt(x) = sqrt(x)`,
  REWRITE_TAC[REAL_LE_LT] THEN REPEAT STRIP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SQRT_0; real_div; REAL_MUL_LZERO]] THEN
  ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; SQRT_POS_LT; GSYM REAL_POW_2] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]);;

export_namedthm REAL_DIV_SQRT "REAL_DIV_SQRT";;

let REAL_RSQRT_LE = prove 
 (`!x y. &0 <= x /\ &0 <= y /\ x <= sqrt y ==> x pow 2 <= y`,
  MESON_TAC[REAL_POW_LE2; SQRT_POW_2]);;

export_namedthm REAL_RSQRT_LE "REAL_RSQRT_LE";;

let REAL_LSQRT_LE = prove 
 (`!x y. &0 <= x /\ sqrt x <= y ==> x <= y pow 2`,
  MESON_TAC[REAL_POW_LE2; SQRT_POS_LE; REAL_LE_TRANS; SQRT_POW_2]);;

export_namedthm REAL_LSQRT_LE "REAL_LSQRT_LE";;

let REAL_SQRT_POW_2 = prove 
 (`!x. sqrt x pow 2 = abs x`,
  REWRITE_TAC[SQRT_WORKS_GEN]);;

export_namedthm REAL_SQRT_POW_2 "REAL_SQRT_POW_2";;

let REAL_ABS_LE_SQRT_POS = prove 
 (`!x y. &0 <= x /\ &0 <= y ==> abs(sqrt x - sqrt y) <= sqrt(abs(x - y))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
  REWRITE_TAC[REAL_POW_2] THEN
  TRANS_TAC REAL_LE_TRANS `abs(sqrt x - sqrt y) * abs(sqrt x + sqrt y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ &0 <= y ==> abs(x - y) <= abs(x + y)`) THEN
    ASM_SIMP_TAC[SQRT_POS_LE];
    REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_ARITH
     `(x - y:real) * (x + y) = x pow 2 - y pow 2`] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]]);;

export_namedthm REAL_ABS_LE_SQRT_POS "REAL_ABS_LE_SQRT_POS";;

let REAL_ABS_LE_SQRT = prove 
 (`!x y. abs(sqrt x - sqrt y) <= sqrt(&2 * abs(x - y))`,
  MATCH_MP_TAC REAL_WLOG_LE THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_ABS_SUB]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `&0 <= x` THENL
   [TRANS_TAC REAL_LE_TRANS `sqrt(abs(x - y))` THEN
    REWRITE_TAC[SQRT_MONO_LE_EQ; REAL_ARITH `abs x <= &2 * abs x`] THEN
    MATCH_MP_TAC REAL_ABS_LE_SQRT_POS THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= y` THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[REAL_ARITH `abs(x - y) = abs(--x - --y)`] THEN
    REWRITE_TAC[GSYM SQRT_NEG] THEN
    TRANS_TAC REAL_LE_TRANS `sqrt(abs(--x - --y))` THEN
    REWRITE_TAC[SQRT_MONO_LE_EQ; REAL_ARITH `abs x <= &2 * abs x`] THEN
    MATCH_MP_TAC REAL_ABS_LE_SQRT_POS THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC] THEN
  ASM_SIMP_TAC[SQRT_LE_0; REAL_ARITH
   `~(&0 <= x) /\ &0 <= y ==> abs(x - y) = y - x`] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  MP_TAC(SPEC `sqrt(--x) - sqrt y` REAL_LE_POW_2) THEN
  REWRITE_TAC[REAL_ARITH
   `(x - y:real) pow 2 = (x pow 2 + y pow 2) - &2 * x * y`] THEN
  REWRITE_TAC[REAL_SQRT_POW_2] THEN REWRITE_TAC[SQRT_NEG; REAL_ABS_NEG] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

export_namedthm REAL_ABS_LE_SQRT "REAL_ABS_LE_SQRT";;
