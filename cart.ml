

(* ========================================================================= *)
(* Definition of finite Cartesian product types.                             *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*     (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018              *)
(* ========================================================================= *)

needs "iterate.ml";;

(* ------------------------------------------------------------------------- *)
(* Association of a number with an indexing type.                            *)
(* ------------------------------------------------------------------------- *)

export_theory "dimindex-def";;

let dimindex = new_definition 
  `dimindex(s:A->bool) = if FINITE(:A) then CARD(:A) else 1`;;

export_namedthm dimindex "dimindex";;

export_theory "dimindex-thm";;

let DIMINDEX_NONZERO = prove 
 (`!s:A->bool. ~(dimindex(s) = 0)`,
  GEN_TAC THEN REWRITE_TAC[dimindex] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[CARD_EQ_0; ARITH] THEN SET_TAC[]);;

export_namedthm DIMINDEX_NONZERO "DIMINDEX_NONZERO";;

let DIMINDEX_GE_1 = prove 
 (`!s:A->bool. 1 <= dimindex(s)`,
  REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; DIMINDEX_NONZERO]);;

export_namedthm DIMINDEX_GE_1 "DIMINDEX_GE_1";;

let DIMINDEX_UNIV = prove 
 (`!s. dimindex(s:A->bool) = dimindex(:A)`,
  REWRITE_TAC[dimindex]);;

export_namedthm DIMINDEX_UNIV "DIMINDEX_UNIV";;

let DIMINDEX_UNIQUE = prove 
 (`(:A) HAS_SIZE n ==> dimindex(:A) = n`,
  MESON_TAC[dimindex; HAS_SIZE]);;

export_namedthm DIMINDEX_UNIQUE "DIMINDEX_UNIQUE";;

let UNIV_HAS_SIZE_DIMINDEX = prove 
 (`(:N) HAS_SIZE dimindex (:N) <=> FINITE(:N)`,
  MESON_TAC[HAS_SIZE; dimindex]);;

export_namedthm UNIV_HAS_SIZE_DIMINDEX "UNIV_HAS_SIZE_DIMINDEX";;

let HAS_SIZE_1 = prove 
 (`(:1) HAS_SIZE 1`,
  SUBGOAL_THEN `(:1) = {one}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIV; IN_SING] THEN MESON_TAC[one];
    SIMP_TAC[NOT_IN_EMPTY; HAS_SIZE; FINITE_RULES; CARD_CLAUSES; ARITH]]);;

export_namedthm HAS_SIZE_1 "HAS_SIZE_1";;

let DIMINDEX_1 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_1;;

export_namedthm DIMINDEX_1 "DIMINDEX_1";;

(* ------------------------------------------------------------------------- *)
(* An indexing type with that size, parametrized by base type.               *)
(* ------------------------------------------------------------------------- *)

export_theory "index-type";;

let finite_image_tybij =
  new_type_definition "finite_image" ("finite_index","dest_finite_image")
  (prove
   (`?x. x IN 1..dimindex(:A)`,
    EXISTS_TAC `1` THEN REWRITE_TAC[IN_NUMSEG; LE_REFL; DIMINDEX_GE_1]));;

export_namedthm finite_image_tybij "finite_image_tybij";;

let FINITE_IMAGE_IMAGE = prove 
 (`UNIV:(A)finite_image->bool = IMAGE finite_index (1..dimindex(:A))`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
  MESON_TAC[finite_image_tybij]);;

export_namedthm FINITE_IMAGE_IMAGE "FINITE_IMAGE_IMAGE";;

(* ------------------------------------------------------------------------- *)
(* Dimension of such a type, and indexing over it.                           *)
(* ------------------------------------------------------------------------- *)

export_theory "dimindex-thm";;

let HAS_SIZE_FINITE_IMAGE = prove 
 (`!s. (UNIV:(A)finite_image->bool) HAS_SIZE dimindex(s:A->bool)`,
  GEN_TAC THEN SIMP_TAC[FINITE_IMAGE_IMAGE] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  ONCE_REWRITE_TAC[DIMINDEX_UNIV] THEN REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
  MESON_TAC[finite_image_tybij]);;

export_namedthm HAS_SIZE_FINITE_IMAGE "HAS_SIZE_FINITE_IMAGE";;

let CARD_FINITE_IMAGE = prove 
 (`!s. CARD(UNIV:(A)finite_image->bool) = dimindex(s:A->bool)`,
  MESON_TAC[HAS_SIZE_FINITE_IMAGE; HAS_SIZE]);;

export_namedthm CARD_FINITE_IMAGE "CARD_FINITE_IMAGE";;

let FINITE_FINITE_IMAGE = prove 
 (`FINITE(UNIV:(A)finite_image->bool)`,
  MESON_TAC[HAS_SIZE_FINITE_IMAGE; HAS_SIZE]);;

export_namedthm FINITE_FINITE_IMAGE "FINITE_FINITE_IMAGE";;

let DIMINDEX_FINITE_IMAGE = prove 
 (`!s t. dimindex(s:(A)finite_image->bool) = dimindex(t:A->bool)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
  MP_TAC(ISPEC `t:A->bool` HAS_SIZE_FINITE_IMAGE) THEN
  SIMP_TAC[FINITE_FINITE_IMAGE; HAS_SIZE]);;

export_namedthm DIMINDEX_FINITE_IMAGE "DIMINDEX_FINITE_IMAGE";;

let FINITE_INDEX_WORKS = prove 
 (`!i:(A)finite_image.
        ?!n. 1 <= n /\ n <= dimindex(:A) /\ (finite_index n = i)`,
  REWRITE_TAC[CONJ_ASSOC; GSYM IN_NUMSEG] THEN MESON_TAC[finite_image_tybij]);;

export_namedthm FINITE_INDEX_WORKS "FINITE_INDEX_WORKS";;

let FINITE_INDEX_INJ = prove 
 (`!i j. 1 <= i /\ i <= dimindex(:A) /\
         1 <= j /\ j <= dimindex(:A)
         ==> ((finite_index i :A finite_image = finite_index j) <=>
              (i = j))`,
  MESON_TAC[FINITE_INDEX_WORKS]);;

export_namedthm FINITE_INDEX_INJ "FINITE_INDEX_INJ";;

let FORALL_FINITE_INDEX = prove 
 (`(!k:(N)finite_image. P k) =
   (!i. 1 <= i /\ i <= dimindex(:N) ==> P(finite_index i))`,
  MESON_TAC[FINITE_INDEX_WORKS]);;

export_namedthm FORALL_FINITE_INDEX "FORALL_FINITE_INDEX";;

(* ------------------------------------------------------------------------- *)
(* Hence finite Cartesian products, with indexing and lambdas.               *)
(* ------------------------------------------------------------------------- *)

export_theory "index-cart-prod";;

let cart_tybij =
  new_type_definition "cart" ("mk_cart","dest_cart")
   (prove(`?f:(B)finite_image->A. T`,REWRITE_TAC[]));;

export_namedthm cart_tybij "cart_tybij";;

parse_as_infix("$",(25,"left"));;

let finite_index = new_definition 
  `x$i = dest_cart x (finite_index i)`;;

export_namedthm finite_index "finite_index";;

let CART_EQ = prove 
 (`!x:A^B y.
    (x = y) <=> !i. 1 <= i /\ i <= dimindex(:B) ==> (x$i = y$i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[finite_index; GSYM FORALL_FINITE_INDEX] THEN
  REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX] THEN MESON_TAC[cart_tybij]);;

export_namedthm CART_EQ "CART_EQ";;

parse_as_binder "lambda";;

let lambda = new_definition 
  `(lambda) g =
     @f:A^B. !i. 1 <= i /\ i <= dimindex(:B) ==> (f$i = g i)`;;

export_namedthm lambda "lambda";;

let LAMBDA_BETA = prove 
 (`!i. 1 <= i /\ i <= dimindex(:B)
       ==> (((lambda) g:A^B) $i = g i)`,
  REWRITE_TAC[lambda] THEN CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `mk_cart(\k. g(@i. 1 <= i /\  i <= dimindex(:B) /\
                                (finite_index i = k))):A^B` THEN
  REWRITE_TAC[finite_index; REWRITE_RULE[] cart_tybij] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  GEN_TAC THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[FINITE_INDEX_INJ; DIMINDEX_FINITE_IMAGE]);;

export_namedthm LAMBDA_BETA "LAMBDA_BETA";;

let LAMBDA_UNIQUE = prove 
 (`!f:A^B g.
        (!i. 1 <= i /\ i <= dimindex(:B) ==> (f$i = g i)) <=>
        ((lambda) g = f)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN MESON_TAC[]);;

export_namedthm LAMBDA_UNIQUE "LAMBDA_UNIQUE";;

let LAMBDA_ETA = prove 
 (`!g. (lambda i. g$i) = g`,
  REWRITE_TAC[CART_EQ; LAMBDA_BETA]);;

export_namedthm LAMBDA_ETA "LAMBDA_ETA";;

(* ------------------------------------------------------------------------- *)
(* For some purposes we can avoid side-conditions on the index.              *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDEX_INRANGE = prove 
 (`!i. ?k. 1 <= k /\ k <= dimindex(:N) /\ !x:A^N. x$i = x$k`,
  REWRITE_TAC[finite_index] THEN MESON_TAC[FINITE_INDEX_WORKS]);;

export_namedthm FINITE_INDEX_INRANGE "FINITE_INDEX_INRANGE";;

let FINITE_INDEX_INRANGE_2 = prove 
 (`!i. ?k. 1 <= k /\ k <= dimindex(:N) /\
           (!x:A^N. x$i = x$k) /\ (!y:B^N. y$i = y$k)`,
  REWRITE_TAC[finite_index] THEN MESON_TAC[FINITE_INDEX_WORKS]);;

export_namedthm FINITE_INDEX_INRANGE_2 "FINITE_INDEX_INRANGE_2";;

let CART_EQ_FULL = prove 
 (`!x y:A^N. x = y <=> !i. x$i = y$i`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN SIMP_TAC[CART_EQ]);;

export_namedthm CART_EQ_FULL "CART_EQ_FULL";;

(* ------------------------------------------------------------------------- *)
(* We need a non-standard sum to "paste" together Cartesian products.        *)
(* ------------------------------------------------------------------------- *)

export_theory "type-index-sum";;

let finite_sum_tybij =
  let th = prove
   (`?x. x IN 1..(dimindex(:A) + dimindex(:B))`,
    EXISTS_TAC `1` THEN SIMP_TAC[IN_NUMSEG; LE_REFL; DIMINDEX_GE_1;
      ARITH_RULE `1 <= a ==> 1 <= a + b`]) in
  new_type_definition "finite_sum" ("mk_finite_sum","dest_finite_sum") th;;

export_namedthm finite_sum_tybij "finite_sum_tybij";;

let pastecart = new_definition 
  `(pastecart:A^M->A^N->A^(M,N)finite_sum) f g =
        lambda i. if i <= dimindex(:M) then f$i
                  else g$(i - dimindex(:M))`;;

export_namedthm pastecart "pastecart";;

let fstcart = new_definition 
  `(fstcart:A^(M,N)finite_sum->A^M) f = lambda i. f$i`;;

export_namedthm fstcart "fstcart";;

let sndcart = new_definition 
  `(sndcart:A^(M,N)finite_sum->A^N) f =
        lambda i. f$(i + dimindex(:M))`;;

export_namedthm sndcart "sndcart";;

let FINITE_SUM_IMAGE = prove 
 (`UNIV:(A,B)finite_sum->bool =
       IMAGE mk_finite_sum (1..(dimindex(:A)+dimindex(:B)))`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
  MESON_TAC[finite_sum_tybij]);;

export_namedthm FINITE_SUM_IMAGE "FINITE_SUM_IMAGE";;

let DIMINDEX_HAS_SIZE_FINITE_SUM = prove 
 (`(UNIV:(M,N)finite_sum->bool) HAS_SIZE (dimindex(:M) + dimindex(:N))`,
  SIMP_TAC[FINITE_SUM_IMAGE] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  ONCE_REWRITE_TAC[DIMINDEX_UNIV] THEN REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
  MESON_TAC[finite_sum_tybij]);;

export_namedthm DIMINDEX_HAS_SIZE_FINITE_SUM "DIMINDEX_HAS_SIZE_FINITE_SUM";;

let DIMINDEX_FINITE_SUM = prove 
 (`dimindex(:(M,N)finite_sum) = dimindex(:M) + dimindex(:N)`,
  GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] DIMINDEX_HAS_SIZE_FINITE_SUM]);;

export_namedthm DIMINDEX_FINITE_SUM "DIMINDEX_FINITE_SUM";;

let FSTCART_PASTECART = prove 
 (`!x y. fstcart(pastecart (x:A^M) (y:A^N)) = x`,
  SIMP_TAC[pastecart; fstcart; CART_EQ; LAMBDA_BETA; DIMINDEX_FINITE_SUM;
           ARITH_RULE `a <= b ==> a <= b + c`]);;

export_namedthm FSTCART_PASTECART "FSTCART_PASTECART";;

let SNDCART_PASTECART = prove 
 (`!x y. sndcart(pastecart (x:A^M) (y:A^N)) = y`,
  SIMP_TAC[pastecart; sndcart; CART_EQ; LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
  W(fun (_,w) -> MP_TAC (PART_MATCH (lhs o rand) LAMBDA_BETA (lhand w))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN MATCH_MP_TAC
     (ARITH_RULE `1 <= i /\ i <= b ==> 1 <= i + a /\ i + a <= a + b`) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ADD_SUB; ARITH_RULE `1 <= i ==> ~(i + a <= a)`]]);;

export_namedthm SNDCART_PASTECART "SNDCART_PASTECART";;

let PASTECART_FST_SND = prove 
 (`!z. pastecart (fstcart z) (sndcart z) = z`,
  SIMP_TAC[pastecart; fstcart; sndcart; CART_EQ; LAMBDA_BETA] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIMINDEX_FINITE_SUM; LAMBDA_BETA;
     ARITH_RULE `i <= a + b ==> i - a <= b`;
     ARITH_RULE `~(i <= a) ==> 1 <= i - a`;
     ARITH_RULE `~(i <= a) ==> ((i - a) + a = i)`]);;

export_namedthm PASTECART_FST_SND "PASTECART_FST_SND";;

let PASTECART_EQ = prove 
 (`!x y. (x = y) <=> (fstcart x = fstcart y) /\ (sndcart x = sndcart y)`,
  MESON_TAC[PASTECART_FST_SND]);;

export_namedthm PASTECART_EQ "PASTECART_EQ";;

let FORALL_PASTECART = prove 
 (`(!p. P p) <=> !x y. P (pastecart x y)`,
  MESON_TAC[PASTECART_FST_SND; FSTCART_PASTECART; SNDCART_PASTECART]);;

export_namedthm FORALL_PASTECART "FORALL_PASTECART";;

let EXISTS_PASTECART = prove 
 (`(?p. P p) <=> ?x y. P (pastecart x y)`,
  MESON_TAC[PASTECART_FST_SND; FSTCART_PASTECART; SNDCART_PASTECART]);;

export_namedthm EXISTS_PASTECART "EXISTS_PASTECART";;

let PASTECART_INJ = prove 
 (`!x:A^M y:A^N w z. pastecart x y = pastecart w z <=> x = w /\ y = z`,
  REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART]);;

export_namedthm PASTECART_INJ "PASTECART_INJ";;

let FSTCART_COMPONENT = prove 
 (`!x:A^(M,N)finite_sum i. 1 <= i /\ i <= dimindex(:M)
                           ==> fstcart x$i = x$i`,
  SIMP_TAC[fstcart; LAMBDA_BETA]);;

export_namedthm FSTCART_COMPONENT "FSTCART_COMPONENT";;

let SNDCART_COMPONENT = prove 
 (`!x:A^(M,N)finite_sum i. 1 <= i /\ i <= dimindex(:N)
                           ==> sndcart x$i = x$(i + dimindex(:M))`,
  SIMP_TAC[sndcart; LAMBDA_BETA]);;

export_namedthm SNDCART_COMPONENT "SNDCART_COMPONENT";;

let PASTECART_COMPONENT = prove 
 (`(!u:A^M v:A^N i. 1 <= i /\ i <= dimindex(:M) ==> pastecart u v$i = u$i) /\
   (!u:A^M v:A^N i. dimindex(:M) + 1 <= i /\ i <= dimindex(:M) + dimindex(:N)
                    ==> pastecart u v$i = v$(i - dimindex(:M)))`,
  REWRITE_TAC[pastecart] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
  [SUBGOAL_THEN `i <= dimindex(:(M,N)finite_sum)`
     (fun th -> ASM_SIMP_TAC[LAMBDA_BETA; th]) THEN
   REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN ASM_ARITH_TAC;
   ASM_SIMP_TAC[LAMBDA_BETA; DIMINDEX_FINITE_SUM;
                ARITH_RULE `dimindex(:M) + 1 <= i ==> 1 <= i`] THEN
   COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

export_namedthm PASTECART_COMPONENT "PASTECART_COMPONENT";;

(* ------------------------------------------------------------------------- *)
(* Likewise a "subtraction" function on type indices.                        *)
(* ------------------------------------------------------------------------- *)

export_theory "type-index-diff";;

let finite_diff_tybij =
  let th = prove
   (`?x. x IN 1..(if dimindex(:B) < dimindex(:A)
                  then dimindex(:A) - dimindex(:B) else 1)`,
    EXISTS_TAC `1` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC) in
  new_type_definition "finite_diff" ("mk_finite_diff","dest_finite_diff") th;;

export_namedthm finite_diff_tybij "finite_diff_tybij";;

let FINITE_DIFF_IMAGE = prove 
 (`UNIV:(A,B)finite_diff->bool =
       IMAGE mk_finite_diff
       (1..(if dimindex(:B) < dimindex(:A)
                  then dimindex(:A) - dimindex(:B) else 1))`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
  MESON_TAC[finite_diff_tybij]);;

export_namedthm FINITE_DIFF_IMAGE "FINITE_DIFF_IMAGE";;

let DIMINDEX_HAS_SIZE_FINITE_DIFF = prove 
 (`(UNIV:(M,N)finite_diff->bool) HAS_SIZE
   (if dimindex(:N) < dimindex(:M) then dimindex(:M) - dimindex(:N) else 1)`,
  SIMP_TAC[FINITE_DIFF_IMAGE] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  ONCE_REWRITE_TAC[DIMINDEX_UNIV] THEN REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
  MESON_TAC[finite_diff_tybij]);;

export_namedthm DIMINDEX_HAS_SIZE_FINITE_DIFF "DIMINDEX_HAS_SIZE_FINITE_DIFF";;

let DIMINDEX_FINITE_DIFF = prove 
 (`dimindex(:(M,N)finite_diff) =
     if dimindex(:N) < dimindex(:M) then dimindex(:M) - dimindex(:N) else 1`,
  GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] DIMINDEX_HAS_SIZE_FINITE_DIFF]);;

export_namedthm DIMINDEX_FINITE_DIFF "DIMINDEX_FINITE_DIFF";;

(* ------------------------------------------------------------------------- *)
(* And a finite-forcing "multiplication" on type indices.                    *)
(* ------------------------------------------------------------------------- *)

export_theory "type-index-mul";;

let finite_prod_tybij =
  let th = prove
   (`?x. x IN 1..(dimindex(:A) * dimindex(:B))`,
     EXISTS_TAC `1` THEN REWRITE_TAC[IN_NUMSEG; LE_REFL] THEN
     MESON_TAC[LE_1; DIMINDEX_GE_1; MULT_EQ_0]) in
  new_type_definition "finite_prod" ("mk_finite_prod","dest_finite_prod") th;;

export_namedthm finite_prod_tybij "finite_prod_tybij";;

let FINITE_PROD_IMAGE = prove 
 (`UNIV:(A,B)finite_prod->bool =
       IMAGE mk_finite_prod (1..(dimindex(:A)*dimindex(:B)))`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
  MESON_TAC[finite_prod_tybij]);;

export_namedthm FINITE_PROD_IMAGE "FINITE_PROD_IMAGE";;

let DIMINDEX_HAS_SIZE_FINITE_PROD = prove 
 (`(UNIV:(M,N)finite_prod->bool) HAS_SIZE (dimindex(:M) * dimindex(:N))`,
  SIMP_TAC[FINITE_PROD_IMAGE] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  ONCE_REWRITE_TAC[DIMINDEX_UNIV] THEN REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
  MESON_TAC[finite_prod_tybij]);;

export_namedthm DIMINDEX_HAS_SIZE_FINITE_PROD "DIMINDEX_HAS_SIZE_FINITE_PROD";;

let DIMINDEX_FINITE_PROD = prove 
 (`dimindex(:(M,N)finite_prod) = dimindex(:M) * dimindex(:N)`,
  GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] DIMINDEX_HAS_SIZE_FINITE_PROD]);;

export_namedthm DIMINDEX_FINITE_PROD "DIMINDEX_FINITE_PROD";;

(* ------------------------------------------------------------------------- *)
(* Type constructors for setting up finite types indexed by binary numbers.  *)
(* ------------------------------------------------------------------------- *)

export_theory "types-index-bin";;

let tybit0_INDUCT,tybit0_RECURSION = define_type
  "tybit0 = mktybit0((A,A)finite_sum)";;

export_namedthm tybit0_INDUCT "tybit0_INDUCT";;
export_namedthm tybit0_RECURSION "tybit0_RECURSION";;

let tybit1_INDUCT,tybit1_RECURSION = define_type
  "tybit1 = mktybit1(((A,A)finite_sum,1)finite_sum)";;

export_namedthm tybit1_INDUCT "tybit1_INDUCT";;
export_namedthm tybit1_RECURSION "tybit1_RECURSION";;

let HAS_SIZE_TYBIT0 = prove 
 (`(:(A)tybit0) HAS_SIZE 2 * dimindex(:A)`,
  SUBGOAL_THEN
   `(:(A)tybit0) = IMAGE mktybit0 (:(A,A)finite_sum)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC[IN_UNIV] THEN MESON_TAC[cases "tybit0"];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    REWRITE_TAC[IN_UNIV; injectivity "tybit0"] THEN
    W(MP_TAC o PART_MATCH lhand
      DIMINDEX_HAS_SIZE_FINITE_SUM o lhand o snd) THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; GSYM MULT_2]]);;

export_namedthm HAS_SIZE_TYBIT0 "HAS_SIZE_TYBIT0";;

let HAS_SIZE_TYBIT1 = prove 
 (`(:(A)tybit1) HAS_SIZE 2 * dimindex(:A) + 1`,
  SUBGOAL_THEN
   `(:(A)tybit1) = IMAGE mktybit1 (:((A,A)finite_sum,1)finite_sum)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC[IN_UNIV] THEN MESON_TAC[cases "tybit1"];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    REWRITE_TAC[IN_UNIV; injectivity "tybit1"] THEN
    W(MP_TAC o PART_MATCH lhand
      DIMINDEX_HAS_SIZE_FINITE_SUM o lhand o snd) THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM MULT_2]]);;

export_namedthm HAS_SIZE_TYBIT1 "HAS_SIZE_TYBIT1";;

let DIMINDEX_TYBIT0 = prove 
 (`dimindex(:(A)tybit0) = 2 * dimindex(:A)`,
  MATCH_MP_TAC DIMINDEX_UNIQUE THEN MATCH_ACCEPT_TAC HAS_SIZE_TYBIT0);;

export_namedthm DIMINDEX_TYBIT0 "DIMINDEX_TYBIT0";;

let DIMINDEX_TYBIT1 = prove 
 (`dimindex(:(A)tybit1) = 2 * dimindex(:A) + 1`,
  MATCH_MP_TAC DIMINDEX_UNIQUE THEN MATCH_ACCEPT_TAC HAS_SIZE_TYBIT1);;

export_namedthm DIMINDEX_TYBIT1 "DIMINDEX_TYBIT1";;

let DIMINDEX_CLAUSES = prove 
 (`dimindex(:1) = 1 /\
   dimindex(:(A)tybit0) = 2 * dimindex(:A) /\
   dimindex(:(A)tybit1) = 2 * dimindex(:A) + 1`,
 REWRITE_TAC[DIMINDEX_1] THEN CONJ_TAC THEN
 MATCH_MP_TAC DIMINDEX_UNIQUE THEN
 REWRITE_TAC[ HAS_SIZE_TYBIT0; HAS_SIZE_TYBIT1]);;

export_namedthm DIMINDEX_CLAUSES "DIMINDEX_CLAUSES";;

let FINITE_1 = prove 
 (`FINITE (:1)`,
  MESON_TAC[HAS_SIZE_1; HAS_SIZE]);;

export_namedthm FINITE_1 "FINITE_1";;

let FINITE_TYBIT0 = prove 
 (`FINITE (:A tybit0)`,
  MESON_TAC[HAS_SIZE_TYBIT0; HAS_SIZE]);;

export_namedthm FINITE_TYBIT0 "FINITE_TYBIT0";;

let FINITE_TYBIT1 = prove 
 (`FINITE (:A tybit1)`,
  MESON_TAC[HAS_SIZE_TYBIT1; HAS_SIZE]);;

export_namedthm FINITE_TYBIT1 "FINITE_TYBIT1";;

let FINITE_CLAUSES = prove 
 (`FINITE(:1) /\ FINITE(:A tybit0) /\ FINITE(:A tybit1)`,
  REWRITE_TAC[FINITE_1; FINITE_TYBIT0; FINITE_TYBIT1]);;

export_namedthm FINITE_CLAUSES "FINITE_CLAUSES";;

(* ------------------------------------------------------------------------- *)
(* Computing dimindex of fintypes.                                           *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_CONV : conv =
  let [pth_num;pth0;pth1;pth_one] = (CONJUNCTS o prove)
   (`(dimindex(:A) = n <=> dimindex(s:A->bool) = NUMERAL n) /\
     (dimindex(:A) = n <=> dimindex(:A tybit0) = BIT0 n) /\
     (dimindex(:A) = n <=> dimindex(:A tybit1) = BIT1 n) /\
     dimindex(:1) = BIT1 _0`,
    CONJ_TAC THENL [REWRITE_TAC[NUMERAL; dimindex]; ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_CLAUSES] THEN CONV_TAC BITS_ELIM_CONV THEN
    ARITH_TAC) in
  let nvar = `n:num` in
  let rec calc_dimindex ty =
    match ty with
      Tyapp("1",_) -> pth_one
    | Tyapp("tybit0",ty'::_) ->
        let th = calc_dimindex ty' in
        let n = rand(concl th) in
        EQ_MP (INST [n,nvar] (INST_TYPE [ty',aty] pth0)) th
    | Tyapp("tybit1",ty'::_) ->
        let th = calc_dimindex ty' in
        let n = rand(concl th) in
        EQ_MP (INST [n,nvar] (INST_TYPE [ty',aty] pth1)) th
    | _ -> fail() in
  function
    Comb(Const("dimindex",_),tm) ->
      let uty = type_of tm in
      let _,(sty::_) = dest_type uty in
      let th = calc_dimindex sty in
      let svar = mk_var("s",uty)
      and ntm = rand(concl th) in
      let pth = INST [tm,svar;ntm,nvar] (INST_TYPE [sty,aty] pth_num) in
      EQ_MP pth th
   | _ -> failwith "DIMINDEX_CONV";;

let HAS_SIZE_DIMINDEX_RULE =
  let pth = prove
   (`(:A) HAS_SIZE n <=> FINITE(:A) /\ dimindex(:A) = n`,
    MESON_TAC[UNIV_HAS_SIZE_DIMINDEX; HAS_SIZE]) in
  let htm = `(HAS_SIZE) (:A)`
  and conv = GEN_REWRITE_CONV I [pth]
  and rule = EQT_ELIM o GEN_REWRITE_CONV I [FINITE_CLAUSES] in
  fun nty ->
    let tm = mk_comb(inst[nty,aty] htm,mk_numeral (dest_finty nty)) in
    let th1 = conv tm in
    EQ_MP (SYM th1)
          (CONJ (rule (lhand(rand(concl th1))))
                (DIMINDEX_CONV (lhand(rand(rand(concl th1))))));;

let DIMINDEX_TAC : tactic =
  CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV);;

(* ------------------------------------------------------------------------- *)
(* Remember cases 2, 3 and 4, which are especially useful for real^N.        *)
(* ------------------------------------------------------------------------- *)

export_theory "dimindex-fintype";;

let DIMINDEX_2 = prove 
 (`dimindex (:2) = 2`,
  DIMINDEX_TAC THEN REFL_TAC);;

export_namedthm DIMINDEX_2 "DIMINDEX_2";;

let DIMINDEX_3 = prove 
 (`dimindex (:3) = 3`,
  DIMINDEX_TAC THEN REFL_TAC);;

export_namedthm DIMINDEX_3 "DIMINDEX_3";;

let DIMINDEX_4 = prove 
 (`dimindex (:4) = 4`,
  DIMINDEX_TAC THEN REFL_TAC);;

export_namedthm DIMINDEX_4 "DIMINDEX_4";;

let HAS_SIZE_2 = HAS_SIZE_DIMINDEX_RULE `:2`;;
let HAS_SIZE_3 = HAS_SIZE_DIMINDEX_RULE `:3`;;
let HAS_SIZE_4 = HAS_SIZE_DIMINDEX_RULE `:4`;;

export_namedthm HAS_SIZE_2 "HAS_SIZE_2";;
export_namedthm HAS_SIZE_3 "HAS_SIZE_3";;
export_namedthm HAS_SIZE_4 "HAS_SIZE_4";;

(* ------------------------------------------------------------------------- *)
(* Finiteness lemma.                                                         *)
(* ------------------------------------------------------------------------- *)

export_theory "finite-cart";;

let FINITE_CART = prove 
 (`!P. (!i. 1 <= i /\ i <= dimindex(:N) ==> FINITE {x | P i x})
       ==> FINITE {v:A^N | !i. 1 <= i /\ i <= dimindex(:N) ==> P i (v$i)}`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:N)
        ==> FINITE {v:A^N | (!i. 1 <= i /\ i <= dimindex(:N) /\ i <= n
                                 ==> P i (v$i)) /\
                            (!i. 1 <= i /\ i <= dimindex(:N) /\ n < i
                                 ==> v$i = @x. F)}`
   (MP_TAC o SPEC `dimindex(:N)`) THEN REWRITE_TAC[LE_REFL; LET_ANTISYM] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= n /\ i <= 0 <=> F`] THEN
    SIMP_TAC[ARITH_RULE `1 <= i /\ i <= n /\ 0 < i <=> 1 <= i /\ i <= n`] THEN
    SUBGOAL_THEN
     `{v | !i. 1 <= i /\ i <= dimindex (:N) ==> v$i = (@x. F)} =
      {(lambda i. @x. F):A^N}`
     (fun th -> SIMP_TAC[FINITE_RULES;th]) THEN
    SIMP_TAC[EXTENSION; IN_SING; IN_ELIM_THM; CART_EQ; LAMBDA_BETA];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
   `IMAGE (\(x:A,v:A^N). (lambda i. if i = SUC n then x else v$i):A^N)
          {x,v | x IN {x:A | P (SUC n) x} /\
                 v IN {v:A^N | (!i. 1 <= i /\ i <= dimindex(:N) /\ i <= n
                                ==> P i (v$i)) /\
                           (!i. 1 <= i /\ i <= dimindex (:N) /\ n < i
                                ==> v$i = (@x. F))}}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN
    ASM_SIMP_TAC[FINITE_PRODUCT; ARITH_RULE `1 <= SUC n`;
                 ARITH_RULE `SUC n <= m ==> n <= m`];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_PAIR_THM; EXISTS_PAIR_THM] THEN
  X_GEN_TAC `v:A^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN EXISTS_TAC `(v:A^N)$(SUC n)` THEN
  EXISTS_TAC `(lambda i. if i = SUC n then @x. F else (v:A^N)$i):A^N` THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; ARITH_RULE `i <= n ==> ~(i = SUC n)`] THEN
  ASM_MESON_TAC[LE; ARITH_RULE `1 <= SUC n`;
                ARITH_RULE `n < i /\ ~(i = SUC n) ==> SUC n < i`]);;

export_namedthm FINITE_CART "FINITE_CART";;

(* ------------------------------------------------------------------------- *)
(* More cardinality results for whole universe.                              *)
(* ------------------------------------------------------------------------- *)

export_theory "set-card-thm";;

let HAS_SIZE_CART_UNIV = prove 
 (`!m. (:A) HAS_SIZE m ==> (:A^N) HAS_SIZE m EXP (dimindex(:N))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(:(N)finite_image->A) HAS_SIZE m EXP (dimindex(:N))`
  MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE_FUNSPACE_UNIV; HAS_SIZE_FINITE_IMAGE];
    DISCH_THEN(MP_TAC o ISPEC `mk_cart:((N)finite_image->A)->A^N` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] HAS_SIZE_IMAGE_INJ)) THEN
    REWRITE_TAC[IN_UNIV] THEN
    ANTS_TAC THENL [MESON_TAC[cart_tybij]; MATCH_MP_TAC EQ_IMP] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC[IN_UNIV] THEN MESON_TAC[cart_tybij]]);;

export_namedthm HAS_SIZE_CART_UNIV "HAS_SIZE_CART_UNIV";;

let CARD_CART_UNIV = prove 
 (`FINITE(:A) ==> CARD(:A^N) = CARD(:A) EXP dimindex(:N)`,
  MESON_TAC[HAS_SIZE_CART_UNIV; HAS_SIZE]);;

export_namedthm CARD_CART_UNIV "CARD_CART_UNIV";;

let FINITE_CART_UNIV = prove 
 (`FINITE(:A) ==> FINITE(:A^N)`,
  MESON_TAC[HAS_SIZE_CART_UNIV; HAS_SIZE]);;

export_namedthm FINITE_CART_UNIV "FINITE_CART_UNIV";;

(* ------------------------------------------------------------------------- *)
(* Explicit construction of a vector from a list of components.              *)
(* ------------------------------------------------------------------------- *)

export_theory "vector";;

let vector = new_definition 
  `(vector l):A^N = lambda i. EL (i - 1) l`;;

export_namedthm vector "vector";;

(* ------------------------------------------------------------------------- *)
(* Convenient set membership elimination theorem.                            *)
(* ------------------------------------------------------------------------- *)

export_theory "set-mem-elim";;

let IN_ELIM_PASTECART_THM = prove 
 (`!P a b. pastecart a b IN {pastecart x y | P x y} <=> P a b`,
  REWRITE_TAC[IN_ELIM_THM; PASTECART_EQ;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MESON_TAC[]);;

export_namedthm IN_ELIM_PASTECART_THM "IN_ELIM_PASTECART_THM";;

(* ------------------------------------------------------------------------- *)
(* Variant of product types using pasting of vectors.                        *)
(* ------------------------------------------------------------------------- *)

export_theory "prod-types-variant";;

parse_as_infix("PCROSS",(22,"right"));;

let PCROSS = new_definition 
 `s PCROSS t = {pastecart (x:A^M) (y:A^N) | x IN s /\ y IN t}`;;

export_namedthm PCROSS "PCROSS";;

let FORALL_IN_PCROSS = prove 
 (`(!z. z IN s PCROSS t ==> P z) <=>
   (!x y. x IN s /\ y IN t ==> P(pastecart x y))`,
  REWRITE_TAC[PCROSS; FORALL_IN_GSPEC]);;

export_namedthm FORALL_IN_PCROSS "FORALL_IN_PCROSS";;

let EXISTS_IN_PCROSS = prove 
 (`(?z. z IN s PCROSS t /\ P z) <=>
   (?x y. x IN s /\ y IN t /\ P(pastecart x y))`,
  REWRITE_TAC[PCROSS; EXISTS_IN_GSPEC; CONJ_ASSOC]);;

export_namedthm EXISTS_IN_PCROSS "EXISTS_IN_PCROSS";;

let PASTECART_IN_PCROSS = prove 
 (`!s t x y. (pastecart x y) IN (s PCROSS t) <=> x IN s /\ y IN t`,
  REWRITE_TAC[PCROSS; IN_ELIM_PASTECART_THM]);;

export_namedthm PASTECART_IN_PCROSS "PASTECART_IN_PCROSS";;

let PCROSS_EQ_EMPTY = prove 
 (`!s t. s PCROSS t = {} <=> s = {} \/ t = {}`,
  REWRITE_TAC[PCROSS] THEN SET_TAC[]);;

export_namedthm PCROSS_EQ_EMPTY "PCROSS_EQ_EMPTY";;

let PCROSS_EMPTY = prove 
 (`(!s. s PCROSS {} = {}) /\ (!t. {} PCROSS t = {})`,
  REWRITE_TAC[PCROSS_EQ_EMPTY]);;

export_namedthm PCROSS_EMPTY "PCROSS_EMPTY";;

let PCROSS_SING = prove 
 (`!x y:A^N. {x} PCROSS {y} = {pastecart x y}`,
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_SING; PASTECART_IN_PCROSS;
              PASTECART_INJ]);;

export_namedthm PCROSS_SING "PCROSS_SING";;

let SUBSET_PCROSS = prove 
 (`!s t s' t'. s PCROSS t SUBSET s' PCROSS t' <=>
                s = {} \/ t = {} \/ s SUBSET s' /\ t SUBSET t'`,
  SIMP_TAC[PCROSS; EXTENSION; IN_ELIM_PASTECART_THM; SUBSET;
   FORALL_PASTECART; PASTECART_IN_PCROSS; NOT_IN_EMPTY] THEN MESON_TAC[]);;

export_namedthm SUBSET_PCROSS "SUBSET_PCROSS";;

let PCROSS_MONO = prove 
 (`!s t s' t'. s SUBSET s' /\ t SUBSET t' ==> s PCROSS t SUBSET s' PCROSS t'`,
  SIMP_TAC[SUBSET_PCROSS]);;

export_namedthm PCROSS_MONO "PCROSS_MONO";;

let PCROSS_EQ = prove 
 (`!s s':real^M->bool t t':real^N->bool.
        s PCROSS t = s' PCROSS t' <=>
        (s = {} \/ t = {}) /\ (s' = {} \/ t' = {}) \/ s = s' /\ t = t'`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_PCROSS] THEN SET_TAC[]);;

export_namedthm PCROSS_EQ "PCROSS_EQ";;

let UNIV_PCROSS_UNIV = prove 
 (`(:A^M) PCROSS (:A^N) = (:A^(M,N)finite_sum)`,
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV]);;

export_namedthm UNIV_PCROSS_UNIV "UNIV_PCROSS_UNIV";;

let HAS_SIZE_PCROSS = prove 
 (`!(s:A^M->bool) (t:A^N->bool) m n.
        s HAS_SIZE m /\ t HAS_SIZE n ==> (s PCROSS t) HAS_SIZE (m * n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_SIZE_PRODUCT) THEN
  MATCH_MP_TAC EQ_IMP THEN SPEC_TAC(`m * n:num`,`k:num`) THEN
  MATCH_MP_TAC BIJECTIONS_HAS_SIZE_EQ THEN
  EXISTS_TAC `\(x:A^M,y:A^N). pastecart x y` THEN
  EXISTS_TAC `\z:A^(M,N)finite_sum. fstcart z,sndcart z` THEN
  REWRITE_TAC[FORALL_IN_GSPEC; PASTECART_IN_PCROSS] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; PASTECART_FST_SND] THEN
  REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART]);;

export_namedthm HAS_SIZE_PCROSS "HAS_SIZE_PCROSS";;

let FINITE_PCROSS = prove 
 (`!(s:A^M->bool) (t:A^N->bool).
        FINITE s /\ FINITE t ==> FINITE(s PCROSS t)`,
  MESON_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_PCROSS]);;

export_namedthm FINITE_PCROSS "FINITE_PCROSS";;

let FINITE_PCROSS_EQ = prove 
 (`!(s:A^M->bool) (t:A^N->bool).
        FINITE(s PCROSS t) <=> s = {} \/ t = {} \/ FINITE s /\ FINITE t`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`s:A^M->bool = {}`; `t:A^N->bool = {}`] THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; FINITE_EMPTY] THEN
  EQ_TAC THEN SIMP_TAC[FINITE_PCROSS] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THENL
   [EXISTS_TAC `IMAGE fstcart ((s PCROSS t):A^(M,N)finite_sum->bool)`;
    EXISTS_TAC `IMAGE sndcart ((s PCROSS t):A^(M,N)finite_sum->bool)`] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; IN_IMAGE; EXISTS_PASTECART] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

export_namedthm FINITE_PCROSS_EQ "FINITE_PCROSS_EQ";;

let IMAGE_FSTCART_PCROSS = prove 
 (`!s:real^M->bool t:real^N->bool.
        IMAGE fstcart (s PCROSS t) = if t = {} then {} else s`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; IMAGE_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[EXISTS_IN_PCROSS; FSTCART_PASTECART] THEN ASM SET_TAC[]);;

export_namedthm IMAGE_FSTCART_PCROSS "IMAGE_FSTCART_PCROSS";;

let IMAGE_SNDCART_PCROSS = prove 
 (`!s:real^M->bool t:real^N->bool.
        IMAGE sndcart (s PCROSS t) = if s = {} then {} else t`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; IMAGE_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[EXISTS_IN_PCROSS; SNDCART_PASTECART] THEN ASM SET_TAC[]);;

export_namedthm IMAGE_SNDCART_PCROSS "IMAGE_SNDCART_PCROSS";;

let PCROSS_INTER = prove 
 (`(!s t u. s PCROSS (t INTER u) = (s PCROSS t) INTER (s PCROSS u)) /\
   (!s t u. (s INTER t) PCROSS u = (s PCROSS u) INTER (t PCROSS u))`,
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_INTER; PASTECART_IN_PCROSS] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

export_namedthm PCROSS_INTER "PCROSS_INTER";;

let PCROSS_UNION = prove 
 (`(!s t u. s PCROSS (t UNION u) = (s PCROSS t) UNION (s PCROSS u)) /\
   (!s t u. (s UNION t) PCROSS u = (s PCROSS u) UNION (t PCROSS u))`,
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_UNION; PASTECART_IN_PCROSS] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

export_namedthm PCROSS_UNION "PCROSS_UNION";;

let PCROSS_DIFF = prove 
 (`(!s t u. s PCROSS (t DIFF u) = (s PCROSS t) DIFF (s PCROSS u)) /\
   (!s t u. (s DIFF t) PCROSS u = (s PCROSS u) DIFF (t PCROSS u))`,
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_DIFF; PASTECART_IN_PCROSS] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

export_namedthm PCROSS_DIFF "PCROSS_DIFF";;

let INTER_PCROSS = prove 
 (`!s s' t t'.
      (s PCROSS t) INTER (s' PCROSS t') = (s INTER s') PCROSS (t INTER t')`,
  REWRITE_TAC[EXTENSION; IN_INTER; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  CONV_TAC TAUT);;

export_namedthm INTER_PCROSS "INTER_PCROSS";;

let PCROSS_UNIONS_UNIONS,PCROSS_UNIONS = (CONJ_PAIR o prove)
 (`(!f g. (UNIONS f) PCROSS (UNIONS g) =
          UNIONS {s PCROSS t | s IN f /\ t IN g}) /\
   (!s f. s PCROSS (UNIONS f) = UNIONS {s PCROSS t | t IN f}) /\
   (!f t. (UNIONS f) PCROSS t = UNIONS {s PCROSS t | s IN f})`,
  REWRITE_TAC[UNIONS_GSPEC; EXTENSION; FORALL_PASTECART; IN_ELIM_THM;
              PASTECART_IN_PCROSS] THEN
  SET_TAC[]);;

export_namedthm PCROSS_UNIONS_UNIONS "PCROSS_UNIONS_UNIONS";;
export_namedthm PCROSS_UNIONS "PCROSS_UNIONS";;

let PCROSS_INTERS_INTERS,PCROSS_INTERS = (CONJ_PAIR o prove)
 (`(!f g. (INTERS f) PCROSS (INTERS g) =
          if f = {} then INTERS {UNIV PCROSS t | t IN g}
          else if g = {} then INTERS {s PCROSS UNIV | s IN f}
          else INTERS {s PCROSS t | s IN f /\ t IN g}) /\
   (!s f. s PCROSS (INTERS f) =
          if f = {} then s PCROSS UNIV else INTERS {s PCROSS t | t IN f}) /\
   (!f t. (INTERS f) PCROSS t =
          if f = {} then UNIV PCROSS t else INTERS {s PCROSS t | s IN f})`,
  REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[INTERS_GSPEC; EXTENSION; FORALL_PASTECART; IN_ELIM_THM;
                  PASTECART_IN_PCROSS; NOT_IN_EMPTY] THEN
  ASM SET_TAC[]);;
  
export_namedthm PCROSS_INTERS_INTERS "PCROSS_INTERS_INTERS";;
export_namedthm PCROSS_INTERS "PCROSS_INTERS";;

let DISJOINT_PCROSS = prove 
 (`!s:A^M->bool t:A^N->bool s' t'.
        DISJOINT (s PCROSS t) (s' PCROSS t') <=>
        DISJOINT s s' \/ DISJOINT t t'`,
  REWRITE_TAC[DISJOINT; INTER_PCROSS; PCROSS_EQ_EMPTY]);;

export_namedthm DISJOINT_PCROSS "DISJOINT_PCROSS";;

export_theory "dummy";;
