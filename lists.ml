

(* ========================================================================= *)
(* Theory of lists, plus characters and strings as lists of characters.      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2014                         *)
(* ========================================================================= *)

needs "ind_types.ml";;

(* ------------------------------------------------------------------------- *)
(* Standard tactic for list induction using MATCH_MP_TAC list_INDUCT         *)
(* ------------------------------------------------------------------------- *)

let LIST_INDUCT_TAC =
  let list_INDUCT = prove
   (`!P:(A)list->bool. P [] /\ (!h t. P t ==> P (CONS h t)) ==> !l. P l`,
    MATCH_ACCEPT_TAC list_INDUCT) in
  MATCH_MP_TAC list_INDUCT THEN
  CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN GEN_TAC THEN DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* Basic definitions.                                                        *)
(* ------------------------------------------------------------------------- *)

export_theory "list-basic-def";;

let HD = new_recursive_definition list_RECURSION
  `HD(CONS (h:A) t) = h`;;

export_namedthm HD "HD";;

let TL = new_recursive_definition list_RECURSION
  `TL(CONS (h:A) t) = t`;;

export_namedthm TL "TL";;

let APPEND = new_recursive_definition list_RECURSION
  `(!l:(A)list. APPEND [] l = l) /\
   (!h t l. APPEND (CONS h t) l = CONS h (APPEND t l))`;;

export_namedthm APPEND "APPEND";;

let REVERSE = new_recursive_definition list_RECURSION
  `(REVERSE [] = []) /\
   (REVERSE (CONS (x:A) l) = APPEND (REVERSE l) [x])`;;

export_namedthm REVERSE "REVERSE";;

let LENGTH = new_recursive_definition list_RECURSION
  `(LENGTH [] = 0) /\
   (!h:A. !t. LENGTH (CONS h t) = SUC (LENGTH t))`;;

export_namedthm LENGTH "LENGTH";;

let MAP = new_recursive_definition list_RECURSION
  `(!f:A->B. MAP f NIL = NIL) /\
   (!f h t. MAP f (CONS h t) = CONS (f h) (MAP f t))`;;

export_namedthm MAP "MAP";;

let LAST = new_recursive_definition list_RECURSION
  `LAST (CONS (h:A) t) = if t = [] then h else LAST t`;;

export_namedthm LAST "LAST";;

let BUTLAST = new_recursive_definition list_RECURSION
 `(BUTLAST [] = []) /\
  (BUTLAST (CONS h t) = if t = [] then [] else CONS h (BUTLAST t))`;;

export_namedthm BUTLAST "BUTLAST";;

let REPLICATE = new_recursive_definition num_RECURSION
  `(REPLICATE 0 x = []) /\
   (REPLICATE (SUC n) x = CONS x (REPLICATE n x))`;;

export_namedthm REPLICATE "REPLICATE";;

let NULL = new_recursive_definition list_RECURSION
  `(NULL [] = T) /\
   (NULL (CONS h t) = F)`;;

export_namedthm NULL "NULL";;

let ALL = new_recursive_definition list_RECURSION
  `(ALL P [] = T) /\
   (ALL P (CONS h t) <=> P h /\ ALL P t)`;;

export_namedthm ALL "ALL";;

let EX = new_recursive_definition list_RECURSION
  `(EX P [] = F) /\
   (EX P (CONS h t) <=> P h \/ EX P t)`;;

export_namedthm EX "EX";;

let ITLIST = new_recursive_definition list_RECURSION
  `(ITLIST f [] b = b) /\
   (ITLIST f (CONS h t) b = f h (ITLIST f t b))`;;

export_namedthm ITLIST "ITLIST";;

let MEM = new_recursive_definition list_RECURSION
  `(MEM x [] <=> F) /\
   (MEM x (CONS h t) <=> (x = h) \/ MEM x t)`;;

export_namedthm MEM "MEM";;

let ALL2_DEF = new_recursive_definition list_RECURSION
  `(ALL2 P [] l2 <=> (l2 = [])) /\
   (ALL2 P (CONS h1 t1) l2 <=>
        if l2 = [] then F
        else P h1 (HD l2) /\ ALL2 P t1 (TL l2))`;;

export_namedthm ALL2_DEF "ALL2_DEF";;

let ALL2 = prove 
 (`(ALL2 P [] [] <=> T) /\
   (ALL2 P (CONS h1 t1) [] <=> F) /\
   (ALL2 P [] (CONS h2 t2) <=> F) /\
   (ALL2 P (CONS h1 t1) (CONS h2 t2) <=> P h1 h2 /\ ALL2 P t1 t2)`,
  REWRITE_TAC[distinctness "list"; ALL2_DEF; HD; TL]);;

export_namedthm ALL2 "ALL2";;

let MAP2_DEF = new_recursive_definition list_RECURSION
  `(MAP2 f [] l = []) /\
   (MAP2 f (CONS h1 t1) l = CONS (f h1 (HD l)) (MAP2 f t1 (TL l)))`;;

export_namedthm MAP2_DEF "MAP2_DEF";;

let MAP2 = prove 
 (`(MAP2 f [] [] = []) /\
   (MAP2 f (CONS h1 t1) (CONS h2 t2) = CONS (f h1 h2) (MAP2 f t1 t2))`,
  REWRITE_TAC[MAP2_DEF; HD; TL]);;

export_namedthm MAP2 "MAP2";;

let EL = new_recursive_definition num_RECURSION
  `(EL 0 l = HD l) /\
   (EL (SUC n) l = EL n (TL l))`;;

export_namedthm EL "EL";;

let FILTER = new_recursive_definition list_RECURSION
  `(FILTER P [] = []) /\
   (FILTER P (CONS h t) = if P h then CONS h (FILTER P t) else FILTER P t)`;;

export_namedthm FILTER "FILTER";;

let ASSOC = new_recursive_definition list_RECURSION
  `ASSOC a (CONS h t) = if FST h = a then SND h else ASSOC a t`;;

export_namedthm ASSOC "ASSOC";;

let ITLIST2_DEF = new_recursive_definition list_RECURSION
  `(ITLIST2 f [] l2 b = b) /\
   (ITLIST2 f (CONS h1 t1) l2 b = f h1 (HD l2) (ITLIST2 f t1 (TL l2) b))`;;

export_namedthm ITLIST2_DEF "ITLIST2_DEF";;

let ITLIST2 = prove 
 (`(ITLIST2 f [] [] b = b) /\
   (ITLIST2 f (CONS h1 t1) (CONS h2 t2) b = f h1 h2 (ITLIST2 f t1 t2 b))`,
  REWRITE_TAC[ITLIST2_DEF; HD; TL]);;

export_namedthm ITLIST2 "ITLIST2";;

let ZIP_DEF = new_recursive_definition list_RECURSION
  `(ZIP [] l2 = []) /\
   (ZIP (CONS h1 t1) l2 = CONS (h1,HD l2) (ZIP t1 (TL l2)))`;;

export_namedthm ZIP_DEF "ZIP_DEF";;

let ZIP = prove 
 (`(ZIP [] [] = []) /\
   (ZIP (CONS h1 t1) (CONS h2 t2) = CONS (h1,h2) (ZIP t1 t2))`,
  REWRITE_TAC[ZIP_DEF; HD; TL]);;

export_namedthm ZIP "ZIP";;

let ALLPAIRS = new_recursive_definition list_RECURSION
  `(ALLPAIRS f [] l <=> T) /\
   (ALLPAIRS f (CONS h t) l <=> ALL (f h) l /\ ALLPAIRS f t l)`;;

export_namedthm ALLPAIRS "ALLPAIRS";;

let PAIRWISE = new_recursive_definition list_RECURSION
  `(PAIRWISE (r:A->A->bool) [] <=> T) /\
   (PAIRWISE (r:A->A->bool) (CONS h t) <=> ALL (r h) t /\ PAIRWISE r t)`;;

export_namedthm PAIRWISE "PAIRWISE";;

let list_of_seq = new_recursive_definition num_RECURSION
 `list_of_seq (s:num->A) 0 = [] /\
  list_of_seq s (SUC n) = APPEND (list_of_seq s n) [s n]`;;

export_namedthm list_of_seq "list_of_seq";;

(* ------------------------------------------------------------------------- *)
(* Various trivial theorems.                                                 *)
(* ------------------------------------------------------------------------- *)

export_theory "list-thm";;

let NOT_CONS_NIL = prove 
 (`!(h:A) t. ~(CONS h t = [])`,
  REWRITE_TAC[distinctness "list"]);;

export_namedthm NOT_CONS_NIL "NOT_CONS_NIL";;

let LAST_CLAUSES = prove 
 (`(LAST [h:A] = h) /\
   (LAST (CONS h (CONS k t)) = LAST (CONS k t))`,
  REWRITE_TAC[LAST; NOT_CONS_NIL]);;

export_namedthm LAST_CLAUSES "LAST_CLAUSES";;

export_theory "list-append";;

let APPEND_NIL = prove 
 (`!l:A list. APPEND l [] = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]);;

export_namedthm APPEND_NIL "APPEND_NIL";;

let APPEND_ASSOC = prove 
 (`!(l:A list) m n. APPEND l (APPEND m n) = APPEND (APPEND l m) n`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]);;

export_namedthm APPEND_ASSOC "APPEND_ASSOC";;

export_theory "list-reverse";;

let REVERSE_APPEND = prove 
 (`!(l:A list) m. REVERSE (APPEND l m) = APPEND (REVERSE m) (REVERSE l)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; REVERSE; APPEND_NIL; APPEND_ASSOC]);;

export_namedthm REVERSE_APPEND "REVERSE_APPEND";;

let REVERSE_REVERSE = prove 
 (`!l:A list. REVERSE(REVERSE l) = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE; REVERSE_APPEND; APPEND]);;

export_namedthm REVERSE_REVERSE "REVERSE_REVERSE";;

let REVERSE_EQ_EMPTY = prove 
 (`!l:A list. REVERSE l = [] <=> l = []`,
  MESON_TAC[REVERSE_REVERSE; REVERSE]);;

export_namedthm REVERSE_EQ_EMPTY "REVERSE_EQ_EMPTY";;

export_theory "list-misc";;

let CONS_11 = prove 
 (`!(h1:A) h2 t1 t2. (CONS h1 t1 = CONS h2 t2) <=> (h1 = h2) /\ (t1 = t2)`,
  REWRITE_TAC[injectivity "list"]);;

export_namedthm CONS_11 "CONS_11";;

let list_CASES = prove 
 (`!l:(A)list. (l = []) \/ ?h t. l = CONS h t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[CONS_11; NOT_CONS_NIL] THEN
  MESON_TAC[]);;

export_namedthm list_CASES "list_CASES";;

let LIST_EQ = prove 
 (`!l1 l2:A list.
        l1 = l2 <=>
        LENGTH l1 = LENGTH l2 /\ !n. n < LENGTH l2 ==> EL n l1 = EL n l2`,
  REPEAT LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11; LENGTH; CONJUNCT1 LT; NOT_SUC] THEN
  ASM_REWRITE_TAC[SUC_INJ] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [MESON[num_CASES] `(!n. P n) <=> P 0 /\ (!n. P(SUC n))`] THEN
  REWRITE_TAC[EL; HD; TL; LT_0; LT_SUC; CONJ_ACI]);;

export_namedthm LIST_EQ "LIST_EQ";;

export_theory "list-length";;

let LENGTH_APPEND = prove 
 (`!(l:A list) m. LENGTH(APPEND l m) = LENGTH l + LENGTH m`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; LENGTH; ADD_CLAUSES]);;

export_namedthm LENGTH_APPEND "LENGTH_APPEND";;

let MAP_APPEND = prove 
 (`!f:A->B. !l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; APPEND]);;

export_namedthm MAP_APPEND "MAP_APPEND";;

let LENGTH_MAP = prove 
 (`!l. !f:A->B. LENGTH (MAP f l) = LENGTH l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; LENGTH]);;

export_namedthm LENGTH_MAP "LENGTH_MAP";;

let LENGTH_EQ_NIL = prove 
 (`!l:A list. (LENGTH l = 0) <=> (l = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_CONS_NIL; NOT_SUC]);;

export_namedthm LENGTH_EQ_NIL "LENGTH_EQ_NIL";;

let LENGTH_EQ_CONS = prove 
 (`!l n. (LENGTH l = SUC n) <=> ?h t. (l = CONS h t) /\ (LENGTH t = n)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; NOT_CONS_NIL] THEN
  ASM_REWRITE_TAC[SUC_INJ; CONS_11] THEN MESON_TAC[]);;

export_namedthm LENGTH_EQ_CONS "LENGTH_EQ_CONS";;

let LENGTH_REVERSE = prove 
 (`!l:A list. LENGTH(REVERSE l) = LENGTH l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; LENGTH_APPEND; LENGTH] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES]);;

export_namedthm LENGTH_REVERSE "LENGTH_REVERSE";;

export_theory "list-map";;

let MAP_o = prove 
 (`!f:A->B. !g:B->C. !l. MAP (g o f) l = MAP g (MAP f l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; o_THM]);;

export_namedthm MAP_o "MAP_o";;

let MAP_EQ = prove 
 (`!f g l. ALL (\x. f x = g x) l ==> (MAP f l = MAP g l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALL] THEN ASM_MESON_TAC[]);;

export_namedthm MAP_EQ "MAP_EQ";;

export_theory "list-ex-all";;

let ALL_IMP = prove 
 (`!P Q l. (!x. MEM x l /\ P x ==> Q x) /\ ALL P l ==> ALL Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; ALL] THEN ASM_MESON_TAC[]);;

export_namedthm ALL_IMP "ALL_IMP";;

let NOT_EX = prove 
 (`!P l. ~(EX P l) <=> ALL (\x. ~(P x)) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[EX; ALL; DE_MORGAN_THM]);;

export_namedthm NOT_EX "NOT_EX";;

let NOT_ALL = prove 
 (`!P l. ~(ALL P l) <=> EX (\x. ~(P x)) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[EX; ALL; DE_MORGAN_THM]);;

export_namedthm NOT_ALL "NOT_ALL";;

let ALL_MAP = prove 
 (`!P f l. ALL P (MAP f l) <=> ALL (P o f) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; MAP; o_THM]);;

export_namedthm ALL_MAP "ALL_MAP";;

let ALL_EQ = prove 
 (`!l. ALL R l /\ (!x. R x ==> (P x <=> Q x))
       ==> (ALL P l <=> ALL Q l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN
  STRIP_TAC THEN BINOP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

export_namedthm ALL_EQ "ALL_EQ";;

let ALL_T = prove 
 (`!l. ALL (\x. T) l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL]);;

export_namedthm ALL_T "ALL_T";;

let MAP_EQ_ALL2 = prove 
 (`!l m. ALL2 (\x y. f x = f y) l m ==> (MAP f l = MAP f m)`,
  REPEAT LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ALL2; CONS_11] THEN
  ASM_MESON_TAC[]);;

export_namedthm MAP_EQ_ALL2 "MAP_EQ_ALL2";;

let ALL2_MAP = prove 
 (`!P f l. ALL2 P (MAP f l) l <=> ALL (\a. P (f a) a) l`,
  GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; MAP; ALL]);;

export_namedthm ALL2_MAP "ALL2_MAP";;

let MAP_EQ_DEGEN = prove 
 (`!l f. ALL (\x. f(x) = x) l ==> (MAP f l = l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; CONS_11] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

export_namedthm MAP_EQ_DEGEN "MAP_EQ_DEGEN";;

let ALL2_AND_RIGHT = prove 
 (`!l m P Q. ALL2 (\x y. P x /\ Q x y) l m <=> ALL P l /\ ALL2 Q l m`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; ALL2] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; ALL2] THEN
  REWRITE_TAC[CONJ_ACI]);;

export_namedthm ALL2_AND_RIGHT "ALL2_AND_RIGHT";;

let ITLIST_APPEND = prove 
 (`!f a l1 l2. ITLIST f (APPEND l1 l2) a = ITLIST f l1 (ITLIST f l2 a)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; APPEND]);;

export_namedthm ITLIST_APPEND "ITLIST_APPEND";;

let ITLIST_EXTRA = prove 
 (`!l. ITLIST f (APPEND l [a]) b = ITLIST f l (f a b)`,
  REWRITE_TAC[ITLIST_APPEND; ITLIST]);;

export_namedthm ITLIST_EXTRA "ITLIST_EXTRA";;

let ALL_MP = prove 
 (`!P Q l. ALL (\x. P x ==> Q x) l /\ ALL P l ==> ALL Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;

export_namedthm ALL_MP "ALL_MP";;

let AND_ALL = prove 
 (`!l. ALL P l /\ ALL Q l <=> ALL (\x. P x /\ Q x) l`,
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; CONJ_ACI]);;

export_namedthm AND_ALL "AND_ALL";;

let EX_IMP = prove 
 (`!P Q l. (!x. MEM x l /\ P x ==> Q x) /\ EX P l ==> EX Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; EX] THEN ASM_MESON_TAC[]);;

export_namedthm EX_IMP "EX_IMP";;

let ALL_MEM = prove 
 (`!P l. (!x. MEM x l ==> P x) <=> ALL P l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MEM] THEN
  ASM_MESON_TAC[]);;

export_namedthm ALL_MEM "ALL_MEM";;

export_theory "list-replicate";;

let LENGTH_REPLICATE = prove 
 (`!n x. LENGTH(REPLICATE n x) = n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; REPLICATE]);;

export_namedthm LENGTH_REPLICATE "LENGTH_REPLICATE";;

let MEM_REPLICATE = prove 
 (`!n x y:A. MEM x (REPLICATE n y) <=> x = y /\ ~(n = 0)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; REPLICATE; NOT_SUC] THEN
  MESON_TAC[]);;

export_namedthm MEM_REPLICATE "MEM_REPLICATE";;

export_theory "list-thm";;

let EX_MAP = prove 
 (`!P f l. EX P (MAP f l) <=> EX (P o f) l`,
  GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; EX; o_THM]);;

export_namedthm EX_MAP "EX_MAP";;

let EXISTS_EX = prove 
 (`!P l. (?x. EX (P x) l) <=> EX (\s. ?x. P x s) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX] THEN
  ASM_MESON_TAC[]);;

export_namedthm EXISTS_EX "EXISTS_EX";;

let FORALL_ALL = prove 
 (`!P l. (!x. ALL (P x) l) <=> ALL (\s. !x. P x s) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL] THEN
  ASM_MESON_TAC[]);;

export_namedthm FORALL_ALL "FORALL_ALL";;

export_theory "list-mem";;

let MEM_APPEND = prove 
 (`!x l1 l2. MEM x (APPEND l1 l2) <=> MEM x l1 \/ MEM x l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; APPEND; DISJ_ACI]);;

export_namedthm MEM_APPEND "MEM_APPEND";;

let MEM_MAP = prove 
 (`!f y l. MEM y (MAP f l) <=> ?x. MEM x l /\ (y = f x)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MEM; MAP] THEN MESON_TAC[]);;

export_namedthm MEM_MAP "MEM_MAP";;

export_theory "list-filter";;

let FILTER_APPEND = prove 
 (`!P l1 l2. FILTER P (APPEND l1 l2) = APPEND (FILTER P l1) (FILTER P l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; APPEND] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND]);;

export_namedthm FILTER_APPEND "FILTER_APPEND";;

let FILTER_MAP = prove 
 (`!P f l. FILTER P (MAP f l) = MAP f (FILTER (P o f) l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; FILTER; o_THM] THEN COND_CASES_TAC THEN
  REWRITE_TAC[MAP]);;

export_namedthm FILTER_MAP "FILTER_MAP";;

let MEM_FILTER = prove 
 (`!P l x. MEM x (FILTER P l) <=> P x /\ MEM x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; FILTER] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[]);;

export_namedthm MEM_FILTER "MEM_FILTER";;

let EX_MEM = prove 
 (`!P l. (?x. P x /\ MEM x l) <=> EX P l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX; MEM] THEN
  ASM_MESON_TAC[]);;

export_namedthm EX_MEM "EX_MEM";;

export_theory "list-zip";;

let MAP_FST_ZIP = prove 
 (`!l1 l2. (LENGTH l1 = LENGTH l2) ==> (MAP FST (ZIP l1 l2) = l1)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; SUC_INJ; MAP; FST; ZIP; NOT_SUC]);;

export_namedthm MAP_FST_ZIP "MAP_FST_ZIP";;

let MAP_SND_ZIP = prove 
 (`!l1 l2. (LENGTH l1 = LENGTH l2) ==> (MAP SND (ZIP l1 l2) = l2)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; SUC_INJ; MAP; FST; ZIP; NOT_SUC]);;

export_namedthm MAP_SND_ZIP "MAP_SND_ZIP";;

let LENGTH_ZIP = prove 
 (`!l1 l2. LENGTH l1 = LENGTH l2 ==> LENGTH(ZIP l1 l2) = LENGTH l2`,
  REPEAT(LIST_INDUCT_TAC ORELSE GEN_TAC) THEN
  ASM_SIMP_TAC[LENGTH; NOT_SUC; ZIP; SUC_INJ]);;

export_namedthm LENGTH_ZIP "LENGTH_ZIP";;

export_theory "list-thm";;

let MEM_ASSOC = prove 
 (`!l x. MEM (x,ASSOC x l) l <=> MEM x (MAP FST l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; MAP; ASSOC] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PAIR; FST]);;

export_namedthm MEM_ASSOC "MEM_ASSOC";;

let ALL_APPEND = prove 
 (`!P l1 l2. ALL P (APPEND l1 l2) <=> ALL P l1 /\ ALL P l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; APPEND; GSYM CONJ_ASSOC]);;

export_namedthm ALL_APPEND "ALL_APPEND";;

export_theory "list-el";;

let MEM_EL = prove 
 (`!l n. n < LENGTH l ==> MEM (EL n l) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; CONJUNCT1 LT; LENGTH] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[EL; HD; LT_SUC; TL]);;

export_namedthm MEM_EL "MEM_EL";;

let MEM_EXISTS_EL = prove 
 (`!l x. MEM x l <=> ?i. i < LENGTH l /\ x = EL i l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; EL; MEM; CONJUNCT1 LT] THEN
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV
   [MESON[num_CASES] `(?i. P i) <=> P 0 \/ (?i. P(SUC i))`] THEN
  REWRITE_TAC[LT_SUC; LT_0; EL; HD; TL]);;

export_namedthm MEM_EXISTS_EL "MEM_EXISTS_EL";;

let ALL_EL = prove 
 (`!P l. (!i. i < LENGTH l ==> P (EL i l)) <=> ALL P l`,
  REWRITE_TAC[GSYM ALL_MEM; MEM_EXISTS_EL] THEN MESON_TAC[]);;

export_namedthm ALL_EL "ALL_EL";;

export_theory "list-all";;

let ALL2_MAP2 = prove 
 (`!l m. ALL2 P (MAP f l) (MAP g m) = ALL2 (\x y. P (f x) (g y)) l m`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; MAP]);;

export_namedthm ALL2_MAP2 "ALL2_MAP2";;

let AND_ALL2 = prove 
 (`!P Q l m. ALL2 P l m /\ ALL2 Q l m <=> ALL2 (\x y. P x y /\ Q x y) l m`,
  GEN_TAC THEN GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2] THEN
  REWRITE_TAC[CONJ_ACI]);;

export_namedthm AND_ALL2 "AND_ALL2";;

let ALLPAIRS_SYM = prove 
 (`!P l m. ALLPAIRS P l m <=> ALLPAIRS (\x y. P y x) m l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALLPAIRS] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALLPAIRS; ALL] THEN
  ASM_MESON_TAC[]);;

export_namedthm ALLPAIRS_SYM "ALLPAIRS_SYM";;

let ALLPAIRS_MEM = prove 
 (`!P l m. (!x y. MEM x l /\ MEM y m ==> P x y) <=> ALLPAIRS P l m`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALLPAIRS; GSYM ALL_MEM; MEM] THEN
  ASM_MESON_TAC[]);;

export_namedthm ALLPAIRS_MEM "ALLPAIRS_MEM";;

let ALLPAIRS_MAP = prove 
 (`!P l m. ALLPAIRS P (MAP f l) (MAP g m) <=>
           ALLPAIRS (\x y. P (f x) (g y)) l m`,
  REWRITE_TAC[GSYM ALLPAIRS_MEM; MEM_MAP] THEN MESON_TAC[]);;

export_namedthm ALLPAIRS_MAP "ALLPAIRS_MAP";;

let ALLPAIRS_EQ = prove 
 (`!l m. !P Q. ALL P (l:A list) /\ ALL Q (m:B list) /\
               (!p q. P p /\ Q q ==> (R p q <=> R' p q))
               ==> (ALLPAIRS R l m <=> ALLPAIRS R' l m)`,
  REWRITE_TAC[GSYM ALLPAIRS_MEM; GSYM ALL_MEM] THEN MESON_TAC[]);;

export_namedthm ALLPAIRS_EQ "ALLPAIRS_EQ";;

let ALL2_ALL = prove 
 (`!P l. ALL2 P l l <=> ALL (\x. P x x) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; ALL]);;

export_namedthm ALL2_ALL "ALL2_ALL";;

export_theory "list-append";;

let APPEND_EQ_NIL = prove 
 (`!l m. (APPEND l m = []) <=> (l = []) /\ (m = [])`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_APPEND; ADD_EQ_0]);;

export_namedthm APPEND_EQ_NIL "APPEND_EQ_NIL";;

let APPEND_LCANCEL = prove 
 (`!l1 l2 l3:A list. APPEND l1 l2 = APPEND l1 l3 <=> l2 = l3`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; CONS_11]);;

export_namedthm APPEND_LCANCEL "APPEND_LCANCEL";;

let APPEND_RCANCEL = prove 
 (`!l1 l2 l3:A list. APPEND l1 l3 = APPEND l2 l3 <=> l1 = l2`,
  ONCE_REWRITE_TAC[MESON[REVERSE_REVERSE]
   `l = l' <=> REVERSE l = REVERSE l'`] THEN
  REWRITE_TAC[REVERSE_APPEND; APPEND_LCANCEL]);;

export_namedthm APPEND_RCANCEL "APPEND_RCANCEL";;

export_theory "list-map";;

let LENGTH_MAP2 = prove 
 (`!f l m. LENGTH l = LENGTH m ==> LENGTH(MAP2 f l m) = LENGTH m`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; NOT_CONS_NIL; NOT_SUC; MAP2; SUC_INJ]);;

export_namedthm LENGTH_MAP2 "LENGTH_MAP2";;

let EL_MAP2 = prove 
 (`!f l m k. k < LENGTH l /\ k < LENGTH m
             ==> EL k (MAP2 f l m) = f (EL k l) (EL k m)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[LENGTH; MAP2; EL; HD; TL; LT_SUC]);;

export_namedthm EL_MAP2 "EL_MAP2";;

let MAP_EQ_NIL  = prove 
 (`!f l. MAP f l = [] <=> l = []`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; NOT_CONS_NIL]);;

export_namedthm MAP_EQ_NIL  "MAP_EQ_NIL";;

let INJECTIVE_MAP = prove 
 (`!f:A->B. (!l m. MAP f l = MAP f m ==> l = m) <=>
            (!x y. f x = f y ==> x = y)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`[x:A]`; `[y:A]`]) THEN
    ASM_REWRITE_TAC[MAP; CONS_11];
    REPEAT LIST_INDUCT_TAC THEN ASM_SIMP_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
    ASM_MESON_TAC[]]);;

export_namedthm INJECTIVE_MAP "INJECTIVE_MAP";;

let SURJECTIVE_MAP = prove 
 (`!f:A->B. (!m. ?l. MAP f l = m) <=> (!y. ?x. f x = y)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `y:B` THEN FIRST_X_ASSUM(MP_TAC o SPEC `[y:B]`) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; CONS_11; NOT_CONS_NIL; MAP_EQ_NIL];
    MATCH_MP_TAC list_INDUCT] THEN
  ASM_MESON_TAC[MAP]);;

export_namedthm SURJECTIVE_MAP "SURJECTIVE_MAP";;

let MAP_ID = prove 
 (`!l. MAP (\x. x) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP]);;

export_namedthm MAP_ID "MAP_ID";;

let MAP_I = prove 
 (`MAP I = I`,
  REWRITE_TAC[FUN_EQ_THM; I_DEF; MAP_ID]);;

export_namedthm MAP_I "MAP_I";;

export_theory "list-last";;

let BUTLAST_APPEND = prove 
 (`!l m:A list. BUTLAST(APPEND l m) =
                if m = [] then BUTLAST l else APPEND l (BUTLAST m)`,
  SIMP_TAC[COND_RAND; APPEND_NIL; MESON[]
   `(if p then T else q) <=> ~p ==> q`] THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[APPEND; BUTLAST; APPEND_EQ_NIL]);;

export_namedthm BUTLAST_APPEND "BUTLAST_APPEND";;

let APPEND_BUTLAST_LAST = prove 
 (`!l. ~(l = []) ==> APPEND (BUTLAST l) [LAST l] = l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LAST; BUTLAST; NOT_CONS_NIL] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[APPEND]);;

export_namedthm APPEND_BUTLAST_LAST "APPEND_BUTLAST_LAST";;

let LAST_APPEND = prove 
 (`!p q. LAST(APPEND p q) = if q = [] then LAST p else LAST q`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; LAST; APPEND_EQ_NIL] THEN
  MESON_TAC[]);;

export_namedthm LAST_APPEND "LAST_APPEND";;

let LENGTH_TL = prove 
 (`!l. ~(l = []) ==> LENGTH(TL l) = LENGTH l - 1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; TL; ARITH; SUC_SUB1]);;

export_namedthm LENGTH_TL "LENGTH_TL";;

let LAST_REVERSE = prove 
 (`!l:A list. ~(l = []) ==> LAST(REVERSE l) = HD l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[HD; REVERSE; LAST; LAST_APPEND; NOT_CONS_NIL]);;

export_namedthm LAST_REVERSE "LAST_REVERSE";;

let HD_REVERSE = prove 
 (`!l:A list. ~(l = []) ==> HD(REVERSE l) = LAST l`,
  MESON_TAC[LAST_REVERSE; REVERSE_REVERSE; REVERSE_EQ_EMPTY]);;

export_namedthm HD_REVERSE "HD_REVERSE";;

let EL_APPEND = prove 
 (`!k l m. EL k (APPEND l m) = if k < LENGTH l then EL k l
                               else EL (k - LENGTH l) m`,
  INDUCT_TAC THEN REWRITE_TAC[EL] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[HD; APPEND; LENGTH; SUB_0; EL; LT_0; CONJUNCT1 LT] THEN
  ASM_REWRITE_TAC[TL; LT_SUC; SUB_SUC]);;

export_namedthm EL_APPEND "EL_APPEND";;

let EL_TL = prove 
 (`!n. EL n (TL l) = EL (n + 1) l`,
  REWRITE_TAC[GSYM ADD1; EL]);;

export_namedthm EL_TL "EL_TL";;

let EL_CONS = prove 
 (`!n h t. EL n (CONS h t) = if n = 0 then h else EL (n - 1) t`,
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; NOT_SUC; SUC_SUB1]);;

export_namedthm EL_CONS "EL_CONS";;

let LAST_EL = prove 
 (`!l. ~(l = []) ==> LAST l = EL (LENGTH l - 1) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LAST; LENGTH; SUC_SUB1] THEN
  DISCH_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[LENGTH; EL; HD; EL_CONS; LENGTH_EQ_NIL]);;

export_namedthm LAST_EL "LAST_EL";;

let HD_APPEND = prove 
 (`!l m:A list. HD(APPEND l m) = if l = [] then HD m else HD l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HD; APPEND; NOT_CONS_NIL]);;

export_namedthm HD_APPEND "HD_APPEND";;

let CONS_HD_TL = prove 
 (`!l. ~(l = []) ==> l = CONS (HD l) (TL l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL;HD;TL]);;

export_namedthm CONS_HD_TL "CONS_HD_TL";;

export_theory "list-thm";;

let EL_MAP = prove 
 (`!f n l. n < LENGTH l ==> EL n (MAP f l) = f(EL n l)`,
  GEN_TAC THEN INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; CONJUNCT1 LT; LT_0; EL; HD; TL; MAP; LT_SUC]);;

export_namedthm EL_MAP "EL_MAP";;

let MAP_REVERSE = prove 
 (`!f l. REVERSE(MAP f l) = MAP f (REVERSE l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; REVERSE; MAP_APPEND]);;

export_namedthm MAP_REVERSE "MAP_REVERSE";;

let ALL_FILTER = prove 
 (`!P Q l:A list. ALL P (FILTER Q l) <=> ALL (\x. Q x ==> P x) l`,
  GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; FILTER] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL]);;

export_namedthm ALL_FILTER "ALL_FILTER";;

let APPEND_SING = prove 
 (`!h t. APPEND [h] t = CONS h t`,
  REWRITE_TAC[APPEND]);;

export_namedthm APPEND_SING "APPEND_SING";;

let MEM_APPEND_DECOMPOSE_LEFT = prove 
 (`!x:A l. MEM x l <=> ?l1 l2. ~(MEM x l1) /\ l = APPEND l1 (CONS x l2)`,
  REWRITE_TAC[TAUT `(p <=> q) <=> (p ==> q) /\ (q ==> p)`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; MEM_APPEND; MEM] THEN X_GEN_TAC `x:A` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[MEM] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `l:A list`] THEN
  ASM_CASES_TAC `x:A = y` THEN ASM_MESON_TAC[MEM; APPEND]);;

export_namedthm MEM_APPEND_DECOMPOSE_LEFT "MEM_APPEND_DECOMPOSE_LEFT";;

let MEM_APPEND_DECOMPOSE = prove 
 (`!x:A l. MEM x l <=> ?l1 l2. l = APPEND l1 (CONS x l2)`,
  REWRITE_TAC[TAUT `(p <=> q) <=> (p ==> q) /\ (q ==> p)`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; MEM_APPEND; MEM] THEN
  ONCE_REWRITE_TAC[MEM_APPEND_DECOMPOSE_LEFT] THEN MESON_TAC[]);;

export_namedthm MEM_APPEND_DECOMPOSE "MEM_APPEND_DECOMPOSE";;

export_theory "list-pairwise";;

let PAIRWISE_APPEND = prove 
 (`!R:A->A->bool l m.
        PAIRWISE R (APPEND l m) <=>
        PAIRWISE R l /\ PAIRWISE R m /\ (!x y. MEM x l /\ MEM y m ==> R x y)`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[APPEND; PAIRWISE; MEM; ALL_APPEND; GSYM ALL_MEM] THEN
  MESON_TAC[]);;

export_namedthm PAIRWISE_APPEND "PAIRWISE_APPEND";;

let PAIRWISE_MAP = prove 
 (`!R f:A->B l.
        PAIRWISE R (MAP f l) <=> PAIRWISE (\x y. R (f x) (f y)) l`,
  GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[PAIRWISE; MAP; ALL_MAP; o_DEF]);;

export_namedthm PAIRWISE_MAP "PAIRWISE_MAP";;

let PAIRWISE_IMPLIES = prove 
 (`!R:A->A->bool R' l.
        PAIRWISE R l /\ (!x y. MEM x l /\ MEM y l /\ R x y ==> R' x y)
        ==> PAIRWISE R' l`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[PAIRWISE; GSYM ALL_MEM; MEM] THEN MESON_TAC[]);;

export_namedthm PAIRWISE_IMPLIES "PAIRWISE_IMPLIES";;

let PAIRWISE_TRANSITIVE = prove 
 (`!R x y:A l.
      (!x y z. R x y /\ R y z ==> R x z)
      ==> (PAIRWISE R (CONS x (CONS y l)) <=> R x y /\ PAIRWISE R (CONS y l))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[PAIRWISE; ALL; GSYM CONJ_ASSOC;
              TAUT `(p /\ q /\ r /\ s <=> p /\ r /\ s) <=>
                    p /\ s ==> r ==> q`] THEN
  STRIP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
  ASM_MESON_TAC[]);;

export_namedthm PAIRWISE_TRANSITIVE "PAIRWISE_TRANSITIVE";;

export_theory "list-seq";;

let LENGTH_LIST_OF_SEQ = prove 
 (`!s:num->A n. LENGTH(list_of_seq s n) = n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_of_seq; LENGTH; LENGTH_APPEND; ADD_CLAUSES]);;

export_namedthm LENGTH_LIST_OF_SEQ "LENGTH_LIST_OF_SEQ";;

let EL_LIST_OF_SEQ = prove 
 (`!s:num->A m n. m < n ==> EL m (list_of_seq s n) = s m`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; LT; EL_APPEND; LENGTH_LIST_OF_SEQ] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUB_REFL; EL; HD; LT_REFL]);;

export_namedthm EL_LIST_OF_SEQ "EL_LIST_OF_SEQ";;

let LIST_OF_SEQ_EQ_NIL = prove 
 (`!s:num->A n. list_of_seq s n = [] <=> n = 0`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_LIST_OF_SEQ; LENGTH]);;

export_namedthm LIST_OF_SEQ_EQ_NIL "LIST_OF_SEQ_EQ_NIL";;

(* ------------------------------------------------------------------------- *)
(* Syntax.                                                                   *)
(* ------------------------------------------------------------------------- *)

let mk_cons h t =
  try let cons = mk_const("CONS",[type_of h,aty]) in
      mk_comb(mk_comb(cons,h),t)
  with Failure _ -> failwith "mk_cons";;

let mk_list (tms,ty) =
  try let nil = mk_const("NIL",[ty,aty]) in
      if tms = [] then nil else
      let cons = mk_const("CONS",[ty,aty]) in
      itlist (mk_binop cons) tms nil
  with Failure _ -> failwith "mk_list";;

let mk_flist tms =
  try mk_list(tms,type_of(hd tms))
  with Failure _ -> failwith "mk_flist";;

(* ------------------------------------------------------------------------- *)
(* Extra monotonicity theorems for inductive definitions.                    *)
(* ------------------------------------------------------------------------- *)

let MONO_ALL = prove 
 (`(!x:A. P x ==> Q x) ==> ALL P l ==> ALL Q l`,
  DISCH_TAC THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;

export_namedthm MONO_ALL "MONO_ALL";;

let MONO_ALL2 = prove 
 (`(!x y. (P:A->B->bool) x y ==> Q x y) ==> ALL2 P l l' ==> ALL2 Q l l'`,
  DISCH_TAC THEN
  SPEC_TAC(`l':B list`,`l':B list`) THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2_DEF] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

export_namedthm MONO_ALL2 "MONO_ALL2";;

monotonicity_theorems := [MONO_ALL; MONO_ALL2] @ !monotonicity_theorems;;

(* ------------------------------------------------------------------------- *)
(* Apply a conversion down a list.                                           *)
(* ------------------------------------------------------------------------- *)

let rec LIST_CONV conv tm =
  if is_cons tm then
    COMB2_CONV (RAND_CONV conv) (LIST_CONV conv) tm
  else if fst(dest_const tm) = "NIL" then REFL tm
  else failwith "LIST_CONV";;

(* ------------------------------------------------------------------------- *)
(* Type of characters, like the HOL88 "ascii" type, with syntax              *)
(* constructors and equality conversions for chars and strings.              *)
(* ------------------------------------------------------------------------- *)

let char_INDUCT,char_RECURSION = define_type
 "char = ASCII bool bool bool bool bool bool bool bool";;

export_namedthm char_INDUCT "char_INDUCT";;
export_namedthm char_RECURSION "char_RECURSION";;

new_type_abbrev("string",`:char list`);;

let dest_char,mk_char,dest_string,mk_string,CHAR_EQ_CONV,STRING_EQ_CONV =
  let bool_of_term t =
    match t with
      Const("T",_) -> true
    | Const("F",_) -> false
    | _ -> failwith "bool_of_term" in
  let code_of_term t =
    let f,tms = strip_comb t in
    if not(is_const f && fst(dest_const f) = "ASCII")
       || not(length tms = 8) then failwith "code_of_term"
    else
       itlist (fun b f -> if b then 1 + 2 * f else 2 * f)
              (map bool_of_term (rev tms)) 0 in
  let char_of_term = Char.chr o code_of_term in
  let dest_string tm =
    try let tms = dest_list tm in
        if fst(dest_type(hd(snd(dest_type(type_of tm))))) <> "char"
        then fail() else
        let ccs = map (String.make 1 o char_of_term) tms in
        String.escaped (implode ccs)
    with Failure _ -> failwith "dest_string" in
  let mk_bool b =
    let true_tm,false_tm = `T`,`F` in
    if b then true_tm else false_tm in
  let mk_code =
    let ascii_tm = `ASCII` in
    let mk_code c =
      let lis = map (fun i -> mk_bool((c / (1 lsl i)) mod 2 = 1)) (0--7) in
      itlist (fun x y -> mk_comb(y,x)) lis ascii_tm in
    let codes = Array.map mk_code (Array.of_list (0--255)) in
    fun c -> Array.get codes c in
  let mk_char = mk_code o Char.code in
  let mk_string s =
    let ns = map (fun i -> Char.code(String.get s i))
                 (0--(String.length s - 1)) in
    mk_list(map mk_code ns,`:char`) in
  let CHAR_DISTINCTNESS =
    let avars,bvars,cvars =
     [`a0:bool`;`a1:bool`;`a2:bool`;`a3:bool`;`a4:bool`;`a5:bool`;`a6:bool`],
     [`b1:bool`;`b2:bool`;`b3:bool`;`b4:bool`;`b5:bool`;`b6:bool`;`b7:bool`],
     [`c1:bool`;`c2:bool`;`c3:bool`;`c4:bool`;`c5:bool`;`c6:bool`;`c7:bool`] in
    let ASCII_NEQS_FT = (map EQF_INTRO o CONJUNCTS o prove)
     (`~(ASCII F b1 b2 b3 b4 b5 b6 b7 = ASCII T c1 c2 c3 c4 c5 c6 c7) /\
       ~(ASCII a0 F b2 b3 b4 b5 b6 b7 = ASCII a0 T c2 c3 c4 c5 c6 c7) /\
       ~(ASCII a0 a1 F b3 b4 b5 b6 b7 = ASCII a0 a1 T c3 c4 c5 c6 c7) /\
       ~(ASCII a0 a1 a2 F b4 b5 b6 b7 = ASCII a0 a1 a2 T c4 c5 c6 c7) /\
       ~(ASCII a0 a1 a2 a3 F b5 b6 b7 = ASCII a0 a1 a2 a3 T c5 c6 c7) /\
       ~(ASCII a0 a1 a2 a3 a4 F b6 b7 = ASCII a0 a1 a2 a3 a4 T c6 c7) /\
       ~(ASCII a0 a1 a2 a3 a4 a5 F b7 = ASCII a0 a1 a2 a3 a4 a5 T c7) /\
       ~(ASCII a0 a1 a2 a3 a4 a5 a6 F = ASCII a0 a1 a2 a3 a4 a5 a6 T)`,
      REWRITE_TAC[injectivity "char"]) in
    let ASCII_NEQS_TF =
      let ilist = zip bvars cvars @ zip cvars bvars in
      let f = EQF_INTRO o INST ilist o GSYM o EQF_ELIM in
      map f ASCII_NEQS_FT in
    let rec prefix n l =
      if n = 0 then [] else
      match l with
        h::t -> h :: prefix (n-1) t
      | _ -> l in
    let rec findneq n prefix a b =
      match a,b with
        b1::a, b2::b -> if b1 <> b2 then n,rev prefix,bool_of_term b2,a,b else
                        findneq (n+1) (b1 :: prefix) a b
      | _, _ -> fail() in
    fun c1 c2 ->
      let _,a = strip_comb c1
      and _,b = strip_comb c2 in
      let n,p,b,s1,s2 = findneq 0 [] a b in
      let ss1 = funpow n tl bvars
      and ss2 = funpow n tl cvars in
      let pp = prefix n avars in
      let pth = if b then ASCII_NEQS_FT else ASCII_NEQS_TF in
      INST (zip p pp @ zip s1 ss1 @ zip s2 ss2) (el n pth) in
  let STRING_DISTINCTNESS =
    let xtm,xstm = `x:char`,`xs:string`
    and ytm,ystm = `y:char`,`ys:string`
    and niltm = `[]:string` in
    let NIL_EQ_THM = EQT_INTRO (REFL niltm)
    and CONS_EQ_THM,CONS_NEQ_THM = (CONJ_PAIR o prove)
     (`(CONS x xs:string = CONS x ys <=> xs = ys) /\
       ((x = y <=> F) ==> (CONS x xs:string = CONS y ys <=> F))`,
      REWRITE_TAC[CONS_11] THEN MESON_TAC[])
    and NIL_NEQ_CONS,CONS_NEQ_NIL = (CONJ_PAIR o prove)
     (`(NIL:string = CONS x xs <=> F) /\
       (CONS x xs:string = NIL <=> F)`,
      REWRITE_TAC[NOT_CONS_NIL]) in
    let rec STRING_DISTINCTNESS s1 s2 =
      if s1 = niltm
      then if s2 = niltm then NIL_EQ_THM
           else let c2,s2 = rand (rator s2),rand s2 in
                INST [c2,xtm;s2,xstm] NIL_NEQ_CONS
      else let c1,s1 = rand (rator s1),rand s1 in
           if s2 = niltm then INST [c1,xtm;s1,xstm] CONS_NEQ_NIL
           else let c2,s2 = rand (rator s2),rand s2 in
           if c1 = c2
           then let th1 = INST [c1,xtm; s1,xstm; s2,ystm] CONS_EQ_THM
                and th2 = STRING_DISTINCTNESS s1 s2 in
                TRANS th1 th2
           else let ilist = [c1,xtm; c2,ytm; s1,xstm; s2,ystm] in
                let itm = INST ilist CONS_NEQ_THM in
                MP itm (CHAR_DISTINCTNESS c1 c2) in
    STRING_DISTINCTNESS in
  let CHAR_EQ_CONV : conv =
    fun tm ->
      let c1,c2 = dest_eq tm in
      if compare c1 c2 = 0 then EQT_INTRO (REFL c1) else
      CHAR_DISTINCTNESS c1 c2
  and STRING_EQ_CONV tm =
    let ltm,rtm = dest_eq tm in
    if compare ltm rtm = 0 then EQT_INTRO (REFL ltm) else
    STRING_DISTINCTNESS ltm rtm in
  char_of_term,mk_char,dest_string,mk_string,CHAR_EQ_CONV,STRING_EQ_CONV;;
