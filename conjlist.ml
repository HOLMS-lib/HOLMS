(* ========================================================================= *)
(* Iterated conjunction of formulae.                                         *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

let CONJLIST = new_recursive_definition list_RECURSION
  `CONJLIST [] = True /\
   (!p X. CONJLIST (CONS p X) = if X = [] then p else p && CONJLIST X)`;;

let CONJLIST_IMP_MEM = prove
 (`!p X. MEM p X ==> [S . H |~ (CONJLIST X --> p)]`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; CONJLIST] THEN
  STRIP_TAC THENL
  [POP_ASSUM (SUBST_ALL_TAC o GSYM) THEN
   COND_CASES_TAC THEN REWRITE_TAC[MLK_imp_refl_th; MLK_and_left_th];
   COND_CASES_TAC THENL [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
   MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `CONJLIST t` THEN CONJ_TAC THENL
   [MATCH_ACCEPT_TAC MLK_and_right_th; ASM_SIMP_TAC[]]]);;

let CONJLIST_MONO = prove
 (`!X Y. (!p. MEM p Y ==> MEM p X) ==> [S . H |~ (CONJLIST X --> CONJLIST Y)]`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; CONJLIST] THENL
  [MESON_TAC[MLK_add_assum; MLK_truth_th]; ALL_TAC] THEN
   COND_CASES_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC[MEM] THEN MESON_TAC[CONJLIST_IMP_MEM];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC MLK_and_intro THEN CONJ_TAC THENL
  [ASM_MESON_TAC[CONJLIST_IMP_MEM];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let CONJLIST_CONS = prove
 (`!p X. [S . H |~ (CONJLIST (CONS p X) <-> p && CONJLIST X)]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJLIST] THEN COND_CASES_TAC THEN
  REWRITE_TAC[MLK_iff_refl_th] THEN POP_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[CONJLIST] THEN ONCE_REWRITE_TAC[MLK_iff_sym] THEN
  MATCH_ACCEPT_TAC MLK_and_rigth_true_th);;

let CONJLIST_IMP = prove
 (`!S H h t. [S . H |~ CONJLIST (CONS h t) --> p] <=>
             [S . H |~ h && CONJLIST t --> p]`,
  REPEAT GEN_TAC THEN EQ_TAC THEN INTRO_TAC "hp" THENL
  [TRANS_TAC MLK_imp_trans `CONJLIST (CONS h t)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MLK_iff_imp2 THEN MATCH_ACCEPT_TAC CONJLIST_CONS;
   TRANS_TAC MLK_imp_trans `h && CONJLIST t` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MLK_iff_imp1 THEN MATCH_ACCEPT_TAC CONJLIST_CONS]);;

let HEAD_TAIL_IMP_CONJLIST = prove
 (`!p h t. [S . H |~ (p --> h)] /\ [S . H |~ (p --> CONJLIST t)]
           ==> [S . H |~ (p --> CONJLIST (CONS h t))]`,
  INTRO_TAC "!p h t; ph pt" THEN REWRITE_TAC[CONJLIST] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[MLK_and_intro]]);;

let IMP_CONJLIST = prove
 (`!p X. [S . H |~ p --> CONJLIST X] <=>
         (!q. MEM q X ==> [S . H |~ (p --> q)])`,
  GEN_TAC THEN SUBGOAL_THEN
    `(!X q. [S . H |~ p --> CONJLIST X] /\ MEM q X
            ==> [S . H |~ p --> q]) /\
     (!X. (!q. MEM q X ==> [S . H |~ p --> q])
     ==> [S . H |~ p --> CONJLIST X])`
    (fun th -> MESON_TAC[th]) THEN
  CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC MLK_imp_trans THEN
   EXISTS_TAC `CONJLIST X` THEN ASM_SIMP_TAC[CONJLIST_IMP_MEM];
   ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THENL
  [REWRITE_TAC[CONJLIST; MLK_imp_clauses]; ALL_TAC] THEN
  DISCH_TAC THEN  MATCH_MP_TAC HEAD_TAIL_IMP_CONJLIST THEN
  ASM_SIMP_TAC[]);;

let CONJLIST_IMP_SUBLIST = prove
 (`!X Y. Y SUBLIST X ==> [S . H |~ CONJLIST X --> CONJLIST Y]`,
  REWRITE_TAC[SUBLIST; IMP_CONJLIST] THEN MESON_TAC[CONJLIST_IMP_MEM]);;

let CONJLIST_IMP_HEAD = prove
 (`!p X. [S . H |~ CONJLIST (CONS p X) --> p]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONJLIST_IMP_MEM THEN REWRITE_TAC[MEM]);;

let CONJLIST_IMP_TAIL = prove
 (`!p X. [S . H |~ CONJLIST (CONS p X) --> CONJLIST X]`,
  MESON_TAC[CONJLIST_IMP_SUBLIST; TAIL_SUBLIST]);;

let CONJLIST_IMP_CONJLIST = prove
 (`!l m. (!p. MEM p m ==> ?q. MEM q l /\ [S . H |~ (q --> p)])
         ==> [S . H |~ (CONJLIST l --> CONJLIST m)]`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
  [REWRITE_TAC[CONJLIST; MLK_imp_clauses]; ALL_TAC] THEN
  INTRO_TAC "hp" THEN
  MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `h && CONJLIST t` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC MLK_and_intro THEN
   CONJ_TAC THENL
   [HYP_TAC "hp: +" (SPEC `h:form`) THEN
    REWRITE_TAC[MEM] THEN MESON_TAC[CONJLIST_IMP_MEM; MLK_imp_trans];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    INTRO_TAC "!p; p" THEN FIRST_X_ASSUM (MP_TAC o SPEC `p:form`) THEN
    ASM_REWRITE_TAC[MEM]];
   ALL_TAC] THEN
  MESON_TAC[CONJLIST_CONS; MLK_iff_imp2]);;

let CONJLIST_APPEND = prove
 (`!l m. [S . H |~ (CONJLIST (APPEND l m) <-> CONJLIST l && CONJLIST m)]`,
  FIX_TAC "m" THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THENL
  [REWRITE_TAC[CONJLIST] THEN ONCE_REWRITE_TAC[MLK_iff_sym] THEN
   MATCH_ACCEPT_TAC MLK_and_left_true_th;
   ALL_TAC] THEN
  MATCH_MP_TAC MLK_iff_trans THEN
  EXISTS_TAC `h && CONJLIST (APPEND t m)` THEN REWRITE_TAC[CONJLIST_CONS] THEN
  MATCH_MP_TAC MLK_iff_trans THEN
  EXISTS_TAC `h && (CONJLIST t && CONJLIST m)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_and_subst_th THEN ASM_REWRITE_TAC[MLK_iff_refl_th];
   ALL_TAC] THEN
  MATCH_MP_TAC MLK_iff_trans THEN
  EXISTS_TAC `(h && CONJLIST t) && CONJLIST m` THEN CONJ_TAC THENL
  [MESON_TAC[MLK_and_assoc_th; MLK_iff_sym]; ALL_TAC] THEN
  MATCH_MP_TAC MLK_and_subst_th THEN REWRITE_TAC[MLK_iff_refl_th] THEN
  ONCE_REWRITE_TAC[MLK_iff_sym] THEN MATCH_ACCEPT_TAC CONJLIST_CONS);;

let FALSE_NOT_CONJLIST = prove
 (`!X. MEM False X ==> [S . H |~ (Not (CONJLIST X))]`,
  INTRO_TAC "!X; X" THEN REWRITE_TAC[MLK_not_def] THEN
  MATCH_MP_TAC CONJLIST_IMP_MEM THEN POP_ASSUM MATCH_ACCEPT_TAC);;

let CONJLIST_MAP_BOX = prove
 (`!l. [S . H |~ (CONJLIST (MAP (Box) l) <-> Box (CONJLIST l))]`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[CONJLIST; MAP; MLK_iff_refl_th] THEN
   MATCH_MP_TAC MLK_imp_antisym THEN
   SIMP_TAC[MLK_add_assum; MLK_truth_th; MLK_necessitation];
   ALL_TAC] THEN
  REWRITE_TAC[MAP] THEN MATCH_MP_TAC MLK_iff_trans THEN
  EXISTS_TAC `Box h && CONJLIST (MAP (Box) t)` THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC CONJLIST_CONS; ALL_TAC] THEN
  MATCH_MP_TAC MLK_iff_trans THEN
  EXISTS_TAC `Box h && Box (CONJLIST t)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_imp_antisym THEN CONJ_TAC THEN
   MATCH_MP_TAC MLK_and_intro THEN
   ASM_MESON_TAC[MLK_and_left_th; MLK_and_right_th; MLK_iff_imp1;
                 MLK_iff_imp2; MLK_imp_trans];
   ALL_TAC] THEN
  MATCH_MP_TAC MLK_iff_trans THEN EXISTS_TAC `Box (h && CONJLIST t)` THEN
  CONJ_TAC THENL
  [MESON_TAC[MLK_box_and_th; MLK_box_and_inv_th; MLK_imp_antisym];
   ALL_TAC] THEN
  MATCH_MP_TAC MLK_box_iff THEN MATCH_MP_TAC MLK_necessitation THEN
  ONCE_REWRITE_TAC[MLK_iff_sym] THEN MATCH_ACCEPT_TAC CONJLIST_CONS);;

let MODPROVES_DEDUCTION_LEMMA_CONJLIST = prove
 (`!S H K p. [S . H |~ CONJLIST K --> p] <=>
             [S . H UNION set_of_list K |~ p]`,
  FIX_TAC "S p" THEN
  C SUBGOAL_THEN (fun th -> MESON_TAC[th])
    `!K H. [S . H |~ CONJLIST K --> p] <=>
           [S . H UNION set_of_list K |~ p]` THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[CONJLIST; set_of_list; UNION_EMPTY; MLK_imp_clauses];
   ALL_TAC] THEN
  GEN_TAC THEN
  REWRITE_TAC[set_of_list;
              SET_RULE `H UNION h:form INSERT s = h INSERT (H UNION s)`] THEN
  REWRITE_TAC[CONJLIST_IMP; GSYM MLK_imp_imp] THEN
  ONCE_REWRITE_TAC[MODPROVES_DEDUCTION_LEMMA] THEN
  ASM_REWRITE_TAC[SET_RULE
    `h:form INSERT H UNION set_of_list t =
     h INSERT (H UNION set_of_list t)`]);;

let MLK_BOX_CONJLIST = prove
 (`!S X. [S . {} |~ Box (CONJLIST X) <-> CONJLIST (MAP (Box) X)]`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [MLK_iff_sym] THEN
  MATCH_ACCEPT_TAC CONJLIST_MAP_BOX);;

g `!S p X. [S  . {} |~ CONJLIST X --> p]
           ==> [S . {} |~ CONJLIST (MAP (Box) X) --> Box p]`;;
e (REPEAT GEN_TAC THEN STRIP_TAC);;
e (CLAIM_TAC "asd" `[S . {} |~ Box CONJLIST X --> Box p]`);;
 e (MATCH_MP_TAC MLK_imp_box);;
 e (ASM_REWRITE_TAC[]);;
e (MATCH_MP_TAC MLK_imp_trans);;
e (EXISTS_TAC `Box CONJLIST X`);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN
     `[S . {} |~ CONJLIST (MAP (Box) X) <-> Box CONJLIST X]
      ==> [S . {} |~ CONJLIST (MAP (Box) X) --> Box CONJLIST X]`
     (fun(th) -> MATCH_MP_TAC th));;
 e (MESON_TAC[MLK_iff_def]);;
e (REWRITE_TAC[MLK_BOX_CONJLIST; MLK_iff_sym]);;
let MKL_CONJLIST_BOX_IMP_BOX = top_thm();;

g `!S p X. [S . {} |~ (CONJLIST (CONS p X) --> False) <->
            (p && CONJLIST X --> False)]`;;
e (REPEAT GEN_TAC);;
e (MATCH_MP_TAC MLK_imp_subst);;
e (ASM_REWRITE_TAC[MLK_iff_refl_th; CONJLIST_CONS]);;
let CONJLIST_CONS_NOT = top_thm();;

g `!S p X. [S . {} |~ CONJLIST (CONS p X) --> False] <=>
          [S . {} |~ p && CONJLIST X --> False]`;;
e (MESON_TAC[CONJLIST_CONS_NOT; MLK_iff]);;
let CONJLIST_CONS_NOT_TH = top_thm();;

g `!S p q r. [S . {} |~ p && q --> r] <=> [S . {} |~ p --> q --> r]`;;
e (MESON_TAC[MLK_shunt; MLK_ante_conj]);;
let MLK_AND_IMP = top_thm();;

g `!S p q. [S . {} |~ Not p --> q <-> (p --> False) --> q]`;;
e (REPEAT GEN_TAC);;
e (MATCH_MP_TAC MLK_imp_subst);;
e (REWRITE_TAC[MLK_axiom_not; MLK_iff_refl_th]);;
let MLK_NOT_IMP_ID = top_thm();;

g `!S p q r. [S . {} |~ (Not p --> q --> r) <-> ((p --> False) --> q --> r)]`;;
e (REPEAT GEN_TAC);;
e (MATCH_MP_TAC MLK_imp_subst);;
e (REWRITE_TAC[MLK_axiom_not; MLK_iff_refl_th]);;
let MLK_NOT_IMP_ID_1 = top_thm();;

g `!S p q r. [S . {} |~ Not p --> q --> r] <=>
             [S . {} |~ (p --> False) --> q --> r]`;;
e (MESON_TAC[MLK_NOT_IMP_ID_1; MLK_iff]);;
let MLK_NOT_IMP_ID_2 = top_thm();;

g `!S q p. [S . {} |~ Not q && p --> False] <=>
           [S . {} |~ (q --> False) --> p --> False]`;;
e (REWRITE_TAC[MLK_AND_IMP]);;
e (REWRITE_TAC[MLK_NOT_IMP_ID_2]);;
let MLK_NOT_IMP_False = top_thm();;

g `!S p q. [S . {} |~ p <-> q]
         ==> ([S . {} |~ Not p] <=> [S . {} |~ Not q])`;;
e (MESON_TAC[MLK_iff; MLK_not_subst]);;
let MLK_NOT_SUBST_1 = top_thm();;

g `!S p. [S . {} |~ Not p --> False] <=> [S . {} |~ Not (p --> False)]`;;
e (REPEAT GEN_TAC);;
e (MATCH_MP_TAC (MESON[]
     `!S p q r. ([S . {} |~ p] <=> [S . {} |~ q]) /\
                ([S . {} |~ q] <=> [S . {} |~ r])
                ==> ([S . {} |~ p] <=> [S . {} |~ r])`));;
e (EXISTS_TAC `Not Not p`);;
e CONJ_TAC;;
 e (ASM_MESON_TAC[MLK_DOUBLENEG_CL; MLK_not_def]);;
e (SUBGOAL_THEN
     `[S . {} |~ Not p <-> (p --> False)]
      ==> ([S . {} |~ Not Not p] <=> [S . {} |~ Not (p --> False)])`
     (fun th -> MATCH_MP_TAC th));;
 e (MESON_TAC[MLK_NOT_SUBST_1]);;
e (REWRITE_TAC[MLK_axiom_not]);;
let MLK_NOT_IMP_ID_4 = top_thm();;

g `!S q p. [S . {} |~ Not q && p --> False]
           ==> [S . {} |~ p --> q]`;;
e (REPEAT GEN_TAC);;
e (REWRITE_TAC[MLK_NOT_IMP_False]);;
e (MATCH_MP_TAC (MESON[]
     `!S p q r. ([S . {} |~ p] ==> [S . {} |~ q]) /\
              ([S . {} |~ q] ==> [S . {} |~ r])
              ==> ([S . {} |~ p] ==> [S . {} |~ r])`));;
e (EXISTS_TAC `((p --> q) --> False) --> False`);;
e (REWRITE_TAC[MLK_imp_false_rule]);;
e (REWRITE_TAC[GSYM MLK_not_def]);;
e (STRIP_TAC);;
e (MATCH_MP_TAC MLK_DOUBLENEG_CL);;
e (SIMP_TAC[MLK_not_def]);;
e (ASM_MESON_TAC[MLK_NOT_IMP_ID_4]);;
let MLK_NOT_IMP_ID_5 = top_thm();;

g `!S w. [S . {}
         |~ CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
            --> CONJLIST (MAP (Box)
                              (FLATMAP (\x. match x with Box c -> [c] | _ -> [])
                                        w))]`;;
e (GEN_TAC THEN LIST_INDUCT_TAC);;
 e (REWRITE_TAC[MEM; FLATMAP; MAP; MLK_imp_refl_th]);;
e (REWRITE_TAC[FLATMAP; MAP_APPEND]);;
e (MATCH_MP_TAC MLK_imp_trans);;
e (EXISTS_TAC
     `CONJLIST (match h with Box c -> [Box c] | _ -> []) &&
      CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) t)`);;
e CONJ_TAC;;
 e (MATCH_MP_TAC MLK_iff_imp1);;
 e (MATCH_ACCEPT_TAC CONJLIST_APPEND);;
e (MATCH_MP_TAC MLK_imp_trans);;
e (EXISTS_TAC
     `CONJLIST (MAP (Box) (match h with Box c -> [c] | _ -> [])) &&
      CONJLIST (MAP (Box)
       (FLATMAP (\x. match x with Box c -> [c] | _ -> []) t))`);;
e CONJ_TAC;;
 r (1);;
 e (MATCH_MP_TAC MLK_iff_imp2);;
 e (MATCH_ACCEPT_TAC CONJLIST_APPEND);;
e (MATCH_MP_TAC MLK_and_intro);;
e CONJ_TAC;;
 r (1);;
 e (ASM_MESON_TAC[MLK_imp_trans; MLK_and_right_th; MAP]);;
e (MATCH_MP_TAC MLK_imp_trans);;
e (EXISTS_TAC `CONJLIST (match h with Box c -> [Box c] | _ -> [])`);;
e CONJ_TAC;;
 e (MATCH_ACCEPT_TAC MLK_and_left_th);;
e (POP_ASSUM (K ALL_TAC));;
e (STRUCT_CASES_TAC (SPEC `h:form` (cases "form")) THEN
   REWRITE_TAC[distinctness "form"; MAP; MLK_imp_refl_th]);;
let CONJLIST_FLATMAP_DOT_BOX_LEMMA = top_thm();;

let CONJLIST_FLATMAP_DOT_BOX_LEMMA_2 = prove
 (`!S. (!p. [S. {} |~ (Box p --> Box p && Box (Box p))]) ==>
          (!w. [S . {} |~
          CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
          -->
          CONJLIST (MAP (Box)
            (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))])`,
  INTRO_TAC "!S; dotbox" THEN LIST_INDUCT_TAC THENL
  [REWRITE_TAC[FLATMAP; MAP; MLK_imp_refl_th]; ALL_TAC] THEN
  REWRITE_TAC[FLATMAP; MAP_APPEND] THEN MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC
    `CONJLIST (match h with Box c -> [Box c] | _ -> []) &&
     CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) t)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC MLK_iff_imp1 THEN MATCH_ACCEPT_TAC CONJLIST_APPEND;
   ALL_TAC] THEN
   MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC
     `CONJLIST (MAP (Box) (match h with Box c -> [c; Box c] | _ -> [])) &&
      CONJLIST (MAP (Box)
       (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) t))` THEN
  CONJ_TAC THENL
  [ALL_TAC;
   MATCH_MP_TAC MLK_iff_imp2 THEN MATCH_ACCEPT_TAC CONJLIST_APPEND] THEN
  MATCH_MP_TAC MLK_and_intro THEN CONJ_TAC THENL
  [ALL_TAC; ASM_MESON_TAC[MLK_imp_trans; MLK_and_right_th]] THEN
  MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `CONJLIST (match h with Box c -> [Box c] | _ -> [])` THEN
  CONJ_TAC THENL [MATCH_ACCEPT_TAC MLK_and_left_th; ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRUCT_CASES_TAC (SPEC `h:form` (cases "form")) THEN
  REWRITE_TAC[distinctness "form"; MAP; MLK_imp_refl_th] THEN
  REWRITE_TAC[CONJLIST; NOT_CONS_NIL] THEN  ASM_MESON_TAC[]);;
