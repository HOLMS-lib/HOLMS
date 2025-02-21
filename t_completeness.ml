(* ========================================================================= *)
(* Proof of the consistency and modal completeness of T.                     *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

let T_AX = new_definition
  `T_AX = {Box p -->  p | p IN (:form)}`;;

let T_IN_T_AX = prove
 (`!q. Box q --> q IN T_AX`,
  REWRITE_TAC[T_AX; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]);;

let T_AX_T= prove
 (`!q. [T_AX. {} |~ (Box q --> q)]`,
  MESON_TAC[MODPROVES_RULES; T_IN_T_AX]);;

(* ------------------------------------------------------------------------- *)
(* Reflexive frames.                                                         *)
(* ------------------------------------------------------------------------- *)

let MODAL_REFL = prove
 (`!W R.
     (!w:W. w IN W ==> R w w) <=>
     (!p. holds_in (W,R) (Box p --> p))`,
  MODAL_SCHEMA_TAC THEN MESON_TAC[]);;

let REFL_DEF = new_definition
  `REFL =
   {(W:W->bool,R:W->W->bool) |
    ~(W = {}) /\
    (!x y:W. R x y ==> x IN W /\ y IN W) /\
    (!x:W. x IN W ==> R x x)}`;;

let IN_REFL = prove
 (`(W:W->bool,R:W->W->bool) IN REFL <=>
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   (!x:W. x IN W ==> R x x)`,
  REWRITE_TAC[REFL_DEF; IN_ELIM_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory: Reflexive Frames are characteristic for T.         *)
(* ------------------------------------------------------------------------- *)

g `REFL:(W->bool)#(W->W->bool)->bool = CHAR T_AX`;;
e (REWRITE_TAC[EXTENSION; FORALL_PAIR_THM]);;
e (REWRITE_TAC[IN_CHAR; IN_REFL; IN_FRAME]);;
e (REWRITE_TAC[T_AX; FORALL_IN_GSPEC; IN_UNIV]);;
e (REPEAT GEN_TAC);;
e EQ_TAC;;
 e (INTRO_TAC "not_empty Rel Refl");;
 e (ASM_MESON_TAC[MODAL_REFL]);;
e (INTRO_TAC "(not_empty Rel) char");;
e (ASM_MESON_TAC[MODAL_REFL]);;
let REFL_CHAR_T = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. Reflexive Frames                                *)
(* ------------------------------------------------------------------------- *)

g `!W:W->bool R:W->W->bool. ~(W = {}) /\
                            (!x y. R x y ==> x IN W /\ y IN W) /\
                            (!x. x IN W ==> R x x)
                            ==> (!p. holds_in (W,R) (Box p --> p))`;;
e (INTRO_TAC "!W R; non_empty Rel Refl");;
e (MP_TAC (REWRITE_RULE [EXTENSION; FORALL_PAIR_THM] REFL_CHAR_T));;
e (INTRO_TAC "Eq_form_Refl_Char");;
e (CLAIM_TAC "In_Refl" `(W,R) IN REFL:(W->bool)#(W->W->bool)->bool`);;
  e (ASM_REWRITE_TAC [IN_REFL]);;
e (SUBGOAL_THEN `(W,R) IN  CHAR T_AX: (W->bool)#(W->W->bool)->bool` MP_TAC);;
  e (ASM_MESON_TAC []);;
e (ASM_REWRITE_TAC [IN_CHAR; T_AX; FORALL_IN_GSPEC; IN_UNIV]);;
e (ASM_MESON_TAC []);;
let REFL_IMP_T = top_thm();;

let T_REFL_VALID = prove
 (`!H p. [T_AX . H |~ p] /\
         (!q. q IN H ==> REFL:(W->bool)#(W->W->bool)->bool |= q)
         ==> REFL:(W->bool)#(W->W->bool)->bool |= p`,
  ASM_MESON_TAC[GEN_CHAR_VALID; REFL_CHAR_T]);;

(* ------------------------------------------------------------------------- *)
(* Finite Reflexive Frames are appropriate for T.                            *)
(* ------------------------------------------------------------------------- *)

let RF_DEF = new_definition
 `RF =
  {(W:W->bool,R:W->W->bool) |
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W /\
   (!x. x IN W ==> R x x)}`;;

let IN_RF = prove
 (`(W:W->bool,R:W->W->bool) IN RF <=>
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W /\
   (!x. x IN W ==> R x x)`,
  REWRITE_TAC[RF_DEF; IN_ELIM_PAIR_THM]);;

let RF_SUBSET_REFL = prove
 (`RF:(W->bool)#(W->W->bool)->bool SUBSET REFL`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_RF; IN_REFL] THEN MESON_TAC[]);;

g `RF: (W->bool)#(W->W->bool)->bool = APPR T_AX`;;
e (REWRITE_TAC[EXTENSION; FORALL_PAIR_THM]);;
e (REPEAT GEN_TAC);;
e EQ_TAC;;
 e (INTRO_TAC "In_RF");;
  e (SUBGOAL_THEN `(p1:W->bool, p2:W->W->bool) IN CHAR T_AX` MP_TAC);;
    e (ASM_MESON_TAC [RF_SUBSET_REFL; SUBSET; REFL_CHAR_T]);;
  e (HYP_TAC "In_RF" (REWRITE_RULE[IN_RF]));;
  e (ASM_REWRITE_TAC [IN_APPR; IN_FINITE_FRAME; IN_FRAME]);;
  e (ASM_MESON_TAC[CHAR_CAR]);;
 e (INTRO_TAC "In_Appr");;
  e (SUBGOAL_THEN  `(p1:W->bool,p2:W->W->bool) IN REFL` MP_TAC);;
   e (SUBGOAL_THEN  `(p1:W->bool,p2:W->W->bool) IN CHAR T_AX` MP_TAC);;
     e (ASM_MESON_TAC[APPR_SUBSET_CHAR; SUBSET; FORALL_PAIR_THM]);;
   e (ASM_MESON_TAC[REFL_CHAR_T; EXTENSION; FORALL_PAIR_THM]);;
  e (HYP_TAC "In_Appr" (REWRITE_RULE[IN_APPR; IN_FINITE_FRAME]));;
  e (ASM_REWRITE_TAC[IN_REFL; IN_RF]);;
let RF_APPR_T = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. RF.                                             *)
(* ------------------------------------------------------------------------- *)

let T_RF_VALID = prove
 (`!p. [T_AX . {} |~ p] ==> RF:(W->bool)#(W->W->bool)->bool |= p`,
  MESON_TAC[GEN_APPR_VALID; RF_APPR_T]);;

(* ------------------------------------------------------------------------- *)
(* Proof of Consistency of T.                                                *)
(* ------------------------------------------------------------------------- *)

let T_CONSISTENT = prove
 (`~ [T_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] T_RF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM;
              IN_RF; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. x = 0 /\ x = y`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* T standard frames and models.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Standard Frame.                                                           *)
(* ------------------------------------------------------------------------- *)

let T_STANDARD_FRAME_DEF = new_definition
  `T_STANDARD_FRAME p = GEN_STANDARD_FRAME T_AX p`;;

let IN_T_STANDARD_FRAME = prove
  (`!p W R. (W,R) IN T_STANDARD_FRAME p <=>
            W = {w | MAXIMAL_CONSISTENT T_AX p w /\
                     (!q. MEM q w ==> q SUBSENTENCE p)} /\
            (W,R) IN RF /\
            (!q w. Box q SUBFORMULA p /\ w IN W
                   ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`,
 REPEAT GEN_TAC THEN
 REWRITE_TAC[T_STANDARD_FRAME_DEF; IN_GEN_STANDARD_FRAME] THEN
 EQ_TAC THEN MESON_TAC[RF_APPR_T]);;

(* ------------------------------------------------------------------------- *)
(* Standard model.                                                           *)
(* ------------------------------------------------------------------------- *)

let T_STANDARD_MODEL_DEF = new_definition
  `T_STANDARD_MODEL = GEN_STANDARD_MODEL T_AX`;;

let RF_SUBSET_FRAME = prove
 (`RF:(W->bool)#(W->W->bool)->bool SUBSET FRAME`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM] THEN INTRO_TAC "![W] [R]" THEN
  REWRITE_TAC[IN_RF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_FRAME]);;

let T_STANDARD_MODEL_CAR = prove
 (`!W R p V.
     T_STANDARD_MODEL p (W,R) V <=>
     (W,R) IN T_STANDARD_FRAME p /\
     (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[T_STANDARD_MODEL_DEF; GEN_STANDARD_MODEL_DEF] THEN
  REWRITE_TAC[IN_T_STANDARD_FRAME; IN_GEN_STANDARD_FRAME] THEN
  EQ_TAC THEN ASM_MESON_TAC[RF_APPR_T]);;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let T_TRUTH_LEMMA = prove
 (`!W R p V q.
     ~ [T_AX . {} |~ p] /\
     T_STANDARD_MODEL p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REWRITE_TAC[T_STANDARD_MODEL_DEF] THEN MESON_TAC[GEN_TRUTH_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Accessibility lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let T_STANDARD_REL_DEF = new_definition
  `T_STANDARD_REL p w x <=>
   GEN_STANDARD_REL T_AX p w x`;;

let T_STANDARD_REL_CAR = prove
 (`!p w x.
     T_STANDARD_REL p w x <=>
     MAXIMAL_CONSISTENT T_AX p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT T_AX p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
     (!B. MEM (Box B) w ==> MEM B x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[T_STANDARD_REL_DEF; GEN_STANDARD_REL] THEN
  EQ_TAC THEN REPEAT (ASM_MESON_TAC[]) THEN REPEAT (ASM_MESON_TAC[]));;

let RF_MAXIMAL_CONSISTENT = prove
 (`!p. ~ [T_AX . {} |~ p]
         ==> ({M | MAXIMAL_CONSISTENT T_AX p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
                   T_STANDARD_REL p) IN RF `,
  INTRO_TAC "!p; p" THEN
  MP_TAC (ISPECL [`T_AX`; `p:form`] GEN_FINITE_FRAME_MAXIMAL_CONSISTENT) THEN
  REWRITE_TAC[IN_FINITE_FRAME] THEN INTRO_TAC "gen_max_cons" THEN
  ASM_REWRITE_TAC[IN_RF] THEN
  (* Nonempty *)
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Well-defined *)
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[T_STANDARD_REL_DEF] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Finite *)
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Reflexive *)
  REWRITE_TAC[IN_ELIM_THM; T_STANDARD_REL_CAR] THEN
  INTRO_TAC "!x; (max_cons) (imp)" THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN INTRO_TAC "box_mem" THEN
  MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA THEN
  EXISTS_TAC `T_AX` THEN EXISTS_TAC `p:form` THEN EXISTS_TAC `[Box B]` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [ASM_REWRITE_TAC[MEM] THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC]  THEN
  CLAIM_TAC "d" `B SUBFORMULA Box B` THENL
  [ASM_REWRITE_TAC[SUBFORMULA_INVERSION; SUBFORMULA_REFL]; ALL_TAC] THEN
  CONJ_TAC THENL
  [CLAIM_TAC "c" `Box B SUBSENTENCE p` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   HYP_TAC "c" (REWRITE_RULE[SUBSENTENCE_CASES]) THEN
   DISJ_CASES_TAC (ASSUME `Box B SUBFORMULA p \/
                           (?p'. Box B = Not p' /\ p' SUBFORMULA p)`) THENL
   [ASM_MESON_TAC[SUBFORMULA_TRANS]; ALL_TAC] THEN
   CLAIM_TAC "@y. e" `?p'. Box B = Not p' /\ p' SUBFORMULA p` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `~(Box B = Not y)` MP_TAC THENL
   [ASM_MESON_TAC[form_DISTINCT]; ALL_TAC] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[CONJLIST] THEN ASM_MESON_TAC[T_AX_T]);;

let T_ACCESSIBILITY_LEMMA = prove
(`!p w q.
   ~ [T_AX . {} |~ p] /\
   MAXIMAL_CONSISTENT T_AX p w /\
   (!q. MEM q w ==> q SUBSENTENCE p) /\
   Box q SUBFORMULA p /\
   (!x. T_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`,
  INTRO_TAC "!p w q; p maxw subw boxq rrr" THEN REMOVE_THEN "rrr" MP_TAC THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN INTRO_TAC "asd" THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN
  REWRITE_TAC[MESON[]`~(p ==> q) <=> (p /\ ~q)`] THEN
  REWRITE_TAC[T_STANDARD_REL_DEF] THEN
  MP_TAC (ISPECL [`T_AX`;`p:form`;`w:form list`;`q:form`]
          GEN_XK_FOR_ACCESSIBILITY_LEMMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  INTRO_TAC "@X. maxX subX subl" THEN
  MP_TAC (ISPECL [`T_AX`;`p:form`;`w:form list`;`q:form`]
                 GEN_ACCESSIBILITY_LEMMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  INTRO_TAC "gsr_wX notqX" THEN EXISTS_TAC `X:form list` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Modal completeness theorem for K4.                                        *)
(* ------------------------------------------------------------------------- *)

g `!p. ~ [T_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT T_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
            T_STANDARD_REL p)
           IN T_STANDARD_FRAME p`;;
e (INTRO_TAC "!p; not_theor_p");;
e (REWRITE_TAC[IN_T_STANDARD_FRAME]);;
e CONJ_TAC;;
 e (MATCH_MP_TAC RF_MAXIMAL_CONSISTENT);;
 e (ASM_REWRITE_TAC[]);;
e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (INTRO_TAC "!q w; boxq maxw subw");;
e EQ_TAC;;
 e (ASM_MESON_TAC[T_STANDARD_REL_CAR]);;
e (ASM_MESON_TAC[T_ACCESSIBILITY_LEMMA]);;
let RF_IN_T_STANDARD_FRAME = top_thm();;

let T_COUNTERMODEL = prove
 (`!M p.
     ~ [T_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT T_AX p M /\
     MEM (Not p) M /\
     (!q. MEM q M ==> q SUBSENTENCE p)
     ==> ~holds ({M | MAXIMAL_CONSISTENT T_AX p M /\
                      (!q. MEM q M ==> q SUBSENTENCE p)},
                 T_STANDARD_REL p)
                (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
                p M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC GEN_COUNTERMODEL THEN
  EXISTS_TAC `T_AX` THEN ASM_REWRITE_TAC[GEN_STANDARD_MODEL_DEF] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[RF_IN_T_STANDARD_FRAME; T_STANDARD_FRAME_DEF]; ALL_TAC] THEN
  ASM_MESON_TAC[IN_ELIM_THM]);;

g `!p. RF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [T_AX . {} |~ p]`;;
e (GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM]);;
e (INTRO_TAC "p_not_theor");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT T_AX p M /\
                     (!q. MEM q M ==> q SUBSENTENCE p)},
                T_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC);;
 e (MATCH_MP_TAC RF_MAXIMAL_CONSISTENT);;
 e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `({M | MAXIMAL_CONSISTENT T_AX p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
                  T_STANDARD_REL p) IN GEN_STANDARD_FRAME T_AX p`
                 MP_TAC);;
 e (ASM_MESON_TAC[RF_IN_T_STANDARD_FRAME; T_STANDARD_FRAME_DEF]);;
e (ASM_MESON_TAC[GEN_COUNTERMODEL_ALT]);;
let T_COMPLETENESS_THM = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* Modal completeness for T for models on a generic (infinite) domain.       *)
(* ------------------------------------------------------------------------- *)

let T_COMPLETENESS_THM_GEN = prove
 (`!p. INFINITE (:A) /\ RF:(A->bool)#(A->A->bool)->bool |= p
       ==> [T_AX . {} |~ p]`,
  SUBGOAL_THEN
    `INFINITE (:A)
     ==> !p. RF:(A->bool)#(A->A->bool)->bool |= p
             ==> RF:(form list->bool)#(form list->form list->bool)->bool |= p`
    (fun th -> MESON_TAC[th; T_COMPLETENESS_THM]) THEN
  ASM_MESON_TAC [RF_APPR_T; GEN_LEMMA_FOR_GEN_COMPLETENESS]);;

(* ------------------------------------------------------------------------- *)
(* Simple decision procedure for T.                                          *)
(* ------------------------------------------------------------------------- *)

let T_TAC : tactic =
  MATCH_MP_TAC T_COMPLETENESS_THM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in; holds;
              IN_RF; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[];;

let T_RULE tm =
  prove(tm, REPEAT GEN_TAC THEN T_TAC);;

T_RULE `!p q r. [T_AX . {} |~ p && q && r --> p && r]`;;
T_RULE `!p q. [T_AX . {} |~ Box (p --> q) --> Box p --> Box q]`;;
T_RULE `!p q. [T_AX . {} |~  Box (p --> q) && Box p --> Box q]`;;
T_RULE `!p. [T_AX . {} |~  Box p --> p]`;;

(* T_RULE `!p. [T_AX . {} |~ Box p --> Box (Box p)]`;;*)
(* T_RULE `!p. [T_AX . {} |~ (Box (Box p --> p) --> Box p)]`;;*)
(* T_RULE `!p. [T_AX . {} |~ Box (Box p --> p) --> Box p]`;; *)
(* T_RULE `[T_AX . {} |~ Box (Box False --> False) --> Box False]`;; *)

(* T_box_iff_th *)
T_RULE `!p q. [T_AX . {} |~ Box (p <-> q) --> (Box p <-> Box q)] `;;

(* ------------------------------------------------------------------------- *)
(* Countermodel using set of formulae (instead of lists of formulae).        *)
(* ------------------------------------------------------------------------- *)

let T_STDWORLDS_RULES,T_STDWORLDS_INDUCT,T_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT T_AX p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN T_STDWORLDS p`;;

let T_STDREL_RULES,T_STDREL_INDUCT,T_STDREL_CASES = new_inductive_definition
  `!w1 w2. T_STANDARD_REL p w1 w2
           ==> T_STDREL p (set_of_list w1) (set_of_list w2)`;;

let T_STDREL_IMP_T_STDWORLDS = prove
 (`!p w1 w2. T_STDREL p w1 w2
             ==> w1 IN T_STDWORLDS p /\
                 w2 IN T_STDWORLDS p`,
  GEN_TAC THEN MATCH_MP_TAC T_STDREL_INDUCT THEN
  REWRITE_TAC[T_STANDARD_REL_CAR] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC T_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;

let SET_OF_LIST_EQ_T_STANDARD_REL = prove
 (`!p u1 u2 w1 w2.
     set_of_list u1 = set_of_list w1 /\ NOREPETITION w1 /\
     set_of_list u2 = set_of_list w2 /\ NOREPETITION w2 /\
     T_STANDARD_REL p u1 u2
     ==> T_STANDARD_REL p w1 w2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[T_STANDARD_REL_CAR] THEN STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]; ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]);;

let BISIMIMULATION_SET_OF_LIST = prove
 (`!p. BISIMIMULATION
       (
         {M | MAXIMAL_CONSISTENT T_AX p M /\
              (!q. MEM q M ==> q SUBSENTENCE p)},
         T_STANDARD_REL p,
         (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
       )
       (T_STDWORLDS p,
        T_STDREL p,
        (\a w. Atom a SUBFORMULA p /\ Atom a IN w))
       (\w1 w2.
          MAXIMAL_CONSISTENT T_AX p w1 /\
          (!q. MEM q w1 ==> q SUBSENTENCE p) /\
          w2 IN T_STDWORLDS p /\
          set_of_list w1 = w2)`,
  GEN_TAC THEN REWRITE_TAC[BISIMIMULATION] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
  [GEN_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC[IN_SET_OF_LIST];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![u1]; w1u1" THEN EXISTS_TAC `set_of_list u1:form->bool` THEN
   HYP_TAC "w1u1 -> hp" (REWRITE_RULE[T_STANDARD_REL_CAR]) THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC T_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC T_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN MATCH_MP_TAC T_STDREL_RULES THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "![u2]; w2u2" THEN EXISTS_TAC `list_of_set u2:form list` THEN
  REWRITE_TAC[CONJ_ACI] THEN
  HYP_TAC "w2u2 -> @x2 y2. x2 y2 x2y2" (REWRITE_RULE[T_STDREL_CASES]) THEN
  REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  SIMP_TAC[SET_OF_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  SIMP_TAC[MEM_LIST_OF_SET; FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
  CONJ_TAC THENL
  [HYP_TAC "x2y2 -> hp" (REWRITE_RULE[T_STANDARD_REL_CAR]) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[T_STDREL_IMP_T_STDWORLDS]; ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN
   EXISTS_TAC `y2:form list` THEN
   SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   ASM_MESON_TAC[T_STANDARD_REL_CAR]; ALL_TAC] THEN
   MATCH_MP_TAC SET_OF_LIST_EQ_T_STANDARD_REL THEN
  EXISTS_TAC `x2:form list` THEN EXISTS_TAC `y2:form list` THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET;
           FINITE_SET_OF_LIST] THEN
  ASM_MESON_TAC[MAXIMAL_CONSISTENT]);;

let T_COUNTERMODEL_FINITE_SETS = prove
 (`!p. ~ [T_AX . {} |~ p] ==> ~holds_in (T_STDWORLDS p, T_STDREL p) p`,
  INTRO_TAC "!p; p" THEN
  DESTRUCT_TAC "@M. max mem subf"
    (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ [T_AX . {} |~ p]`)) THEN
  REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP] THEN
  ASSUM_LIST (LABEL_TAC "hp" o MATCH_MP T_COUNTERMODEL o
                end_itlist CONJ o rev) THEN
  EXISTS_TAC `\a w. Atom a SUBFORMULA p /\ Atom a IN w` THEN
  EXISTS_TAC `set_of_list M:form->bool` THEN CONJ_TAC THENL
  [MATCH_MP_TAC T_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "hp" MP_TAC THEN
  MATCH_MP_TAC (MESON[] `(p <=> q) ==> (~p ==> ~q)`) THEN
  MATCH_MP_TAC BISIMIMULATION_HOLDS THEN
  EXISTS_TAC `(\w1 w2. MAXIMAL_CONSISTENT T_AX p w1 /\
                       (!q. MEM q w1 ==> q SUBSENTENCE p) /\
                       w2 IN T_STDWORLDS p /\
                       set_of_list w1 = w2)` THEN
  ASM_REWRITE_TAC[BISIMIMULATION_SET_OF_LIST] THEN
  MATCH_MP_TAC T_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;