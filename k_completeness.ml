(* ========================================================================= *)
(* Proof of the consistency and modal completeness of K.                     *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory.                                                    *)
(* ------------------------------------------------------------------------- *)

let FRAME_CHAR_K = prove
 (`FRAME:(W->bool)#(W->W->bool)->bool = CHAR {}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN
  REWRITE_TAC[IN_CHAR; IN_FRAME] THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY]);;

let K_FRAME_VALID = prove
(`!H p. [{} . H |~ p] /\
         (!q. q IN H ==> FRAME:(W->bool)#(W->W->bool)->bool |= q)
        ==> FRAME:(W->bool)#(W->W->bool)->bool |= p`,
ASM_MESON_TAC[GEN_CHAR_VALID; FRAME_CHAR_K]);;

g `FINITE_FRAME:(W->bool)#(W->W->bool)->bool = APPR {}`;;
e (REWRITE_TAC[EXTENSION; FORALL_PAIR_THM]);;
e (REWRITE_TAC[APPR_CAR; FRAME_CHAR_K; IN_FINITE_FRAME_INTER]);;
let FINITE_FRAME_APPR_K = top_thm();;

let K_FINITE_FRAME_VALID = prove
(`!p. [{} . {} |~ p] ==> FINITE_FRAME:(W->bool)#(W->W->bool)->bool |= p`,
ASM_MESON_TAC[GEN_APPR_VALID; FINITE_FRAME_APPR_K]);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness.                                                       *)
(* ------------------------------------------------------------------------- *)

g `~ [{} . {} |~ False]`;;
e (REFUTE_THEN (MP_TAC o MATCH_MP
    (INST_TYPE [`:num`,`:W`] K_FINITE_FRAME_VALID)));;
e (REWRITE_TAC[NOT_IN_EMPTY]);;
e (REWRITE_TAC[valid; holds; holds_in;
               FORALL_PAIR_THM; IN_FINITE_FRAME; NOT_FORALL_THM]);;
e (MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`]);;
e (REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING]);;
e (MESON_TAC[]);;
let K_CONSISTENT = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* K standard frames and models.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Standard Frame.                                                           *)
(* ------------------------------------------------------------------------- *)

let K_STANDARD_FRAME_DEF = new_definition
  `K_STANDARD_FRAME = GEN_STANDARD_FRAME {}`;;

let IN_K_STANDARD_FRAME = prove
(`(W,R) IN K_STANDARD_FRAME p <=>
W = {w | MAXIMAL_CONSISTENT {} p w /\
         (!q. MEM q w ==> q SUBSENTENCE p)} /\
(W,R) IN FINITE_FRAME /\
(!q w. Box q SUBFORMULA p /\ w IN W
       ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`,
 REWRITE_TAC[K_STANDARD_FRAME_DEF; IN_GEN_STANDARD_FRAME] THEN
 EQ_TAC THEN MESON_TAC[FINITE_FRAME_APPR_K]);;

(* ------------------------------------------------------------------------- *)
(* Standard Model.                                                           *)
(* ------------------------------------------------------------------------- *)

let K_STANDARD_MODEL_DEF = new_definition
   `K_STANDARD_MODEL = GEN_STANDARD_MODEL {}`;;

let K_STANDARD_MODEL_CAR = prove
 (`K_STANDARD_MODEL p (W,R) V <=>
   (W,R) IN K_STANDARD_FRAME p /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`,
  REWRITE_TAC[K_STANDARD_MODEL_DEF; K_STANDARD_FRAME_DEF;
              GEN_STANDARD_MODEL_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let K_TRUTH_LEMMA = prove
(`!W R p V q.
    ~ [{} . {} |~ p] /\
    K_STANDARD_MODEL p (W,R) V /\
    q SUBFORMULA p
    ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REWRITE_TAC[K_STANDARD_MODEL_DEF] THEN MESON_TAC[GEN_TRUTH_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Accessibility lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let K_STANDARD_REL_DEF = new_definition
  `K_STANDARD_REL p = GEN_STANDARD_REL {} p`;;

let K_STANDARD_REL_CAR = prove
 (`K_STANDARD_REL p w x <=>
   MAXIMAL_CONSISTENT {} p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT {} p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)`,
  REWRITE_TAC[K_STANDARD_REL_DEF; GEN_STANDARD_REL]);;

let  K_MAXIMAL_CONSISTENT = prove
(`!p. ~ [{} . {} |~ p]
     ==> ({M | MAXIMAL_CONSISTENT {} p M /\
          (!q. MEM q M ==> q SUBSENTENCE p)},
          K_STANDARD_REL p) IN FINITE_FRAME`,
 INTRO_TAC "!p; p" THEN
 MP_TAC (ISPECL [`{}: form ->bool`;
                 `p:form`] GEN_FINITE_FRAME_MAXIMAL_CONSISTENT) THEN
 ASM_REWRITE_TAC[K_STANDARD_REL_DEF]);;

let K_ACCESSIBILITY_LEMMA= prove
(`!p w q. ~ [{} . {} |~ p] /\
         MAXIMAL_CONSISTENT {} p w /\
         (!q. MEM q w ==> q SUBSENTENCE p) /\
         Box q SUBFORMULA p /\
         (!x. K_STANDARD_REL p w x ==> MEM q x)
         ==> MEM (Box q) w`,
 INTRO_TAC "!p w q; p maxw subw boxq rrr" THEN REMOVE_THEN "rrr" MP_TAC THEN
 ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN INTRO_TAC "asd" THEN
 REWRITE_TAC[NOT_FORALL_THM] THEN
 REWRITE_TAC[MESON[]`~(p ==> q) <=> (p /\ ~q)`] THEN
 REWRITE_TAC[K_STANDARD_REL_DEF] THEN
 MP_TAC (ISPECL [`{}: form-> bool`;`p:form`;`w:form list`;`q:form`]
        GEN_XK_FOR_ACCESSIBILITY_LEMMA) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
INTRO_TAC "@X. maxX subX subl" THEN
MP_TAC (ISPECL [`{}: form-> bool`;`p:form`;`w:form list`;`q:form`]
               GEN_ACCESSIBILITY_LEMMA) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
INTRO_TAC "gsr_wX notqX" THEN
EXISTS_TAC `X:form list` THEN
 ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Modal completeness theorem for K.                                         *)
(* ------------------------------------------------------------------------- *)

g `!p. ~ [{} . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT {} p M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)},
            K_STANDARD_REL p) IN K_STANDARD_FRAME p`;;
e (INTRO_TAC "!p; not_theor_p");;
e (REWRITE_TAC[IN_K_STANDARD_FRAME]);;
e CONJ_TAC;;
e (MATCH_MP_TAC K_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (INTRO_TAC "!q w; subform w_in");;
e EQ_TAC;;
 e (ASM_MESON_TAC[K_STANDARD_REL_CAR]);;
 e (INTRO_TAC "Implies_Mem_q");;
   e (HYP_TAC "w_in" (REWRITE_RULE[IN_ELIM_THM]));;
   e (MATCH_MP_TAC K_ACCESSIBILITY_LEMMA);;
   e (EXISTS_TAC `p:form`);;
   e (ASM_REWRITE_TAC[]);;
let KF_IN_STANDARD_K_FRAME = top_thm();;

g `!M p.
     ~ [{} . {} |~ p] /\
     MAXIMAL_CONSISTENT {} p M /\
     MEM (Not p) M /\
     (!q. MEM q M ==> q SUBSENTENCE p)
     ==> ~holds ({M | MAXIMAL_CONSISTENT {} p M /\
                      (!q. MEM q M ==> q SUBSENTENCE p)},
                 K_STANDARD_REL p)
                (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
                p M`;;
e (INTRO_TAC "!M p; p_not_theor max_cons mem implies");;
e (MATCH_MP_TAC GEN_COUNTERMODEL);;
e (EXISTS_TAC `{}:form->bool`);;
e (ASM_REWRITE_TAC[GEN_STANDARD_MODEL_DEF]);;
e CONJ_TAC;;
e (ASM_MESON_TAC[KF_IN_STANDARD_K_FRAME; K_STANDARD_FRAME_DEF]);;
e (ASM_MESON_TAC[IN_ELIM_THM]);;
let K_COUNTERMODEL = top_thm();;

g `!p. FINITE_FRAME:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [{} . {} |~ p]`;;
e (GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] );;
e (INTRO_TAC "p_not_theor");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT {} p M /\
                     (!q. MEM q M ==> q SUBSENTENCE p)},
                K_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC );;
e (MATCH_MP_TAC K_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `({M | MAXIMAL_CONSISTENT {} p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
                  K_STANDARD_REL p) IN GEN_STANDARD_FRAME {} p`
     MP_TAC);;
e (ASM_MESON_TAC[KF_IN_STANDARD_K_FRAME; K_STANDARD_FRAME_DEF]);;
e (ASM_MESON_TAC[GEN_COUNTERMODEL_ALT]);;
let K_COMPLETENESS_THM = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* Modal completeness for K for models on a generic (infinite) domain.       *)
(* ------------------------------------------------------------------------- *)

let K_COMPLETENESS_THM_GEN = prove
 (`!p. INFINITE (:A) /\ FINITE_FRAME:(A->bool)#(A->A->bool)->bool |= p
       ==> [{} . {} |~ p]`,
  SUBGOAL_THEN
    `INFINITE (:A)
     ==> !p. FINITE_FRAME:(A->bool)#(A->A->bool)->bool |= p
             ==> FINITE_FRAME:(form list->bool)#(form list->form list->bool)->bool |= p`
    (fun th -> MESON_TAC[th; K_COMPLETENESS_THM]) THEN
  ASM_MESON_TAC[FINITE_FRAME_APPR_K; GEN_LEMMA_FOR_GEN_COMPLETENESS]);;

(* ------------------------------------------------------------------------- *)
(* Simple decision procedure for K.                                          *)
(* ------------------------------------------------------------------------- *)

let K_TAC : tactic =
  MATCH_MP_TAC K_COMPLETENESS_THM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in; holds;
              IN_FINITE_FRAME; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[];;

let K_RULE tm =
  prove(tm, REPEAT GEN_TAC THEN K_TAC);;

K_RULE `!p q r. [{} . {} |~ (Not p --> q --> r) <->
                            ((p --> False) --> q --> r)]`;;

K_RULE `!p. [{} . {} |~ (p --> False) --> False <-> p]`;;

K_RULE `!p q. [{} . {} |~ Not (p && q) <-> Not p || Not q]`;;

(* ------------------------------------------------------------------------- *)
(* Countermodel using set of formulae (instead of lists of formulae).        *)
(* ------------------------------------------------------------------------- *)

let K_STDWORLDS_RULES,K_STDWORLDS_INDUCT,K_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT {} p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN K_STDWORLDS p`;;

let K_STDREL_RULES,K_STDREL_INDUCT,K_STDREL_CASES = new_inductive_definition
  `!w1 w2. K_STANDARD_REL p w1 w2
           ==> K_STDREL p (set_of_list w1) (set_of_list w2)`;;

let K_STDREL_IMP_K_STDWORLDS = prove
 (`!p w1 w2. K_STDREL p w1 w2 ==>
             w1 IN K_STDWORLDS p /\
             w2 IN K_STDWORLDS p`,
  GEN_TAC THEN MATCH_MP_TAC K_STDREL_INDUCT THEN
  REWRITE_TAC[K_STANDARD_REL_CAR] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC K_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;

g `!p. BISIMIMULATION
       ({M | MAXIMAL_CONSISTENT {} p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
         K_STANDARD_REL p,
         (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w))
       (K_STDWORLDS p,
        K_STDREL p,
        (\a w. Atom a SUBFORMULA p /\ Atom a IN w))
       (\w1 w2.
          MAXIMAL_CONSISTENT {} p w1 /\
          (!q. MEM q w1 ==> q SUBSENTENCE p) /\
          w2 IN K_STDWORLDS p /\
          set_of_list w1 = w2)`;;
e (GEN_TAC THEN REWRITE_TAC[BISIMIMULATION] THEN REPEAT GEN_TAC THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC[IN_SET_OF_LIST];
    ALL_TAC] THEN
   CONJ_TAC);;
e (INTRO_TAC "![u1]; w1u1" THEN EXISTS_TAC `set_of_list u1:form->bool` THEN
   HYP_TAC "w1u1 -> hp" (REWRITE_RULE[K_STANDARD_REL_CAR]) THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC K_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC K_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN MATCH_MP_TAC K_STDREL_RULES THEN
   ASM_REWRITE_TAC[]);;
e (INTRO_TAC "![u2]; w2u2" THEN EXISTS_TAC `list_of_set u2:form list` THEN
   REWRITE_TAC[CONJ_ACI] THEN
   HYP_TAC "w2u2 -> @x2 y2. x2 y2 x2y2" (REWRITE_RULE[K_STDREL_CASES]) THEN
   REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   SIMP_TAC[SET_OF_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   SIMP_TAC[MEM_LIST_OF_SET; FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
   CONJ_TAC THENL
   [HYP_TAC "x2y2 -> hp" (REWRITE_RULE[K_STANDARD_REL_CAR]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC);;
e (ASM_MESON_TAC[K_STDREL_IMP_K_STDWORLDS]);;
e CONJ_TAC;;
e (ASM_REWRITE_TAC[K_STANDARD_REL_DEF]);;
e (MATCH_MP_TAC SET_OF_LIST_EQ_STANDARD_REL THEN
   EXISTS_TAC `x2:form list` THEN EXISTS_TAC `y2:form list` THEN
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT; K_STANDARD_REL_DEF]);;
e (MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN
   EXISTS_TAC `y2:form list` THEN
   SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   ASM_MESON_TAC[K_STANDARD_REL_CAR]);;
let K_BISIMIMULATION_SET_OF_LIST = top_thm();;

let K_COUNTERMODEL_FINITE_SETS = prove
 (`!p. ~[{} . {} |~ p] ==> ~holds_in (K_STDWORLDS p, K_STDREL p) p`,
  INTRO_TAC "!p; p" THEN
  DESTRUCT_TAC "@M. max mem subf"
    (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ [{} . {} |~ p]`)) THEN
  REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP] THEN
  ASSUM_LIST (LABEL_TAC "hp" o MATCH_MP K_COUNTERMODEL o
                end_itlist CONJ o rev) THEN
  EXISTS_TAC `\a w. Atom a SUBFORMULA p /\ Atom a IN w` THEN
  EXISTS_TAC `set_of_list M:form->bool` THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "hp" MP_TAC THEN
  MATCH_MP_TAC (MESON[] `(p <=> q) ==> (~p ==> ~q)`) THEN
  MATCH_MP_TAC BISIMIMULATION_HOLDS THEN
  EXISTS_TAC `\w1 w2. MAXIMAL_CONSISTENT {} p w1 /\
                      (!q. MEM q w1 ==> q SUBSENTENCE p) /\
                      w2 IN K_STDWORLDS p /\
                      set_of_list w1 = w2` THEN
  ASM_REWRITE_TAC[K_BISIMIMULATION_SET_OF_LIST] THEN
  MATCH_MP_TAC K_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;
