(* ========================================================================= *)
(* Partial parametrization of the proof of the modal completeness.           *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini.                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Standard Frame.                                                           *)
(* ------------------------------------------------------------------------- *)

let FRAME = new_definition
  `FRAME (W:W->bool,R:W->W->bool) <=>
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W)`;;

let GEN_STANDARD_FRAME = new_definition
  `GEN_STANDARD_FRAME K S p (W,R) <=>
   W = {w | MAXIMAL_CONSISTENT S p w /\
            (!q. MEM q w ==> q SUBSENTENCE p)} /\
   K (W,R)  /\
   (!q w. Box q SUBFORMULA p /\ w IN W
          ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x)) /\
   (K (W,R) ==> FRAME(W,R))`;;

(* ------------------------------------------------------------------------- *)
(* Standard Model.                                                           *)
(* ------------------------------------------------------------------------- *)

let GEN_STANDARD_MODEL = new_definition
  `GEN_STANDARD_MODEL K S p (W,R) V <=>
   GEN_STANDARD_FRAME K S p (W,R) /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`;;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let GEN_TRUTH_LEMMA = prove
 (`!K S W R p V q.
     ~ [S . {} |~ p] /\
     GEN_STANDARD_MODEL K S p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GEN_STANDARD_MODEL; GEN_STANDARD_FRAME; SUBSENTENCE_CASES] THEN
  INTRO_TAC "np ((W K 1 2) val) q" THEN REMOVE_THEN "W" SUBST_VAR_TAC THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REMOVE_THEN "q" MP_TAC THEN
  HYP_TAC "1" (REWRITE_RULE[IN_ELIM_THM]) THEN
  HYP_TAC "val" (REWRITE_RULE[FORALL_IN_GSPEC]) THEN
  SPEC_TAC (`q:form`,`q:form`) THEN MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[holds] THEN
  CONJ_TAC THENL
  [INTRO_TAC "sub; !w; w" THEN
   HYP_TAC "w -> cons memq" (REWRITE_RULE[MAXIMAL_CONSISTENT]) THEN
   ASM_MESON_TAC[FALSE_IMP_NOT_CONSISTENT];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[MAXIMAL_CONSISTENT] THEN
   INTRO_TAC "p; !w; (cons (norep mem)) subf" THEN
   HYP_TAC "mem: t | nt" (C MATCH_MP (ASSUME `True SUBFORMULA p`)) THEN
   ASM_REWRITE_TAC[] THEN
   REFUTE_THEN (K ALL_TAC) THEN
   REMOVE_THEN "cons" MP_TAC THEN REWRITE_TAC[CONSISTENT] THEN
   REWRITE_TAC[MLK_not_def] THEN MATCH_MP_TAC MLK_imp_trans THEN
   EXISTS_TAC `Not True` THEN ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN
   MATCH_MP_TAC MLK_iff_imp1 THEN MATCH_ACCEPT_TAC MLK_not_true_th;
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![q/a]; q; sub; !w; w" THEN REMOVE_THEN "q" MP_TAC THEN
   MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    INTRO_TAC "sub1 q"] THEN EQ_TAC THENL
    [HYP MESON_TAC "w sub1 q" [MAXIMAL_CONSISTENT_MEM_NOT];
     REMOVE_THEN "q" (MP_TAC o SPEC `w: form list`) THEN
     ANTS_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT]];
     ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY
  (INTRO_TAC "![q1] [q2]; q1 q2; sub; !w; w" THEN
   REMOVE_THEN "q1" MP_TAC THEN
   MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    INTRO_TAC "sub1 +" THEN DISCH_THEN (MP_TAC o SPEC `w:form list`)] THEN
   REMOVE_THEN "q2" MP_TAC THEN
   MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    INTRO_TAC "sub2 +" THEN DISCH_THEN (MP_TAC o SPEC `w:form list`)] THEN
   HYP REWRITE_TAC "w" [] THEN
   DISCH_THEN (SUBST1_TAC o GSYM) THEN
   DISCH_THEN (SUBST1_TAC o GSYM) THEN
   CLAIM_TAC "rmk"
     `!q. q SUBFORMULA p ==> (MEM q w <=> [S. {} |~ CONJLIST w --> q])` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE];
    ALL_TAC]) THENL [

   (* Case && *)
   ASM_SIMP_TAC[] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE;
    MLK_and_intro; MLK_and_left_th; MLK_and_right_th; MLK_imp_trans]
  ;
   (* Case || *)
   EQ_TAC THENL
   [INTRO_TAC "q1q2";
    ASM_MESON_TAC[MLK_or_left_th; MLK_or_right_th; MLK_imp_trans]] THEN
   CLAIM_TAC "wq1q2" `[S . {} |~ CONJLIST w --> q1 || q2]` THENL
   [ASM_SIMP_TAC[CONJLIST_IMP_MEM]; ALL_TAC] THEN
   CLAIM_TAC "hq1 | hq1" `MEM q1 w \/ MEM (Not q1) w` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CLAIM_TAC "hq2 | hq2" `MEM q2 w \/ MEM (Not q2) w` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
    ASM_REWRITE_TAC[];
    REFUTE_THEN (K ALL_TAC)] THEN
   SUBGOAL_THEN `~ ([S . {} |~ (CONJLIST w --> False)])` MP_TAC THENL
   [REWRITE_TAC[GSYM MLK_not_def] THEN
    ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT];
    REWRITE_TAC[]] THEN
   MATCH_MP_TAC MLK_frege THEN EXISTS_TAC `q1 || q2` THEN
   ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN MATCH_MP_TAC MLK_imp_swap THEN
   REWRITE_TAC[MLK_disj_imp] THEN CONJ_TAC THEN MATCH_MP_TAC MLK_imp_swap THEN
   ASM_MESON_TAC[CONJLIST_IMP_MEM; MLK_axiom_not; MLK_iff_imp1; MLK_imp_trans]
 ;
 (* Case --> *)
 ASM_SIMP_TAC[] THEN EQ_TAC THENL
 [ASM_MESON_TAC[MLK_frege; CONJLIST_IMP_MEM]; INTRO_TAC "imp"] THEN
 CLAIM_TAC "hq1 | hq1" `MEM q1 w \/ MEM (Not q1) w` THENL
 [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
  ASM_MESON_TAC[CONJLIST_IMP_MEM; MLK_imp_swap; MLK_add_assum];
  ALL_TAC] THEN
 MATCH_MP_TAC MLK_shunt THEN MATCH_MP_TAC MLK_imp_trans THEN
 EXISTS_TAC `q1 && Not q1` THEN CONJ_TAC THENL
 [ALL_TAC; MESON_TAC[MLK_nc_th; MLK_imp_trans; MLK_ex_falso_th]] THEN
 MATCH_MP_TAC MLK_and_intro THEN REWRITE_TAC[MLK_and_right_th] THEN
 ASM_MESON_TAC[CONJLIST_IMP_MEM; MLK_imp_trans; MLK_and_left_th]
;
(* Case <-> *)
ASM_SIMP_TAC[] THEN REMOVE_THEN "sub" (K ALL_TAC) THEN EQ_TAC THENL
[MESON_TAC[MLK_frege; MLK_add_assum; MLK_modusponens_th;
           MLK_axiom_iffimp1; MLK_axiom_iffimp2];
 ALL_TAC] THEN
INTRO_TAC "iff" THEN MATCH_MP_TAC MLK_imp_trans THEN
EXISTS_TAC `(q1 --> q2) && (q2 --> q1)` THEN CONJ_TAC THENL
[MATCH_MP_TAC MLK_and_intro; MESON_TAC[MLK_iff_def_th; MLK_iff_imp2]] THEN
CLAIM_TAC "rmk'"
  `!q. q SUBFORMULA p
       ==> (MEM (Not q) w <=> [S . {} |~ CONJLIST w --> Not q])` THENL
[ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_NEG_EQ_DERIVABLE];
 ALL_TAC] THEN
CLAIM_TAC "hq1 | hq1"
  `[S . {} |~ (CONJLIST w --> q1)] \/ [S . {} |~ CONJLIST w --> Not q1]` THENL
[ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
 ASM_MESON_TAC[MLK_imp_swap; MLK_add_assum];
 ALL_TAC] THEN
CLAIM_TAC "hq2 | hq2"
  `[S . {} |~ (CONJLIST w --> q2)] \/ [S . {} |~ (CONJLIST w --> Not q2)]` THENL
[ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
 ASM_MESON_TAC[MLK_imp_swap; MLK_add_assum];
 ALL_TAC] THEN
ASM_MESON_TAC[MLK_nc_th; MLK_imp_trans; MLK_and_intro;
              MLK_ex_falso_th; MLK_imp_swap; MLK_shunt]
;
(* Case Box *)
INTRO_TAC "!a; a; sub; !w; w" THEN REWRITE_TAC[holds; IN_ELIM_THM] THEN
CLAIM_TAC "suba" `a SUBFORMULA p` THENL
[MATCH_MP_TAC SUBFORMULA_TRANS THEN
  EXISTS_TAC `Box a` THEN
  ASM_REWRITE_TAC[SUBFORMULA_INVERSION; SUBFORMULA_REFL];
  ALL_TAC] THEN
HYP_TAC "K" (REWRITE_RULE[FRAME; IN_ELIM_THM]) THEN
HYP_TAC "2" (REWRITE_RULE[FRAME; IN_ELIM_THM]) THEN
EQ_TAC THENL
[INTRO_TAC "boxa; !w'; (maxw' subw') r" THEN
 HYP_TAC "a" (C MATCH_MP (ASSUME `a SUBFORMULA p`)) THEN
 HYP_TAC "a: +" (SPEC `w':form list`) THEN
 ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
 DISCH_THEN (SUBST1_TAC o GSYM) THEN
 REMOVE_THEN "1" (MP_TAC o SPECL [`a: form`;`w: form list`]) THEN
 ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
 ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
 ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
 ALL_TAC] THEN
INTRO_TAC "3" THEN
REMOVE_THEN  "1" (MP_TAC o SPECL [`a:form`; `w:form list`]) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
DISCH_THEN SUBST1_TAC THEN INTRO_TAC "![w']; w'" THEN
REMOVE_THEN "3" (MP_TAC o SPEC `w':form list`) THEN
ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
HYP_TAC "a" (C MATCH_MP (ASSUME `a SUBFORMULA p`)) THEN
HYP_TAC "a: +" (SPEC `w':form list`) THEN
ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
DISCH_THEN (SUBST1_TAC o GSYM) THEN REWRITE_TAC[]
]
);;

(* ------------------------------------------------------------------------- *)
(* Standard Relation.                                                        *)
(* ------------------------------------------------------------------------- *)

let GEN_STANDARD_REL = new_definition
  `GEN_STANDARD_REL S p w x <=>
   MAXIMAL_CONSISTENT S p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT S p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)`;;

(* ------------------------------------------------------------------------- *)
(* Invariance by permutation.                                                *)
(* ------------------------------------------------------------------------- *)

let SET_OF_LIST_EQ_IMP_MEM = prove
 (`!l m x:A. set_of_list l = set_of_list m /\ MEM x l
             ==> MEM x m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN MESON_TAC[]);;

let SET_OF_LIST_EQ_CONJLIST = prove
 (`!S X Y. set_of_list X = set_of_list Y
         ==> [S . {} |~ CONJLIST X --> CONJLIST Y]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONJLIST_IMP_CONJLIST THEN
  INTRO_TAC "!p; p" THEN EXISTS_TAC `p:form` THEN
  REWRITE_TAC[MLK_imp_refl_th] THEN ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]);;

let SET_OF_LIST_EQ_CONJLIST_EQ = prove
 (`!S X Y. set_of_list X = set_of_list Y
         ==> [S . {} |~ CONJLIST X <-> CONJLIST Y]`,
  REWRITE_TAC[MLK_iff_def] THEN MESON_TAC[SET_OF_LIST_EQ_CONJLIST]);;

let SET_OF_LIST_EQ_CONSISTENT = prove
 (`!S X Y. set_of_list X = set_of_list Y /\ CONSISTENT S X
         ==> CONSISTENT S Y`,
  REWRITE_TAC[CONSISTENT] THEN INTRO_TAC "!S X Y; eq hp; p" THEN
  REMOVE_THEN "hp" MP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MLK_modusponens THEN EXISTS_TAC `Not (CONJLIST Y)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLK_contrapos THEN
  MATCH_MP_TAC SET_OF_LIST_EQ_CONJLIST THEN ASM_REWRITE_TAC[]);;

let SET_OF_LIST_EQ_MAXIMAL_CONSISTENT = prove
 (`!S p X Y. set_of_list X = set_of_list Y /\ NOREPETITION Y /\
             MAXIMAL_CONSISTENT S p X
             ==> MAXIMAL_CONSISTENT S p Y`,
  REWRITE_TAC[MAXIMAL_CONSISTENT] THEN REPEAT STRIP_TAC THENL
  [ASM_MESON_TAC[SET_OF_LIST_EQ_CONSISTENT];
   ASM_REWRITE_TAC[];
   ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]]);;

(* ------------------------------------------------------------------------- *)
(* Auxiliary lemmas for bisimulation                                         *)
(* ------------------------------------------------------------------------- *)

g `!S p u1 u2 w1 w2.
     set_of_list u1 = set_of_list w1 /\ NOREPETITION w1 /\
     set_of_list u2 = set_of_list w2 /\ NOREPETITION w2 /\
     GEN_STANDARD_REL S p u1 u2
     ==> GEN_STANDARD_REL S p w1 w2`;;
e (REPEAT GEN_TAC);;
e (REWRITE_TAC[GEN_STANDARD_REL]);;
e (STRIP_TAC);;
e (CONJ_TAC);;
e (MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[]);;
e (CONJ_TAC);;
e (ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]);;
e (CONJ_TAC);;
e (MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[]);;
e (ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]);;
let SET_OF_LIST_EQ_GEN_STANDARD_REL = top_thm();;

let GEN_STDWORLDS_RULES,GEN_STDWORLDS_INDUCT,GEN_STDWORLDS_CASES =
  new_inductive_set
  `!S M. MAXIMAL_CONSISTENT S p M /\
         (!q. MEM q M ==> q SUBSENTENCE p)
         ==> set_of_list M IN GEN_STDWORLDS p`;;

let GEN_STDREL_RULES,GEN_STDREL_INDUCT,GEN_STDREL_CASES =
  new_inductive_definition
  `!S w1 w2. GEN_STANDARD_REL S p w1 w2
             ==> GEN_STDREL p (set_of_list w1) (set_of_list w2)`;;

g `!p w1 w2. GEN_STDREL p w1 w2
             ==> w1 IN GEN_STDWORLDS p /\
                 w2 IN GEN_STDWORLDS p`;;
e (GEN_TAC);;
e (MATCH_MP_TAC GEN_STDREL_INDUCT);;
e (REWRITE_TAC[GEN_STANDARD_REL]);;
e (REPEAT STRIP_TAC);;
  e (MATCH_MP_TAC GEN_STDWORLDS_RULES);;
  e (EXISTS_TAC `S:form->bool`);;
  e (ASM_REWRITE_TAC[]);;
e (MATCH_MP_TAC GEN_STDWORLDS_RULES);;
e (EXISTS_TAC `S:form->bool`);;
e (ASM_REWRITE_TAC[]);;
let GEN_STDREL_IMP_GEN_STDWORLDS = top_thm();;
