(* ========================================================================= *)
(* Partial parametrization of the proof of the modal completeness.           *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Frame.                                                                    *)
(* ------------------------------------------------------------------------- *)

let FRAME_DEF = new_definition
  `FRAME = {(W:W->bool,R:W->W->bool) | ~(W = {}) /\
                                       (!x y:W. R x y ==> x IN W /\ y IN W)}`;;

let IN_FRAME = prove
 (`!W:W->bool R:W->W->bool. (W,R) IN FRAME <=>
   ~(W = {}) /\ (!x y:W. R x y ==> x IN W /\ y IN W)`,
  REWRITE_TAC[FRAME_DEF; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let FINITE_FRAME_DEF = new_definition
  `FINITE_FRAME = {(W:W->bool,R:W->W->bool) | (W,R) IN FRAME /\ FINITE W}`;;

let IN_FINITE_FRAME = prove
 (`!W:W->bool R:W->W->bool. (W,R) IN FINITE_FRAME <=>
   ~(W = {}) /\ (!x y:W. R x y ==> x IN W /\ y IN W) /\ FINITE W`,
  REWRITE_TAC[FINITE_FRAME_DEF; IN_FRAME; IN_ELIM_THM; PAIR_EQ] THEN
  MESON_TAC[]);;

let FINITE_FRAME_SUBSET_FRAME = prove
 (`FINITE_FRAME:(W->bool)#(W->W->bool)->bool SUBSET FRAME`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_FINITE_FRAME; IN_FRAME] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory and General Validity.                               *)
(* ------------------------------------------------------------------------- *)

(* Frames characteristic to certain axioms schemata S: CHAR S.               *)

let CHAR_DEF = new_definition
  `CHAR S = {(W:W->bool,R:W->W->bool) |
                    (W,R) IN FRAME /\
                    (!p. p IN S ==> holds_in (W:W->bool,R:W->W->bool) p)}`;;

let IN_CHAR = prove
 (`!S. (W:W->bool,R:W->W->bool) IN CHAR S <=>
       (W,R) IN FRAME /\
       !p. p IN S ==> holds_in (W:W->bool,R:W->W->bool) p`,
  REWRITE_TAC[CHAR_DEF; IN_ELIM_PAIR_THM]);;

let GEN_KAXIOM_CHAR_VALID = prove
 (`!S p. KAXIOM p ==> CHAR S:(W->bool)#(W->W->bool)->bool |= p`,
  GEN_TAC THEN MATCH_MP_TAC KAXIOM_INDUCT THEN REWRITE_TAC[valid] THEN
  FIX_TAC "f" THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  SPEC_TAC (`f:(W->bool)#(W->W->bool)`,`f:(W->bool)#(W->W->bool)`) THEN
  MATCH_MP_TAC (MESON[PAIR_SURJECTIVE]
    `(!W:W->bool R:W->W->bool. P (W,R)) ==> (!f. P f)`) THEN
  REWRITE_TAC[IN_CHAR; IN_FRAME] THEN REPEAT GEN_TAC THEN
  REPEAT CONJ_TAC THEN MODAL_TAC);;

let GEN_AX_CHAR_VALID = prove
 (`!S p. p IN S ==> CHAR S:(W->bool)#(W->W->bool)->bool |= p`,
  INTRO_TAC "!S p; in_S" THEN REWRITE_TAC[valid; FORALL_PAIR_THM] THEN
  REWRITE_TAC[IN_CHAR] THEN INTRO_TAC "!p1 p2; in_frame char" THEN
  ASM_MESON_TAC[]);;

let GEN_CHAR_VALID = prove
 (`!S H p. [S . H |~ p] /\
           (!q. q IN H ==> CHAR S:(W->bool)#(W->W->bool)->bool |= q)
           ==> CHAR S:(W->bool)#(W->W->bool)->bool |= p`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC MODPROVES_INDUCT THEN
  CONJ_TAC THENL [SIMP_TAC[GEN_KAXIOM_CHAR_VALID]; ALL_TAC] THEN
  CONJ_TAC THENL [SIMP_TAC[GEN_AX_CHAR_VALID]; ALL_TAC] THEN
  CONJ_TAC THENL [MESON_TAC[GEN_KAXIOM_CHAR_VALID]; ALL_TAC] THEN
  CONJ_TAC THENL [MODAL_TAC; ALL_TAC] THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN MODAL_TAC);;

g `!S:form->bool W:(W->bool) R:(W->W->bool).
    ((W,R) IN FRAME /\ !p. [S . {} |~ p] ==> holds_in (W,R) p) <=>
    (W,R) IN CHAR S`;;
e (REPEAT GEN_TAC);;
e (REWRITE_TAC[IN_CHAR]);;
e EQ_TAC;;
 e (INTRO_TAC "In_Frame char");;
 e (ASM_REWRITE_TAC[]);;
 e (INTRO_TAC "!p; p_in_S");;
 e (SUBGOAL_THEN `[S . {} |~ p]` MP_TAC);;
 e (ASM_MESON_TAC[MODPROVES_RULES]);;
 e (ASM_MESON_TAC[]);;
e (INTRO_TAC "In_Frame char");;
e (ASM_REWRITE_TAC[]);;
e (INTRO_TAC "!p; p_teor_S");;
e (SUBGOAL_THEN `CHAR S:(W->bool)#(W->W->bool)->bool |= p` MP_TAC);;
 e (MATCH_MP_TAC GEN_CHAR_VALID);;
 e (ASM_MESON_TAC[NOT_IN_EMPTY]);;
 e (REWRITE_TAC[valid; FORALL_PAIR_THM]);;
 e (INTRO_TAC "char_valid");;
e (SUBGOAL_THEN `(W:W->bool,R:W->W->bool) IN CHAR S` MP_TAC);;
 e (ASM_REWRITE_TAC[IN_CHAR]);;
e (ASM_MESON_TAC[]);;
let CHAR_CAR = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* Frames appropriate to certain axioms sets S: APPR S.                      *)
(* ------------------------------------------------------------------------- *)

let APPR_DEF = new_definition
  `APPR S = {(W:W->bool,R:W->W->bool) |
             (W,R) IN FINITE_FRAME  /\
             !p. [S. {} |~ p] ==> holds_in (W:W->bool,R:W->W->bool) p}`;;

let IN_APPR = prove
 (`!S. (W:W->bool,R:W->W->bool) IN APPR S <=>
       (W,R) IN FINITE_FRAME /\
       !p. [S. {} |~ p] ==> holds_in (W:W->bool,R:W->W->bool) p`,
  REWRITE_TAC[APPR_DEF; IN_ELIM_PAIR_THM]);;

let APPR_CAR = prove
  (`!S:form->bool W:(W->bool) R:(W->W->bool).
     (W,R) IN APPR S <=>
     (W,R) IN CHAR S /\ FINITE W`,
    ASM_REWRITE_TAC[IN_APPR] THEN
    ASM_MESON_TAC[FINITE_FRAME_SUBSET_FRAME; SUBSET; CHAR_CAR;
                  IN_FINITE_FRAME; IN_CHAR; IN_FRAME]);;

let APPR_EQ_CHAR_FINITE = prove
  (`!S. APPR S : (W->bool)#(W->W->bool)->bool = CHAR S INTER FINITE_FRAME`,
   GEN_TAC THEN
   REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; APPR_CAR; IN_INTER;
               IN_FINITE_FRAME; IN_CHAR; IN_FRAME; NOT_IN_EMPTY] THEN
   REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

g `!S:form->bool. APPR S:(W->bool)#(W->W->bool)->bool SUBSET CHAR S`;;
e (REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_APPR]);;
e (INTRO_TAC "!S p1 p2; In_Fin_Frame Appr");;
e (CLAIM_TAC "In_Frame" `(p1:W->bool, p2:W->W->bool) IN FRAME`);;
  e (ASM_MESON_TAC[SUBSET; FINITE_FRAME_SUBSET_FRAME]);;
e (MP_TAC CHAR_CAR);;
e (DISCH_TAC);;
e (ASM_MESON_TAC[CHAR_CAR]);;
let APPR_SUBSET_CHAR = top_thm();;

let GEN_APPR_VALID = prove
  (`!S p. [S. {} |~ p] ==> APPR S:(W->bool)#(W->W->bool)->bool |= p`,
   INTRO_TAC "!S p; Steor_p" THEN REWRITE_TAC[valid; FORALL_PAIR_THM;] THEN
   REPEAT GEN_TAC THEN ASM_REWRITE_TAC[IN_APPR] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Standard Frame.                                                           *)
(* ------------------------------------------------------------------------- *)

let GEN_STANDARD_FRAME_DEF = new_definition
  `GEN_STANDARD_FRAME S p =
   APPR S INTER
   {(W,R) | W = {w | MAXIMAL_CONSISTENT S p w /\
            (!q. MEM q w ==> q SUBSENTENCE p)} /\
            (!q w. Box q SUBFORMULA p /\ w IN W
                   ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))}`;;

let IN_GEN_STANDARD_FRAME = prove
 (`(W,R) IN GEN_STANDARD_FRAME S p <=>
   W = {w | MAXIMAL_CONSISTENT S p w /\
            (!q. MEM q w ==> q SUBSENTENCE p)} /\
   (W,R) IN APPR S /\
   (!q w. Box q SUBFORMULA p /\ w IN W
          ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`,
  REWRITE_TAC[GEN_STANDARD_FRAME_DEF; IN_INTER; IN_ELIM_PAIR_THM] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Standard Model.                                                           *)
(* ------------------------------------------------------------------------- *)

let GEN_STANDARD_MODEL_DEF = new_definition
  `GEN_STANDARD_MODEL S p (W,R) V <=>
   (W,R) IN GEN_STANDARD_FRAME S p /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`;;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let GEN_TRUTH_LEMMA = prove
 (`!S W R p V q.
     ~ [S . {} |~ p] /\
     GEN_STANDARD_MODEL S p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GEN_STANDARD_MODEL_DEF; IN_GEN_STANDARD_FRAME;
              SUBSENTENCE_CASES; IN_APPR] THEN
  INTRO_TAC "np ((W (2 Appr) 1) val) q" THEN REMOVE_THEN "W" SUBST_VAR_TAC THEN
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
     `[S . {} |~ (CONJLIST w --> q1)] \/
      [S . {} |~ CONJLIST w --> Not q1]` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
    ASM_MESON_TAC[MLK_imp_swap; MLK_add_assum];
    ALL_TAC] THEN
   CLAIM_TAC "hq2 | hq2"
     `[S . {} |~ (CONJLIST w --> q2)] \/
      [S . {} |~ (CONJLIST w --> Not q2)]` THENL
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
   HYP_TAC "2" (REWRITE_RULE[IN_FINITE_FRAME; IN_ELIM_THM]) THEN
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
  ]);;

(* ------------------------------------------------------------------------- *)
(* Standard Relation.                                                        *)
(* ------------------------------------------------------------------------- *)

let GEN_STANDARD_REL = new_definition
  `GEN_STANDARD_REL S p w x <=>
   MAXIMAL_CONSISTENT S p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT S p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)`;;

g `!S p. ~ [S. {} |~ p]
         ==> ({M | MAXIMAL_CONSISTENT S p M /\
                   (!q. MEM q M ==> q SUBSENTENCE p)},
              GEN_STANDARD_REL S p)
             IN FINITE_FRAME`;;
e (INTRO_TAC "!S p; p");;
e (REWRITE_TAC[IN_FINITE_FRAME]);;
e CONJ_TAC;; (* non empty *)
 e (REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM]);;
 e (ASM_MESON_TAC[NONEMPTY_MAXIMAL_CONSISTENT]);;
e CONJ_TAC;; (* well define *)
 e (REWRITE_TAC[GEN_STANDARD_REL]);;
 e (SET_TAC[]);;
e (MATCH_MP_TAC FINITE_SUBSET);; (* finite *)
e (EXISTS_TAC `{l | NOREPETITION l /\
                    !q. MEM q l ==> q IN {q | q SUBSENTENCE p}}`);;
e (CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[MAXIMAL_CONSISTENT]]);;
e (MATCH_MP_TAC FINITE_NOREPETITION);;
e (POP_ASSUM_LIST (K ALL_TAC));;
e (SUBGOAL_THEN `{q | q SUBSENTENCE p} =
                 {q | q SUBFORMULA p} UNION IMAGE (Not) {q | q SUBFORMULA p}`
     SUBST1_TAC);;
 e (REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_UNION;
                FORALL_IN_GSPEC; FORALL_IN_IMAGE]);;
 e (REWRITE_TAC[IN_UNION; IN_ELIM_THM; SUBSENTENCE_RULES]);;
 e GEN_TAC;;
 e (GEN_REWRITE_TAC LAND_CONV [SUBSENTENCE_CASES]);;
 e (ASM SET_TAC[]);;
e (REWRITE_TAC[FINITE_UNION; FINITE_SUBFORMULA]);;
e (MATCH_MP_TAC FINITE_IMAGE);;
e (REWRITE_TAC[FINITE_SUBFORMULA]);;
let GEN_FINITE_FRAME_MAXIMAL_CONSISTENT = top_thm();;

g `!p l. MEM p (FLATMAP (\x. match x with Box c -> [c] | _ -> []) l)
         ==> MEM (Box p) l`;;
e GEN_TAC;;
e LIST_INDUCT_TAC;;
 e (REWRITE_TAC[MEM; FLATMAP]);;
e (PURE_REWRITE_TAC[FLATMAP]);;
e (PURE_REWRITE_TAC[MEM_APPEND]);;
e (PURE_ONCE_REWRITE_TAC[MESON[]
     `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`]);;
e CONJ_TAC;;
 r 1;;
 e (ASM IMP_REWRITE_TAC[MEM]);;
e (REWRITE_TAC[MEM]);;
e (ASSUME_TAC (MATCH_CONV `match h with Box c -> [c] | _ -> []`));;
e (REMOVE_THEN "" MP_TAC THEN COND_CASES_TAC);;
 e (POP_ASSUM (CHOOSE_THEN SUBST_VAR_TAC));;
 e (ASM_REWRITE_TAC[MEM]);;
 e (MESON_TAC[]);;
e STRIP_TAC;;
e (FIRST_X_ASSUM(SUBST1_TAC));;
e (REWRITE_TAC[MEM]);;
let MEM_FLATMAP_LEMMA = top_thm();;

let MEM_FLATMAP_LEMMA_2 = prove
 (`!p l. MEM p (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) l) <=>
         (?q. p = Box q /\ MEM p l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; FLATMAP] THEN
  REWRITE_TAC[MEM_APPEND] THEN ASM_CASES_TAC `?c. h = Box c` THENL
  [POP_ASSUM (CHOOSE_THEN SUBST_VAR_TAC) THEN ASM_REWRITE_TAC[MEM] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `~ MEM p (match h with Box c -> [Box c] | _ -> [])`
    (fun th -> ASM_REWRITE_TAC[th]) THENL
  [POP_ASSUM MP_TAC THEN STRUCT_CASES_TAC (SPEC `h:form` (cases "form")) THEN
   REWRITE_TAC[MEM; distinctness "form"; injectivity "form"] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  POP_ASSUM (fun th -> MESON_TAC[th]));;

g `!S p w q.
     ~ [S . {} |~ p] /\
     MAXIMAL_CONSISTENT S p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     Box q SUBFORMULA p /\
     ~MEM (Box q) w
     ==> ?X. MAXIMAL_CONSISTENT S p X /\
             (!q. MEM q X ==> q SUBSENTENCE p) /\
             CONS (Not q)
                  (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)
               SUBLIST X`;;
e (INTRO_TAC "!S p w q; p maxw subw boxq contra");;
e (CLAIM_TAC "consistent_X"
     `CONSISTENT S (CONS (Not q)
                          (FLATMAP (\x. match x with Box c -> [c] | _ -> [])
                                   w))`);;
 e (REFUTE_THEN MP_TAC);;
 e (INTRO_TAC "PA");;
 e (SUBGOAL_THEN `MEM (Box q) w ==> F` (fun(th) -> (MATCH_MP_TAC th)));;
  e (ASM_MESON_TAC[]);;
 e (REMOVE_THEN "PA" MP_TAC THEN REWRITE_TAC[CONSISTENT]);;
 e (INTRO_TAC "PA");;
 e (SUBGOAL_THEN
     `[S . {}
       |~ CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
          --> Box q] /\
      (!c. MEM c (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)
           ==> MEM (Box c) w ) /\
      Box q SUBSENTENCE p
      ==> MEM (Box q) w`
     (fun th -> MATCH_MP_TAC th));;
   e (REPEAT STRIP_TAC);;
   e (MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA);;
   e (EXISTS_TAC `S: form->bool `);;
   e (MAP_EVERY EXISTS_TAC[`p:form`;
        `FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w`]);;
   e (ASM_REWRITE_TAC[MEM_FLATMAP_LEMMA_2]);;
   e GEN_TAC;;
   e (INTRO_TAC "@y. a b");;
   e (ASM_REWRITE_TAC[]);;
 e (ASM IMP_REWRITE_TAC[MEM_FLATMAP_LEMMA; SUBFORMULA_IMP_SUBSENTENCE]);;
 e (MATCH_MP_TAC MLK_imp_trans);;
 e (EXISTS_TAC
     `CONJLIST (MAP (Box)
                    (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w))`);;
 e (REWRITE_TAC[CONJLIST_FLATMAP_DOT_BOX_LEMMA]);;
 e (MATCH_MP_TAC MKL_CONJLIST_BOX_IMP_BOX);;
 e (REMOVE_THEN "PA" MP_TAC);;
 e (REWRITE_TAC[MLK_not_def]);;
 e (REWRITE_TAC[CONJLIST_CONS_NOT_TH]);;
 e (MESON_TAC[MLK_NOT_IMP_ID_5]);;
 e (MP_TAC (SPECL
              [`S:form->bool`; `p:form`;
               `CONS (Not q)
                     (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)`]
           EXTEND_MAXIMAL_CONSISTENT));;
e ANTS_TAC;;
e (ASM_REWRITE_TAC[MEM]);;
e (GEN_TAC THEN STRIP_TAC);;
e (FIRST_X_ASSUM SUBST_VAR_TAC);;
e (MATCH_MP_TAC SUBFORMULA_IMP_NEG_SUBSENTENCE);;
e (HYP MESON_TAC "boxq"
     [SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
e (CLAIM_TAC "boxq'" `MEM (Box q') (w:(form)list)`);;
e (MATCH_MP_TAC MEM_FLATMAP_LEMMA);;
e (ASM_REWRITE_TAC[]);;
e (CLAIM_TAC "boxq'sub" `Box (q':form) SUBSENTENCE p`);;
e (ASM_MESON_TAC[]);;
e (HYP_TAC "boxq'sub" (REWRITE_RULE[SUBSENTENCE_CASES; distinctness "form"]));;
e (MATCH_MP_TAC SUBFORMULA_IMP_SUBSENTENCE);;
e (HYP MESON_TAC "boxq'sub"
     [SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
e (INTRO_TAC "@X. maxX subX subl" THEN EXISTS_TAC `X:form list`);;
e (ASM_REWRITE_TAC[NOT_IMP]);;
let GEN_XK_FOR_ACCESSIBILITY_LEMMA = top_thm() ;;

g `!S p w q.
     ~ [S . {} |~ p] /\
     MAXIMAL_CONSISTENT S p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     Box q SUBFORMULA p /\
     ~MEM (Box q) w /\
     MAXIMAL_CONSISTENT S p X /\
     (!q. MEM q X ==> q SUBSENTENCE p) /\
     CONS (Not q)
          (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w) SUBLIST X
     ==> GEN_STANDARD_REL S p w X /\ ~MEM q X`;;
e (INTRO_TAC "!S p w q; p maxw subw boxq contra maxX subX subl");;
e (ASM_REWRITE_TAC[GEN_STANDARD_REL]);;
e CONJ_TAC;;
e (INTRO_TAC "!B; B");;
e (HYP_TAC "subl" (REWRITE_RULE[SUBLIST]));;
e (REMOVE_THEN "subl" MATCH_MP_TAC);;
e (REWRITE_TAC[MEM; distinctness "form"; injectivity "form"]);;
e (DISJ2_TAC THEN REWRITE_TAC[MEM_FLATMAP]);;
e (EXISTS_TAC `Box B`);;
e (ASM_REWRITE_TAC[MEM]);;
e (HYP_TAC "subl" (REWRITE_RULE[SUBLIST]));;
e (HYP_TAC "subl: +" (SPEC `Not q` o REWRITE_RULE[SUBLIST]));;
e (IMP_REWRITE_TAC[GSYM MAXIMAL_CONSISTENT_MEM_NOT]);;
e STRIP_TAC;;
e CONJ_TAC;;
r 1;;
e (MATCH_MP_TAC SUBFORMULA_TRANS);;
e (EXISTS_TAC `Box (q:form)`);;
e (ASM_REWRITE_TAC[]);;
e (ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
r 1;;
e (REMOVE_THEN "" MATCH_MP_TAC THEN REWRITE_TAC[MEM]);;
let GEN_ACCESSIBILITY_LEMMA = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* General Lemmata for Completeness Theorems.                                *)
(* ------------------------------------------------------------------------- *)

g `!S W R V M p. ~ [S . {} |~ p] /\
                 MAXIMAL_CONSISTENT S p M /\
                 MEM (Not p) M /\
                 (!q. MEM q M ==> q SUBSENTENCE p) /\
                 GEN_STANDARD_MODEL S p (W,R) V
                 ==> ~holds (W,R) V p M`;;
e (REPEAT GEN_TAC);;
e (INTRO_TAC "p_not_theor max_cons_M mem_notp q_subs_p standard_model");;
e (MP_TAC (ISPECL [`S: form ->bool`;
                   `W: (form)list->bool`;
                   `R: (form)list-> (form)list ->bool`;
                   `p:form`;
                   `V:((char)list->(form)list->bool)`;
                   `p:form`] GEN_TRUTH_LEMMA));;
e ANTS_TAC;;
e (ASM_REWRITE_TAC[SUBFORMULA_REFL]);;
e (DISCH_THEN (MP_TAC o SPEC `M:form list`));;
e ANTS_TAC;;
e (HYP_TAC "standard_model"
     (REWRITE_RULE[GEN_STANDARD_MODEL_DEF; IN_GEN_STANDARD_FRAME]));;
e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (DISCH_THEN (SUBST1_TAC o GSYM));;
e (ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT_NC]);;
let GEN_COUNTERMODEL = top_thm();;

g `!S W R p. ~ [S . {} |~ p] /\
             (W,R) IN GEN_STANDARD_FRAME S p
             ==> ~holds_in (W,R) p`;;
e (INTRO_TAC "!S W R p; p_not_theor in_standard_frame");;
e (REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP; IN_ELIM_THM]);;
e (EXISTS_TAC `\a M. Atom a SUBFORMULA p /\ MEM (Atom a) M`);;
e (DESTRUCT_TAC "@M. max mem subf"
     (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ [S . {} |~ p]`)));;
e (EXISTS_TAC `M:form list` THEN ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `GEN_STANDARD_MODEL S p (W,R) (\a M. Atom a SUBFORMULA p /\
                 MEM (Atom a) M) ` MP_TAC);;
e (ASM_MESON_TAC[GEN_STANDARD_MODEL_DEF]);;
e (INTRO_TAC "standard_model");;
e CONJ_TAC;;
e (HYP_TAC "in_standard_frame" (REWRITE_RULE[IN_GEN_STANDARD_FRAME]));;
e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (MATCH_MP_TAC GEN_COUNTERMODEL);;
e (EXISTS_TAC `S:form -> bool`);;
e (ASM_REWRITE_TAC[]);;
let GEN_COUNTERMODEL_ALT = top_thm();;

(* ------------------------------------------------------------------------- *)
(* General Lemma for Completeness Theorems on a generic (infinite) domain.   *)
(* ------------------------------------------------------------------------- *)

g `!S. INFINITE (:A)
       ==> !p. APPR S:(A->bool)#(A->A->bool)->bool |= p
            ==> APPR S:(form list->bool)#(form list->form list->bool)->bool
                  |= p`;;
e (INTRO_TAC "!S; A" THEN MATCH_MP_TAC BISIMILAR_VALID);;
e (REWRITE_TAC[IN_APPR]);;
e (REPEAT GEN_TAC THEN INTRO_TAC "(finite1 Appr) w1");;
e (CLAIM_TAC "@f. inj" `?f:form list->A. (!x y. f x = f y ==> x = y)`);;
 e (SUBGOAL_THEN `(:form list) <=_c (:A)` MP_TAC);;
  e (TRANS_TAC CARD_LE_TRANS `(:num)`);;
  e (ASM_REWRITE_TAC[GSYM INFINITE_CARD_LE; GSYM COUNTABLE_ALT]);;
  e (ASM_SIMP_TAC[COUNTABLE_LIST; COUNTABLE_FORM]);;
 e (REWRITE_TAC[le_c; IN_UNIV]);;
e (CLAIM_TAC "f_in_IMAGE"
     `!x. x IN W1 ==> f x IN IMAGE (f:form list->A) (W1:form list->bool)`);;
 e (MESON_TAC[FUN_IN_IMAGE]);;
e (CLAIM_TAC "sur"
     `!y. y IN IMAGE (f:form list->A) (W1:form list->bool)
          ==> (?!x. x IN W1 /\ f x = y)`);;
 e (ASM_REWRITE_TAC[IN_IMAGE]);;
 e (INTRO_TAC "!y; (@x. sur_im)");;
 e (ASM_REWRITE_TAC[EXISTS_UNIQUE_DEF]);;
 e CONJ_TAC;;
  e (EXISTS_TAC `x:form list`);;
  e (ASM_REWRITE_TAC[]);;
 e (ASM_MESON_TAC[]);;
e (CLAIM_TAC "@g. im invdx invsx"
     `?g. (!y. y IN IMAGE (f:form list->A) (W1:form list->bool)
               ==> g y IN W1) /\
          (!y. y IN IMAGE f W1 ==> f (g y) = y) /\
          (!x. x IN W1 ==> g (f x) = x)`);;
 e (ASM_MESON_TAC[BIJECTIVE_INVERSES]);;
e (MAP_EVERY EXISTS_TAC
     [`IMAGE (f:form list->A) W1`;
      `\x y:A. ?a b:form list.
         a IN W1 /\ b IN W1 /\ x = f a /\ y = f b /\ R1 a b`;
      `\a:string w:A. ?x:form list. w = f x /\ V1 a x`;
      `f (w1:form list):A`]);;
e CONJ_TAC;;
 e (REWRITE_TAC[IN_FINITE_FRAME]);;
 e (REPEAT CONJ_TAC);;
  (* 1 *)
  e (HYP SET_TAC "w1" []);;
  e (SET_TAC[]);;
  (* 2 *)
  e (ASM_MESON_TAC[IN_FINITE_FRAME; FINITE_IMAGE]);;
  (* 3 *)
  e (INTRO_TAC "!p; p");;
  e (ASM_REWRITE_TAC[holds_in]);;
  e (REPEAT GEN_TAC);;
  e DISCH_TAC;;
  e (CLAIM_TAC "p_holds" `holds_in (W1:form list->bool,R1) p`);;
   e (ASM_MESON_TAC[]);;
  e (CLAIM_TAC "@V1.bis"
     `?V1. BISIMILAR (IMAGE (f:form list->A) W1,
                      (\x y:A. ?a b:form list.
                         a IN W1 /\ b IN W1 /\ x = f a /\ y = f b /\ R1 a b),
                      V)
                     ((W1:form list->bool),R1, V1)
                     (w:A) ((g:A->form list) (w:A))`);;
   e (EXISTS_TAC
        `\a:char list w:form list. V a ((f:form list -> A) w):bool`);;
   e (REWRITE_TAC[BISIMILAR]);;
   e (EXISTS_TAC `\w:A w1:form list. w1 IN W1 /\ (f:form list->A) w1 = w`);;
   e (ASM_REWRITE_TAC[BISIMIMULATION]);;
   e (REWRITE_TAC[EXISTS_IN_IMAGE]);;
   e CONJ_TAC;;
    e (REPEAT GEN_TAC THEN STRIP_TAC);;
    e (FIRST_X_ASSUM SUBST_VAR_TAC);;
    e (ASM_SIMP_TAC[FUN_IN_IMAGE]);;
    e CONJ_TAC;;
     e (HYP MESON_TAC "inj" []);;
     e (ASM_MESON_TAC[IN_FINITE_FRAME]);;
  e CONJ_TAC;;
   e (ASM_MESON_TAC[]);;
   e (ASM_MESON_TAC[]);;
 e (MP_TAC (ISPECL [`IMAGE (f:form list->A) W1`;
                    `\x y:A. ?a b:form list.
                       a IN W1 /\ b IN W1 /\ x = f a /\ y = f b /\ R1 a b`;
                    `V:char list->A->bool`;
                    `W1:form list->bool`;
                    `R1:form list->form list->bool`;
                    `V1:char list-> form list->bool`;
                    `w:A`;
                    `(g:A->form list) w`]
                   BISIMILAR_HOLDS));;
  e ANTS_TAC;;
   e (ASM_MESON_TAC[]);;
 e DISCH_TAC;;
 e (CLAIM_TAC "p_holds"
      `holds (W1:form list->bool,R1) V1 p ((g:A->form list) w)`);;
  e (HYP_TAC "p_holds" (REWRITE_RULE[holds_in]));;
  e (CLAIM_TAC "gw_in_W1" `(g:A-> form list) w IN W1 `);;
   e (ASM_MESON_TAC[]);;
  e (ASM_MESON_TAC[]);;
 e (ASM_MESON_TAC[]);;
e (REWRITE_TAC[BISIMILAR]);;
e (EXISTS_TAC `\w1:form list w2:A. w1 IN W1 /\ w2 = f w1`);;
e (ASM_REWRITE_TAC[BISIMIMULATION]);;
e (REMOVE_THEN "w1" (K ALL_TAC));;
e (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC);;
e (ASM_SIMP_TAC[FUN_IN_IMAGE]);;
e CONJ_TAC;;
 e (HYP MESON_TAC "inj" []);;
e CONJ_TAC;;
 e (REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_IN_IMAGE]);;
 e (ASM_MESON_TAC[IN_FINITE_FRAME]);;
e (ASM_MESON_TAC[]);;
let GEN_LEMMA_FOR_GEN_COMPLETENESS = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* Invariance by permutation.                                                *)
(* ------------------------------------------------------------------------- *)

let SET_OF_LIST_EQ_IMP_MEM = prove
 (`!l m x:A. set_of_list l = set_of_list m /\ MEM x l ==> MEM x m`,
  REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN MESON_TAC[]);;

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

let SET_OF_LIST_EQ_STANDARD_REL = prove
 (`!S p u1 u2 w1 w2.
     set_of_list u1 = set_of_list w1 /\ NOREPETITION w1 /\
     set_of_list u2 = set_of_list w2 /\ NOREPETITION w2 /\
     GEN_STANDARD_REL S p u1 u2
     ==> GEN_STANDARD_REL S p w1 w2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GEN_STANDARD_REL] THEN STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]; ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]);;

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
e STRIP_TAC;;
e CONJ_TAC;;
e (MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[]);;
e CONJ_TAC;;
e (ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]);;
e CONJ_TAC;;
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
e GEN_TAC;;
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
