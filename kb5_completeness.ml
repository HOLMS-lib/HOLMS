(* ========================================================================= *)
(* Proof of the axioms and frame correspondence for KB5.                     *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025-2026.                             *)
(* ========================================================================= *)

needs "HOLMS/gen_completeness.ml";;

(* ------------------------------------------------------------------------- *)
(*  Axiomatisation KB5                                                       *)
(* ------------------------------------------------------------------------- *)

let KB5_AX = new_definition
  `KB5_AX = {B_SCHEMA p | p IN (:form)} UNION
            {FIVE_SCHEMA p | p IN (:form)}`;;

let B_IN_KB5_AX = prove
 (`!q. q --> Box Diam q IN KB5_AX`,
  REWRITE_TAC[KB5_AX; B_SCHEMA_DEF; FIVE_SCHEMA_DEF; IN_ELIM_THM;
              IN_UNIV; IN_UNION] THEN
  MESON_TAC[]);;

let FIVE_IN_KB5_AX = prove
 (`!q. Diam q --> Box Diam q IN KB5_AX`,
  REWRITE_TAC[KB5_AX; B_SCHEMA_DEF; FIVE_SCHEMA_DEF; IN_ELIM_THM;
              IN_UNIV; IN_UNION] THEN
  MESON_TAC[]);;

let KB5_AX_B = prove
 (`!q. [KB5_AX. {} |~ (q --> Box Diam q)]`,
  MESON_TAC[MODPROVES_RULES; B_IN_KB5_AX]);;

let KB5_AX_FIVE = prove
 (`!q. [KB5_AX. {} |~ (Diam q --> Box Diam q)]`,
  MESON_TAC[MODPROVES_RULES; FIVE_IN_KB5_AX]);;

(* ------------------------------------------------------------------------- *)
(*  Axiomatisation K4B                                                       *)
(* ------------------------------------------------------------------------- *)

let K4B_AX = new_definition
  `K4B_AX = {B_SCHEMA p | p IN (:form)} UNION
            {FOUR_SCHEMA p | p IN (:form)}`;;

let B_IN_K4B_AX = prove
 (`!q. q --> Box Diam q IN K4B_AX`,
  REWRITE_TAC[K4B_AX; B_SCHEMA_DEF; FOUR_SCHEMA_DEF; IN_ELIM_THM;
              IN_UNIV; IN_UNION] THEN
  MESON_TAC[]);;

let FOUR_IN_K4B_AX = prove
 (`!q. Box q --> Box Box q IN K4B_AX`,
  REWRITE_TAC[K4B_AX; B_SCHEMA_DEF; FOUR_SCHEMA_DEF; IN_ELIM_THM;
              IN_UNIV; IN_UNION] THEN
  MESON_TAC[]);;

let K4B_AX_B = prove
 (`!q. [K4B_AX. {} |~ (q --> Box Diam q)]`,
  MESON_TAC[MODPROVES_RULES; B_IN_K4B_AX]);;

let K4B_AX_FOUR = prove
 (`!q. [K4B_AX. {} |~ (Box q --> Box Box q)]`,
  MESON_TAC[MODPROVES_RULES; FOUR_IN_K4B_AX]);;

(* ------------------------------------------------------------------------- *)
(*  Equivalence between the two axiomatisations                              *)
(* ------------------------------------------------------------------------- *)

let KB5_AX_FOUR = prove
 (`!q. [KB5_AX . {} |~ (Box q --> Box Box q)]`,
  GEN_TAC THEN
  MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `Box Diam (Box q)` THEN
  CONJ_TAC THENL
  [MATCH_ACCEPT_TAC (ISPEC `Box q` KB5_AX_B);
   MATCH_MP_TAC MLK_imp_box THEN
   CLAIM_TAC "contra_five_instance"
    `[KB5_AX . {} |~ Not Box Diam Not q --> Not Diam Not q]` THENL
   [ASM_MESON_TAC[MLK_contrapos_eq; KB5_AX_FIVE];
    HYP_TAC "contra_five_instance" (REWRITE_RULE[diam_DEF]) THEN
    ASM_REWRITE_TAC[diam_DEF] THEN
    ASM_MESON_TAC[MLK_not_not_th; MLK_imp_mp_subst;
                  MLK_iff_refl_th; MLK_iff_sym;
                  MLK_not_subst; MLK_box_subst]]]);;

let K4B_AX_DUAL_FOUR = prove
 (`!q. [K4B_AX . {} |~ (Diam (Diam q) --> Diam q)]`,
  GEN_TAC THEN REWRITE_TAC[diam_DEF] THEN
  MATCH_MP_TAC (ISPECL
   [`Not Box Box (Not q)`;
    `Not Box Not (Not Box Not q)`;
    `Not Box (Not q)`;
    `Not Box Not q`] MLK_imp_mp_subst) THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC MLK_not_subst THEN
   MATCH_MP_TAC MLK_box_subst THEN
   ASM_MESON_TAC[MLK_not_not_th; MLK_iff_sym];
   MATCH_ACCEPT_TAC MLK_iff_refl_th;
   MATCH_MP_TAC MLK_contrapos THEN
   MATCH_ACCEPT_TAC (ISPEC `Not q` K4B_AX_FOUR)]);;

let K4B_AX_FIVE = prove
 (`!q. [K4B_AX . {} |~ (Diam q --> Box Diam q)]`,
  GEN_TAC THEN MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `Box Diam (Diam q)` THEN
  CONJ_TAC THENL
  [MATCH_ACCEPT_TAC (ISPEC `Diam q` K4B_AX_B);
   MATCH_MP_TAC MLK_imp_box THEN
   MATCH_ACCEPT_TAC (ISPEC `q:form` K4B_AX_DUAL_FOUR)]);;

let KB5_PROVES_K4B = prove
 (`!H p. [KB5_AX . H |~ p] ==> [K4B_AX . H |~ p]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!H p. [KB5_AX . H |~ p] ==> [K4B_AX . H |~ p]` MP_TAC THENL
  [MATCH_MP_TAC MODPROVES_INDUCT THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[MODPROVES_RULES];
    REWRITE_TAC[KB5_AX; IN_UNION; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[B_SCHEMA_DEF; FIVE_SCHEMA_DEF] THEN
    REWRITE_TAC[GSYM MODPROVES_DEDUCTION_LEMMA] THEN
    ASM_MESON_TAC[MODPROVES_RULES; K4B_AX_B; K4B_AX_FIVE;
                  MODPROVES_MONO2; EMPTY_SUBSET; MODPROVES_HP];
    MESON_TAC[MODPROVES_RULES];
    MESON_TAC[MODPROVES_RULES];
    MESON_TAC[MODPROVES_RULES]];
   DISCH_THEN (MP_TAC o SPECL [`H:form->bool`; `p:form`]) THEN
   ASM_REWRITE_TAC[]]);;

let K4B_PROVES_KB5 = prove
 (`!H p. [K4B_AX . H |~ p] ==> [KB5_AX . H |~ p]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!H p. [K4B_AX . H |~ p] ==> [KB5_AX . H |~ p]` MP_TAC THENL
  [MATCH_MP_TAC MODPROVES_INDUCT THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[MODPROVES_RULES];
    REWRITE_TAC[K4B_AX; IN_UNION; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[B_SCHEMA_DEF; FOUR_SCHEMA_DEF] THEN
    REWRITE_TAC[GSYM MODPROVES_DEDUCTION_LEMMA] THEN
    ASM_MESON_TAC[MODPROVES_RULES; KB5_AX_B; KB5_AX_FOUR;
                  MODPROVES_MONO2; EMPTY_SUBSET; MODPROVES_HP];
    MESON_TAC[MODPROVES_RULES];
    MESON_TAC[MODPROVES_RULES];
    MESON_TAC[MODPROVES_RULES]];
   DISCH_THEN (MP_TAC o SPECL [`H:form->bool`; `p:form`]) THEN
   ASM_REWRITE_TAC[]]);;

let KB5_K4B_EQ = prove
 (`!H p. [KB5_AX . H |~ p] <=> [K4B_AX . H |~ p]`,
  MESON_TAC[KB5_PROVES_K4B; K4B_PROVES_KB5]);;

(* ------------------------------------------------------------------------- *)
(* Symmetric-Euclidean frames.                                               *)
(* ------------------------------------------------------------------------- *)

let EUSYM_DEF = new_definition
  `EUSYM =
   {(W:W->bool,R:W->W->bool) |
    (W,R) IN FRAME /\
    EUCLIDEAN W R /\
    SYMMETRIC W R}`;;

let IN_EUSYM = prove
 (`(W:W->bool,R:W->W->bool) IN EUSYM <=>
   (W,R) IN FRAME /\
   EUCLIDEAN W R /\
   SYMMETRIC W R`,
  REWRITE_TAC[EUSYM_DEF; IN_ELIM_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory: Symmetric-Euclidean Frames characterize KB5.       *)
(* ------------------------------------------------------------------------- *)

let EUSYM_CHAR_KB5 = prove
 (`EUSYM:(W->bool)#(W->W->bool)->bool = CHAR KB5_AX`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN
  REWRITE_TAC[IN_CHAR; IN_EUSYM] THEN
  REWRITE_TAC[KB5_AX; FORALL_IN_UNION; FORALL_IN_GSPEC;
              MODAL_SYM; MODAL_EUCL; IN_UNIV] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Transitive-symmetric frames.                                              *)
(* ------------------------------------------------------------------------- *)

let TSYM_DEF = new_definition
  `TSYM =
   {(W:W->bool,R:W->W->bool) |
    (W,R) IN FRAME /\
    TRANSITIVE W R /\
    SYMMETRIC W R}`;;

let IN_TSYM = prove
 (`(W:W->bool,R:W->W->bool) IN TSYM <=>
   (W,R) IN FRAME /\
   TRANSITIVE W R /\
   SYMMETRIC W R`,
  REWRITE_TAC[TSYM_DEF; IN_ELIM_PAIR_THM]);;

let EUCL_SYM_EQ_TRANS_SYM = prove
 (`!W:W->bool R. (EUCLIDEAN W R /\ SYMMETRIC W R) <=>
                 (TRANSITIVE W R /\ SYMMETRIC W R)`,
  REWRITE_TAC[EUCLIDEAN; TRANSITIVE; SYMMETRIC] THEN MESON_TAC[]);;

let TSYM_EUSYM = prove
 (`TSYM:(W->bool)#(W->W->bool)->bool = EUSYM`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_TSYM; IN_EUSYM;
              EUCL_SYM_EQ_TRANS_SYM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory: Transitive-Symmetric Frames characterize K4B.      *)
(* ------------------------------------------------------------------------- *)

let TSYM_CHAR_K4B = prove
 (`TSYM:(W->bool)#(W->W->bool)->bool = CHAR K4B_AX`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_CHAR; IN_TSYM; K4B_AX;
              FORALL_IN_UNION; FORALL_IN_GSPEC; MODAL_TRANS; MODAL_SYM;
              IN_UNIV] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness                                                        *)
(* ------------------------------------------------------------------------- *)

let K4B_TSYM_VALID = prove
 (`!H p. [K4B_AX . H |~ p] /\
         (!q. q IN H ==> TSYM:(W->bool)#(W->W->bool)->bool |= q)
         ==> TSYM:(W->bool)#(W->W->bool)->bool |= p`,
  ASM_MESON_TAC[GEN_CHAR_VALID; TSYM_CHAR_K4B]);;

let KB5_EUSYM_VALID = prove
 (`!H p. [KB5_AX . H |~ p] /\
         (!q. q IN H ==> EUSYM:(W->bool)#(W->W->bool)->bool |= q)
         ==> EUSYM:(W->bool)#(W->W->bool)->bool |= p`,
  ASM_MESON_TAC[GEN_CHAR_VALID; EUSYM_CHAR_KB5]);;

(* ------------------------------------------------------------------------- *)
(* Finite symmetric-Euclidean frames are appropriate for KB5.                *)
(* ------------------------------------------------------------------------- *)

let ESF_DEF = new_definition
  `ESF =
   {(W:W->bool,R:W->W->bool) |
    (W,R) IN FINITE_FRAME /\
    EUCLIDEAN W R /\
    SYMMETRIC W R}`;;

let IN_ESF = prove
 (`(W:W->bool,R:W->W->bool) IN ESF <=>
   (W,R) IN FINITE_FRAME /\
   EUCLIDEAN W R /\
   SYMMETRIC W R`,
  REWRITE_TAC[ESF_DEF; IN_ELIM_PAIR_THM]);;

let ESF_FIN_EUSYM = prove
 (`ESF:(W->bool)#(W->W->bool)->bool = EUSYM INTER FINITE_FRAME`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_INTER; IN_ESF;
              IN_FINITE_FRAME; IN_EUSYM; IN_FRAME] THEN
  MESON_TAC[FINITE_FRAME_SUBSET_FRAME; SUBSET]);;

let ESF_APPR_KB5 = prove
 (`ESF:(W->bool)#(W->W->bool)->bool = APPR KB5_AX`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; APPR_CAR; ESF_FIN_EUSYM;
              EUSYM_CHAR_KB5; IN_INTER; IN_CHAR;
              IN_FINITE_FRAME_INTER] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Finite transitive-symmetric frames are appropriate for K4B.               *)
(* ------------------------------------------------------------------------- *)

let TSF_DEF = new_definition
  `TSF =
   {(W:W->bool,R:W->W->bool) |
    (W,R) IN FINITE_FRAME /\
    TRANSITIVE W R /\
    SYMMETRIC W R}`;;

let IN_TSF = prove
 (`(W:W->bool,R:W->W->bool) IN TSF <=>
   (W,R) IN FINITE_FRAME /\
   TRANSITIVE W R /\
   SYMMETRIC W R`,
  REWRITE_TAC[TSF_DEF; IN_ELIM_PAIR_THM]);;

let TSF_FIN_TSYM = prove
 (`TSF:(W->bool)#(W->W->bool)->bool = TSYM INTER FINITE_FRAME`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_INTER; IN_TSF;
              IN_FINITE_FRAME; IN_TSYM; IN_FRAME] THEN
  MESON_TAC[FINITE_FRAME_SUBSET_FRAME; SUBSET]);;

let TSF_APPR_K4B = prove
 (`TSF:(W->bool)#(W->W->bool)->bool = APPR K4B_AX`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; APPR_CAR; TSF_FIN_TSYM;
              TSYM_CHAR_K4B; IN_INTER; IN_CHAR;
              IN_FINITE_FRAME_INTER] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Soundness w.r.t. finite frames.                                           *)
(* ------------------------------------------------------------------------- *)

let KB5_ESF_VALID = prove
 (`!p. [KB5_AX . {} |~ p] ==>
       ESF:(W->bool)#(W->W->bool)->bool |= p`,
  MESON_TAC[GEN_APPR_VALID; ESF_APPR_KB5]);;

let K4B_TSF_VALID = prove
 (`!p. [K4B_AX . {} |~ p] ==>
       TSF:(W->bool)#(W->W->bool)->bool |= p`,
  MESON_TAC[GEN_APPR_VALID; TSF_APPR_K4B]);;

(* ------------------------------------------------------------------------- *)
(* Consistency of KB5 and K4B.                                                *)
(* ------------------------------------------------------------------------- *)

let KB5_CONSISTENT = prove
 (`~ [KB5_AX . {} |~ False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`]KB5_ESF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM; IN_ESF;
              IN_FINITE_FRAME; EUCLIDEAN; SYMMETRIC;
              NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. x = 0 /\ x = y`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;

let K4B_CONSISTENT = prove
 (`~ [K4B_AX . {} |~ False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`]K4B_TSF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM; IN_TSF;
              IN_FINITE_FRAME; TRANSITIVE; SYMMETRIC;
              NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. x = 0 /\ x = y`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* KB5 standard worlds, frames, and models.                                   *)
(* ------------------------------------------------------------------------- *)

let KB5_STANDARD_WORLD_DEF = new_definition
  `KB5_STANDARD_WORLD p = GEN_STANDARD_WORLD KB5_AX p`;;

let KB5_STANDARD_FRAME_DEF = new_definition
  `KB5_STANDARD_FRAME p = GEN_STANDARD_FRAME KB5_AX p`;;

let IN_KB5_STANDARD_FRAME = prove
 (`!p W R. (W,R) IN KB5_STANDARD_FRAME p <=>
           W = KB5_STANDARD_WORLD p /\
           (W,R) IN ESF /\
           (!q w. Box q SUBFORMULA p /\ w IN W
                  ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[KB5_STANDARD_FRAME_DEF; IN_GEN_STANDARD_FRAME;
              KB5_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD] THEN
  EQ_TAC THEN MESON_TAC[ESF_APPR_KB5]);;

let KB5_STANDARD_MODEL_DEF = new_definition
  `KB5_STANDARD_MODEL = GEN_STANDARD_MODEL KB5_AX`;;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let KB5_TRUTH_LEMMA = prove
 (`!W R p V q.
     ~ [KB5_AX . {} |~ p] /\
     KB5_STANDARD_MODEL p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REWRITE_TAC[KB5_STANDARD_MODEL_DEF] THEN MESON_TAC[GEN_TRUTH_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Accessibility lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let KB5_STANDARD_REL_DEF = new_definition
  `KB5_STANDARD_REL p w x <=>
   GEN_STANDARD_REL KB5_AX p w x /\
   (!B. MEM (Box B) w ==> MEM (Box B) x) /\
   (!B. MEM (Box B) x ==> MEM B w  /\ MEM (Box B) w)`;;

let KB5_STANDARD_REL_CAR = prove
 (`!p w x.
     KB5_STANDARD_REL p w x <=>
     w IN KB5_STANDARD_WORLD p /\
     x IN KB5_STANDARD_WORLD p /\
     (!B. MEM (Box B) w ==> MEM B x /\ MEM (Box B) x) /\
     (!B. MEM (Box B) x ==> MEM B w /\ MEM (Box B) w)`,
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[KB5_STANDARD_REL_DEF; GEN_STANDARD_REL; 
              IN_ELIM_THM; KB5_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD] THEN
  MESON_TAC[]);;


let ESYF_MAXIMAL_CONSISTENT = prove
 (`!p. ~ [KB5_AX . {} |~ p]
       ==> (KB5_STANDARD_WORLD p,
            KB5_STANDARD_REL p)
           IN ESF `,
  INTRO_TAC "!p; p" THEN
  MP_TAC (ISPECL [`KB5_AX`; `p:form`] GEN_FINITE_FRAME_MAXIMAL_CONSISTENT) THEN
  REWRITE_TAC[IN_FINITE_FRAME] THEN INTRO_TAC "gen_max_cons" THEN
  ASM_REWRITE_TAC[ESF_FIN_EUSYM; IN_INTER; SYM TSYM_EUSYM; IN_TSYM;
                  IN_FINITE_FRAME_INTER; IN_FRAME; TRANSITIVE; SYMMETRIC] THEN
  REWRITE_TAC[TAUT `(P /\ Q /\ R) /\ P /\ S <=> P /\ S /\ Q /\ R`] THEN
  REPEAT CONJ_TAC THENL 
  (* Nonempty *)
  [REWRITE_TAC[KB5_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD] THEN
   ASM_MESON_TAC[]; 
  (* Well-defined *)
   ASM_REWRITE_TAC[KB5_STANDARD_REL_CAR] THEN ASM_MESON_TAC[];
  (* Finite *)
   REWRITE_TAC[KB5_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD] THEN
   ASM_MESON_TAC[];
  (* Transitive *)
  REWRITE_TAC[IN_ELIM_THM; KB5_STANDARD_REL_CAR] THEN 
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
  (* Symmetric *)
  REWRITE_TAC[IN_ELIM_THM; KB5_STANDARD_REL_CAR] THEN 
  INTRO_TAC "!w w'; w w' w w' mem_w mem_w'"  THEN
  ASM_REWRITE_TAC[]]);;

let KB5_ACCESSIBILITY_LEMMA = prove
  (`!p w q.
     ~ [KB5_AX . {} |~ p] /\
     w IN KB5_STANDARD_WORLD p /\
     Box q SUBFORMULA p /\
     (!x. KB5_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`,
   INTRO_TAC "!p w q; p stdw boxq rel" THEN
   HYP_TAC "stdw" (REWRITE_RULE
     [KB5_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD; IN_ELIM_THM]) THEN
   REFUTE_THEN (LABEL_TAC "contra") THEN
   REMOVE_THEN "rel" MP_TAC THEN REWRITE_TAC[NOT_FORALL_THM] THEN
   ABBREV_TAC `X = Not q INSERT
     ({C | Box C IN set_of_list w} UNION
      {Box C | Box C IN set_of_list w} UNION
      {Not Box E | Not E IN set_of_list w /\ Box E SUBSENTENCE p} UNION
      {Not Box E | Not Box E IN set_of_list w})` THEN
    POP_ASSUM (LABEL_TAC "X") THEN
   CLAIM_TAC "subX" `!r. r IN X ==> r SUBSENTENCE p` THENL
   [EXPAND_TAC "X" THEN 
   REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_UNION; FORALL_IN_GSPEC] THEN
   CONJ_TAC THENL
   [SUFFICE_TAC `q SUBFORMULA p` [SUBFORMULA_IMP_NEG_SUBSENTENCE] THEN
    ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION;
                  SUBFORMULA_REFL];
    REPEAT CONJ_TAC THENL
    [INTRO_TAC "!C; boxC" THEN
     MATCH_MP_TAC SUBFORMULA_IMP_SUBSENTENCE THEN
     MATCH_MP_TAC SUBFORMULA_TRANS THEN EXISTS_TAC `Box C` THEN
     REWRITE_TAC[SUBFORMULA_INVERSION; SUBFORMULA_REFL] THEN
     SUFFICE_TAC `Box C SUBSENTENCE p`
      [SUBSENTENCE_CASES; form_DISTINCT] THEN
     HYP MESON_TAC "stdw boxC" [IN_SET_OF_LIST];
     INTRO_TAC "!C; boxC" THEN
     HYP MESON_TAC "stdw boxC" [IN_SET_OF_LIST];
     MESON_TAC [SUBSENTENCE_CASES; form_DISTINCT];
     INTRO_TAC "!E; notboxE" THEN
     HYP MESON_TAC "stdw notboxE" [IN_SET_OF_LIST]]];
   ALL_TAC] THEN
   CLAIM_TAC "FinX" `FINITE (X:form->bool)` THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{r | r SUBSENTENCE p}` THEN
    CONJ_TAC THENL [MATCH_ACCEPT_TAC FINITE_SUBSENTENCE;
                    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
                    ASM_MESON_TAC[]];
    ALL_TAC] THEN
   THEN1
   (CLAIM_TAC "@M. Mmax Mfin Msub Msuper"
    `?M. MAXIMAL_SETCONSISTENT KB5_AX p M /\
         FINITE M /\
         (!r. r IN M ==> r SUBSENTENCE p) /\
         X SUBSET M`)
   (ABBREV_TAC `P =
      {C | Box C IN set_of_list w} UNION
      {Box C | Box C IN set_of_list w} UNION
      {Not Box E | Not E IN set_of_list w /\ Box E SUBSENTENCE p} UNION
      {Not Box E | Not Box E IN set_of_list w}` THEN
    ABBREV_TAC `Y =
      {Box C | Box C IN set_of_list w} UNION
      {Not E | Not E IN set_of_list w /\ Box E SUBSENTENCE p} UNION
      {Not Box E | Not Box E IN set_of_list w}` THEN
    CLAIM_TAC "FinP" `FINITE (P:form->bool)` THENL
    [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `X:form->bool` THEN
     CONJ_TAC THENL
     [HYP REWRITE_TAC "FinX" [];
      EXPAND_TAC "P" THEN EXPAND_TAC "X" THEN EXPAND_TAC "P" THEN
      REWRITE_TAC[SUBSET; IN_INSERT] THEN
      GEN_TAC THEN DISCH_THEN (LABEL_TAC "pin") THEN DISJ2_TAC THEN
      REMOVE_THEN "pin" ACCEPT_TAC];
     ALL_TAC] THEN
    CLAIM_TAC "FinY" `FINITE (Y:form->bool)` THENL
    [MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `{r | r SUBSENTENCE p}` THEN
     CONJ_TAC THENL
     [MATCH_ACCEPT_TAC FINITE_SUBSENTENCE;
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN EXPAND_TAC "Y" THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM; IN_SET_OF_LIST] THEN
      ASM_MESON_TAC[]];
     ALL_TAC] THEN
    MATCH_MP_TAC EXTEND_MAXIMAL_SETCONSISTENT THEN
    SHOW_TAC `SETCONSISTENT KB5_AX X` THENL
    [EXPAND_TAC "X" THEN REMOVE_THEN "X" (K ALL_TAC) THEN
     REFUTE_THEN (LABEL_TAC "contra_cons") THEN
     REMOVE_THEN "contra" MP_TAC THEN
     REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN
     MATCH_MP_TAC MAXIMAL_SETCONSISTENT_LEMMA THEN
     MAP_EVERY EXISTS_TAC [`KB5_AX`; `p:form`; `Y:form->bool`] THEN
     HYP_TAC "stdw: maxconsw w"
       (REWRITE_RULE[IN_ELIM_THM; KB5_STANDARD_WORLD_DEF;
                     GEN_STANDARD_WORLD;
                     MAXIMAL_CONSISTENT_IFF_MAXIMAL_SETCONSISTENT]) THEN
     HYP REWRITE_TAC "maxconsw boxq" [] THEN
     CONJ_TAC THENL
     [EXPAND_TAC "Y" THEN REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
      SET_TAC[];
      ALL_TAC] THEN
     HYP_TAC "contra_cons" (REWRITE_RULE[SETCONSISTENT]) THEN
     HYP_SUFFICE_TAC
      `[KB5_AX . {} |~ CONJLIST (list_of_set Y) --> Box q]`
      "FinY" [GSYM MODPROVES_DEDUCTION_LEMMA_CONJLIST_EMPTY_ALT] THEN
     CLAIM_TAC "contra_prove"
      `[KB5_AX . {} |~ CONJLIST (list_of_set P) --> q]` THENL
     [HYP SIMP_TAC "FinX FinP"
        [MODPROVES_DEDUCTION_LEMMA_CONJLIST_EMPTY_ALT] THEN
      ONCE_REWRITE_TAC[GSYM MLK_DOUBLENEG_IFF; MLK_not_def] THEN
      ONCE_REWRITE_TAC[MLK_not_def] THEN
      REWRITE_TAC[MODPROVES_DEDUCTION_LEMMA] THEN
      HYP REWRITE_TAC "contra_cons" [];
      ALL_TAC] THEN
     CLAIM_TAC "Bbox"
      `!E. [KB5_AX . {} |~ Not E --> Box Not Box E]` THENL
     [GEN_TAC THEN
      SUBGOAL_THEN
       `[KB5_AX . {} |~ Not E --> Box Diam (Not E)]` MP_TAC THENL
      [MATCH_ACCEPT_TAC (ISPEC `Not E` KB5_AX_B);
       REWRITE_TAC[diam_DEF] THEN
       MESON_TAC[MLK_not_not_th; MLK_imp_mp_subst;
                 MLK_iff_refl_th; MLK_iff_sym; MLK_not_subst;
                 MLK_box_subst]];
      ALL_TAC] THEN
     CLAIM_TAC "Fivebox"
      `!E. [KB5_AX . {} |~ Not Box E --> Box Not Box E]` THENL
     [GEN_TAC THEN
      SUBGOAL_THEN
       `[KB5_AX . {} |~ Diam (Not E) --> Box Diam (Not E)]` MP_TAC THENL
      [MATCH_ACCEPT_TAC (ISPEC `Not E` KB5_AX_FIVE);
       REWRITE_TAC[diam_DEF] THEN
       MESON_TAC[MLK_not_not_th; MLK_imp_mp_subst;
                 MLK_iff_refl_th; MLK_iff_sym; MLK_not_subst;
                 MLK_box_subst]];
      ALL_TAC] THEN
     CLAIM_TAC "FinBoxP" `FINITE (IMAGE (Box) P)` THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN HYP REWRITE_TAC "FinP" [];
      ALL_TAC] THEN
     SHOW_TAC
      `[KB5_AX . {} |~ CONJLIST (list_of_set Y) --> Box q]` THENL
     [MATCH_MP_TAC MLK_imp_trans THEN
      EXISTS_TAC `CONJLIST (list_of_set (IMAGE (Box) P))` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC CONJLIST_IMP_CONJLIST THEN
       GEN_TAC THEN
       INTRO_TAC "memy" THEN
       REMOVE_THEN "memy" MP_TAC THEN
       HYP SIMP_TAC "FinBoxP" [MEM_LIST_OF_SET] THEN
       EXPAND_TAC "P" THEN 
       REWRITE_TAC[IN_IMAGE; IN_UNION; IN_ELIM_THM] THEN
       INTRO_TAC "@C. C_in C_eq" THEN
       REMOVE_THEN "C_eq"
       (DISJ_CASES_THEN2 (LABEL_TAC "case1")
        (DISJ_CASES_THEN2 (CHOOSE_THEN (LABEL_TAC "case2"))
         (DISJ_CASES_THEN2 (CHOOSE_THEN (LABEL_TAC "case3")) 
                           (CHOOSE_THEN (LABEL_TAC "case4"))))) THENL
       [EXISTS_TAC `Box C` THEN CONJ_TAC THENL
        [HYP SIMP_TAC "FinY" [MEM_LIST_OF_SET] THEN
         EXPAND_TAC "Y" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
         ASM_MESON_TAC[];
         ASM_REWRITE_TAC[] THEN MATCH_ACCEPT_TAC MLK_imp_refl_th];
        EXISTS_TAC `Box C'` THEN CONJ_TAC THENL
        [HYP SIMP_TAC "FinY" [MEM_LIST_OF_SET] THEN
         EXPAND_TAC "Y" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
         HYP ASM_MESON_TAC "case2 C_in" [];
         HYP ASM_MESON_TAC "C_in" [KB5_AX_FOUR]];
        EXISTS_TAC `Not E` THEN CONJ_TAC THENL
        [HYP SIMP_TAC "FinY" [MEM_LIST_OF_SET] THEN
         EXPAND_TAC "Y" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
         HYP ASM_MESON_TAC "case3 C_in" [];
         HYP ASM_REWRITE_TAC "case3 C_in Bbox" []];
        EXISTS_TAC `Not Box E` THEN CONJ_TAC THENL
        [HYP SIMP_TAC "FinY" [MEM_LIST_OF_SET] THEN
         EXPAND_TAC "Y" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
         HYP ASM_MESON_TAC "case4 C_in" [];
         HYP ASM_REWRITE_TAC "case4 C_in Fivebox" []]];
        MATCH_MP_TAC MLK_imp_trans THEN
        EXISTS_TAC `Box (CONJLIST (list_of_set P))` THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC MLK_imp_trans THEN
         EXISTS_TAC `CONJLIST (MAP (Box) (list_of_set P))` THEN
         CONJ_TAC THENL
         [MATCH_MP_TAC SET_OF_LIST_EQ_CONJLIST THEN
          HYP MESON_TAC "FinP FinBoxP" 
                        [SET_OF_LIST_MAP; SET_OF_LIST_OF_SET; MAP];
          MATCH_MP_TAC MLK_iff_imp1 THEN
          MATCH_ACCEPT_TAC CONJLIST_MAP_BOX];
         MATCH_MP_TAC MLK_imp_box THEN
         HYP REWRITE_TAC "contra_prove" []]]]; ALL_TAC] THEN
    THEN1 (SHOW_TAC `FINITE (X:form->bool)`)(HYP REWRITE_TAC "FinX" []) THEN
    SHOW_TAC `!r. r IN X ==> r SUBSENTENCE p` THENL [HYP REWRITE_TAC "subX" []]) THEN
  SUFFICE_TAC `KB5_STANDARD_REL p w (list_of_set M) /\ ~MEM q (list_of_set M)` []
  THEN SHOW_TAC `~MEM (q:form) (list_of_set M)` THENL
  [HYP_SUFFICE_TAC `~(q:form IN M)` "Mfin" [MEM_LIST_OF_SET] THEN
   HYP_SUFFICE_TAC `Not q IN M` "Mmax" [IN_SETCONSISTENT_NC; MAXIMAL_SETCONSISTENT_IMP_SETCONSISTENT] THEN
   HYP_SUFFICE_TAC `Not q IN X` "Msuper" [SUBSET] THEN
   EXPAND_TAC "X" THEN REWRITE_TAC[IN_INSERT; IN_UNION];
   ALL_TAC] THEN
  SHOW_TAC `KB5_STANDARD_REL p w (list_of_set M)` THENL
  [ASM_REWRITE_TAC[KB5_STANDARD_REL_CAR] THEN
   SHOW_TAC `(list_of_set (M:form->bool)) IN KB5_STANDARD_WORLD p` THENL
   [REWRITE_TAC[KB5_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD; IN_ELIM_THM;
                MAXIMAL_CONSISTENT_IFF_MAXIMAL_SETCONSISTENT] THEN
    HYP SIMP_TAC "Mfin"
      [SET_OF_LIST_OF_SET; NOREPETITION_LIST_OF_SET; MEM_LIST_OF_SET] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
   SHOW_TAC `w IN KB5_STANDARD_WORLD p` THENL
   [REWRITE_TAC [KB5_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD; IN_ELIM_THM] THEN
    HYP MESON_TAC "stdw" []; ALL_TAC] THEN
   SHOW_TAC `!B. MEM (Box B) w ==> MEM B (list_of_set M) /\ MEM (Box B) (list_of_set M)` THENL
   [INTRO_TAC "!B; BoxB_mem_w" THEN
    CONJ_TAC THENL
    [HYP_SUFFICE_TAC `B:form IN M` "Mfin" [MEM_LIST_OF_SET] THEN
     HYP_SUFFICE_TAC `B:form IN X` "Msuper" [SUBSET] THEN
     EXPAND_TAC "X" THEN 
     SUFFICE_TAC `B IN {C | Box C IN set_of_list w}` [IN_INSERT; IN_UNION] THEN
     REWRITE_TAC[IN_ELIM_THM] THEN 
     ASM_REWRITE_TAC[IN_SET_OF_LIST]; 
     HYP_SUFFICE_TAC `Box B:form IN M` "Mfin" [MEM_LIST_OF_SET] THEN
     HYP_SUFFICE_TAC `Box B:form IN X` "Msuper" [SUBSET] THEN
     EXPAND_TAC "X" THEN 
     SUFFICE_TAC `Box B IN {Box C | Box C IN set_of_list w}` [IN_INSERT; IN_UNION] THEN
     REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `B:form` THEN
     ASM_REWRITE_TAC[IN_SET_OF_LIST]]; ALL_TAC] THEN
   SHOW_TAC `!B. MEM (Box B) (list_of_set M) ==> MEM B w /\ MEM (Box B) w` THENL
   [SUFFICE_TAC `(?E:form. MEM (Box E) (list_of_set M) /\ (~ MEM E w \/ ~  MEM (Box E) w)) 
                 ==> F` [] THEN
    HYP_SUFFICE_TAC `(?E:form. Box E IN M /\ (~ (E IN (set_of_list w)) \/ 
                                             ~ (Box E IN (set_of_list w)))) ==> F`
                    "Mfin" [GSYM IN_SET_OF_LIST; SET_OF_LIST_OF_SET] THEN
    INTRO_TAC "@E. BoxE_in_M EorBoxE_not_mem_w" THEN
    REMOVE_THEN "EorBoxE_not_mem_w" 
     (DISJ_CASES_THEN2 (LABEL_TAC "E_not_mem_w") (LABEL_TAC "BoxE_not_mem_w")) THENL
     [HYP_SUFFICE_TAC `Not Box E IN M` "Mmax BoxE_in_M" 
                      [IN_SETCONSISTENT_NC; MAXIMAL_SETCONSISTENT] THEN     
      HYP_SUFFICE_TAC `Not Box E IN X` "Msuper" [SUBSET]  THEN
      EXPAND_TAC "X" THEN REWRITE_TAC[IN_UNION; IN_INSERT; IN_ELIM_THM] THEN
      SUFFICE_TAC `Not E IN set_of_list w /\ Box E SUBSENTENCE p` [] THEN
      SHOW_TAC `Not E IN set_of_list w` THENL
      [CLAIM_TAC "wmax" `MAXIMAL_SETCONSISTENT KB5_AX p (set_of_list w)` THENL
       [HYP_TAC "stdw" (REWRITE_RULE[IN_ELIM_THM; KB5_STANDARD_WORLD_DEF; 
                                     GEN_STANDARD_WORLD]) THEN
        ASM_MESON_TAC[MAXIMAL_CONSISTENT_IFF_MAXIMAL_SETCONSISTENT]; ALL_TAC] THEN
       HYP_SUFFICE_TAC `E SUBFORMULA p` "wmax E_not_mem_w" [MAXIMAL_SETCONSISTENT] THEN
       MATCH_MP_TAC SUBFORMULA_TRANS THEN
       SUBGOAL_THEN `Box E SUBSENTENCE p` MP_TAC THENL
       [HYP MESON_TAC "BoxE_in_M Msub" []; ALL_TAC] THEN
       REWRITE_TAC[SUBSENTENCE_CASES] THEN
       ASM_MESON_TAC[form_DISTINCT; SUBFORMULA_TRANS; SUBFORMULA_INVERSION;
                     SUBFORMULA_REFL];
       HYP MESON_TAC "BoxE_in_M Msub" []];
      HYP_SUFFICE_TAC `Not Box E IN M` "Mmax BoxE_in_M" 
                      [IN_SETCONSISTENT_NC; MAXIMAL_SETCONSISTENT] THEN     
      HYP_SUFFICE_TAC `Not Box E IN X` "Msuper" [SUBSET]  THEN
      EXPAND_TAC "X" THEN REWRITE_TAC[IN_UNION; IN_INSERT; IN_ELIM_THM] THEN
      SUFFICE_TAC `Not Box E IN set_of_list w ` [] THEN
      CLAIM_TAC "wmax" `MAXIMAL_SETCONSISTENT KB5_AX p (set_of_list w)` THENL
       [HYP_TAC "stdw" (REWRITE_RULE[IN_ELIM_THM; KB5_STANDARD_WORLD_DEF; 
                                     GEN_STANDARD_WORLD]) THEN
        ASM_MESON_TAC[MAXIMAL_CONSISTENT_IFF_MAXIMAL_SETCONSISTENT]; ALL_TAC] THEN
       HYP_SUFFICE_TAC `Box E SUBFORMULA p` "wmax BoxE_not_mem_w" 
                       [MAXIMAL_SETCONSISTENT] THEN
       MATCH_MP_TAC SUBFORMULA_TRANS THEN
       SUBGOAL_THEN `Box E SUBSENTENCE p` MP_TAC THENL
       [HYP MESON_TAC "BoxE_in_M Msub" []; ALL_TAC] THEN
       REWRITE_TAC[SUBSENTENCE_CASES] THEN
       ASM_MESON_TAC[form_DISTINCT; SUBFORMULA_TRANS; SUBFORMULA_INVERSION;
                     SUBFORMULA_REFL]]]]);;

(* ------------------------------------------------------------------------- *)
(* Modal completeness theorem for KB5.                                       *)
(* ------------------------------------------------------------------------- *)

let KB5_STD_IN_KB5_STANDARD_FRAME = prove
 (`!p. ~ [KB5_AX . {} |~ p]
       ==> (KB5_STANDARD_WORLD p, KB5_STANDARD_REL p)
           IN KB5_STANDARD_FRAME p`,
  INTRO_TAC "!p; not_theor_p" THEN
  ASM_REWRITE_TAC[IN_KB5_STANDARD_FRAME] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[ESYF_MAXIMAL_CONSISTENT];
   INTRO_TAC "!q w; boxq stdw" THEN
   EQ_TAC THENL
   [ASM_MESON_TAC[KB5_STANDARD_REL_CAR];
    ASM_MESON_TAC[KB5_ACCESSIBILITY_LEMMA]]]);;

let KB5_COUNTERMODEL = prove
 (`!M p.
     ~ [KB5_AX . {} |~ p] /\
     M IN KB5_STANDARD_WORLD p /\
     MEM (Not p) M
     ==> ~holds
          (KB5_STANDARD_WORLD p, KB5_STANDARD_REL p)
          (STANDARD_EVAL p) p M`,
  INTRO_TAC "!M p; pr stdM mem" THEN
  MATCH_MP_TAC GEN_COUNTERMODEL THEN EXISTS_TAC `KB5_AX` THEN
  HYP_TAC "stdM -> maxconsM M"
   (REWRITE_RULE[IN_KB5_STANDARD_FRAME; KB5_STANDARD_WORLD_DEF;
                 GEN_STANDARD_WORLD; IN_ELIM_THM]) THEN
  ASM_REWRITE_TAC[GEN_STANDARD_MODEL_DEF] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[KB5_STD_IN_KB5_STANDARD_FRAME;
                 KB5_STANDARD_FRAME_DEF];
   ALL_TAC] THEN
  ASM_MESON_TAC[IN_ELIM_THM; STANDARD_EVAL;
                KB5_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD]);;

let KB5_COMPLETENESS_THM = prove
 (`!p. ESF:(form list->bool)#(form list->form list->bool)-> bool |= p
       ==> [KB5_AX . {} |~ p]`,
  GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  INTRO_TAC "p_not_theor" THEN
  REWRITE_TAC[valid; NOT_FORALL_THM] THEN
  EXISTS_TAC `(KB5_STANDARD_WORLD p, KB5_STANDARD_REL p)` THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
  [ASM_MESON_TAC[ESYF_MAXIMAL_CONSISTENT];
   SUBGOAL_THEN
    `(KB5_STANDARD_WORLD p, KB5_STANDARD_REL p)
     IN GEN_STANDARD_FRAME KB5_AX p` MP_TAC THENL
   [ASM_MESON_TAC[KB5_STD_IN_KB5_STANDARD_FRAME;
                  KB5_STANDARD_FRAME_DEF];
    ASM_MESON_TAC[GEN_COUNTERMODEL_ALT]]]);;

(* ------------------------------------------------------------------------- *)
(* Modal completeness for KB5 for models on a generic (infinite) domain.     *)
(* ------------------------------------------------------------------------- *)

let KB5_COMPLETENESS_THM_GEN = prove
 (`!p. INFINITE (:A) /\
       ESF:(A->bool)#(A->A->bool)->bool |= p
       ==> [KB5_AX . {} |~ p]`,
  SUBGOAL_THEN
   `INFINITE (:A)
    ==> !p. ESF:(A->bool)#(A->A->bool)->bool |= p
            ==> ESF:(form list->bool)#(form list->form list->bool)->bool |= p`
   (fun th -> MESON_TAC[th; KB5_COMPLETENESS_THM]) THEN
  ASM_MESON_TAC[ESF_APPR_KB5; GEN_LEMMA_FOR_GEN_COMPLETENESS]);;

(* ------------------------------------------------------------------------- *)
(* Simple decision procedure for KB5.                                       *)
(* ------------------------------------------------------------------------- *)

let KB5_TAC : tactic =
  MATCH_MP_TAC KB5_COMPLETENESS_THM THEN
  REWRITE_TAC[diam_DEF; valid; FORALL_PAIR_THM; holds_in; holds; IN_ESF;
    IN_FINITE_FRAME; EUCLIDEAN; SYMMETRIC; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[];;

let KB5_RULE tm =
  prove(tm, REPEAT GEN_TAC THEN KB5_TAC);;

KB5_RULE `!p q r. [KB5_AX . {} |~ p && q && r --> p && r]`;;
KB5_RULE `!p q. [KB5_AX . {} |~ Box (p --> q) && Box p --> Box q]`;;
KB5_RULE `!p q. [KB5_AX . {} |~ Box p --> Box (Box p)]`;;
KB5_RULE `!p. [KB5_AX . {} |~ p --> Box Diam p]`;;
KB5_RULE `!p. [KB5_AX . {} |~ Diam p --> Box Diam p]`;;
(* KB5_RULE `!p. [KB5_AX . {} |~ Box p --> p]`;; *)

(* ------------------------------------------------------------------------- *)
(* Countermodel using sets of formulae instead of lists of formulae.         *)
(* ------------------------------------------------------------------------- *)

let KB5_STDWORLDS_RULES,KB5_STDWORLDS_INDUCT,KB5_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT KB5_AX p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN KB5_STDWORLDS p`;;

let KB5_STDREL_RULES,KB5_STDREL_INDUCT,KB5_STDREL_CASES =
  new_inductive_definition
  `!w1 w2. KB5_STANDARD_REL p w1 w2
           ==> KB5_STDREL p (set_of_list w1) (set_of_list w2)`;;

let KB5_STDREL_IMP_KB5_STDWORLDS = prove
 (`!p w1 w2. KB5_STDREL p w1 w2 ==>
             w1 IN KB5_STDWORLDS p /\
             w2 IN KB5_STDWORLDS p`,
  GEN_TAC THEN MATCH_MP_TAC KB5_STDREL_INDUCT THEN
  REWRITE_TAC[KB5_STANDARD_REL_CAR] THEN
  INTRO_TAC "!w1 w2; stdw1 stdw2 w2 w1" THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC KB5_STDWORLDS_RULES THEN
   HYP_TAC "stdw1" (REWRITE_RULE[IN_ELIM_THM; KB5_STANDARD_WORLD_DEF;
                                 GEN_STANDARD_WORLD]) THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC KB5_STDWORLDS_RULES THEN
   HYP_TAC "stdw2" (REWRITE_RULE[IN_ELIM_THM; KB5_STANDARD_WORLD_DEF;
                                 GEN_STANDARD_WORLD]) THEN
   ASM_REWRITE_TAC[]]);;

let SET_OF_LIST_EQ_KB5_STANDARD_REL = prove
 (`!p u1 u2 w1 w2.
     set_of_list u1 = set_of_list w1 /\ NOREPETITION w1 /\
     set_of_list u2 = set_of_list w2 /\ NOREPETITION w2 /\
     KB5_STANDARD_REL p u1 u2
     ==> KB5_STANDARD_REL p w1 w2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[KB5_STANDARD_REL_CAR] THEN
  REWRITE_TAC[IN_ELIM_THM; KB5_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD] THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM];
   MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM];
   ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM];
   ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]]);;

let KB5_STANDARD_BISIM = new_definition
 `KB5_STANDARD_BISIM (p:form) (w1:form list) (w2:form->bool) <=>
         w1 IN KB5_STANDARD_WORLD p /\
         w2 IN KB5_STDWORLDS p /\
         set_of_list w1 = w2`;;

let KB5_BISIMIMULATION_SET_OF_LIST = prove
 (`!p:form. BISIMIMULATION
      (KB5_STANDARD_WORLD p,
        KB5_STANDARD_REL p,
        STANDARD_EVAL p)
      (KB5_STDWORLDS p,
       KB5_STDREL p,
       SET_STANDARD_EVAL p)
      (KB5_STANDARD_BISIM p)`,
  GEN_TAC THEN
  REWRITE_TAC[STANDARD_EVAL; SET_STANDARD_EVAL; KB5_STANDARD_BISIM;
              BISIMIMULATION] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; KB5_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [GEN_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC[IN_SET_OF_LIST];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![u1]; w1u1" THEN
   EXISTS_TAC `set_of_list u1:form->bool` THEN
   HYP_TAC "w1u1 -> hp"
    (REWRITE_RULE[KB5_STANDARD_REL_CAR; IN_ELIM_THM;
                  KB5_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD]) THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC KB5_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC KB5_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   MATCH_MP_TAC KB5_STDREL_RULES THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "![u2]; w2u2" THEN
  EXISTS_TAC `list_of_set u2:form list` THEN
  REWRITE_TAC[CONJ_ACI] THEN
  HYP_TAC "w2u2 -> @x2 y2. x2 y2 x2y2"
   (REWRITE_RULE[KB5_STDREL_CASES]) THEN
  REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  SIMP_TAC[SET_OF_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  SIMP_TAC[MEM_LIST_OF_SET; FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
  CONJ_TAC THENL
  [HYP_TAC "x2y2 -> hp"
   (REWRITE_RULE[KB5_STANDARD_REL_CAR; IN_ELIM_THM;
                 KB5_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD]) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[KB5_STDREL_IMP_KB5_STDWORLDS];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_KB5_STANDARD_REL THEN
   EXISTS_TAC `x2:form list` THEN EXISTS_TAC `y2:form list` THEN
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET;
            FINITE_SET_OF_LIST] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT];
   ALL_TAC] THEN
  MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN
  EXISTS_TAC `y2:form list` THEN
  SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET;
           FINITE_SET_OF_LIST] THEN
  HYP_TAC "x2y2 -> hp"
   (REWRITE_RULE[KB5_STANDARD_REL_CAR; IN_ELIM_THM;
                 KB5_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD]) THEN
  ASM_MESON_TAC[]);;

let KB5_COUNTERMODEL_FINITE_SETS = prove
 (`!p. ~ [KB5_AX . {} |~ p]
       ==> ~holds_in (KB5_STDWORLDS p, KB5_STDREL p) p`,
  INTRO_TAC "!p; p" THEN
  DESTRUCT_TAC "@M. maxM memM M"
   (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT
    (ASSUME `~ [KB5_AX . {} |~ p]`)) THEN
  CLAIM_TAC "stdwM" `M IN KB5_STANDARD_WORLD p` THENL
  [ASM_REWRITE_TAC[IN_ELIM_THM; KB5_STANDARD_WORLD_DEF;
                   GEN_STANDARD_WORLD];
   ALL_TAC] THEN
  REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP] THEN
  EXISTS_TAC `SET_STANDARD_EVAL p` THEN
  EXISTS_TAC `set_of_list M:form->bool` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC KB5_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `holds (KB5_STANDARD_WORLD p, KB5_STANDARD_REL p)
      (STANDARD_EVAL p) p M <=>
    holds (KB5_STDWORLDS p, KB5_STDREL p)
      (SET_STANDARD_EVAL p) p (set_of_list M)`
   ASSUME_TAC THENL
  [MATCH_MP_TAC BISIMIMULATION_HOLDS THEN
    EXISTS_TAC `KB5_STANDARD_BISIM p` THEN
    CONJ_TAC THENL
   [MATCH_ACCEPT_TAC KB5_BISIMIMULATION_SET_OF_LIST;
    REWRITE_TAC[KB5_STANDARD_BISIM] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC KB5_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]];
   ASM_MESON_TAC[KB5_COUNTERMODEL]]);;