(* ========================================================================= *)
(* Grzegorczyk Logic (Grz).                                                  *)
(*                                                                           *)
(* Meta-theory (soundness and completeness).                                 *)
(* Translation to GL Logic.                                                  *)
(* Decision procedure via the translation.                                   *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025-26.                               *)
(* ========================================================================= *)

needs "HOLMS/k_decid.ml";;       (* Used in GRZ_EQ_S4GRZ and its lemmas     *)
needs "HOLMS/s4_decid.ml";;      (* Used in S4GRZ_TRUTH_LEMMA               *)
needs "HOLMS/gl_decid.ml";;      (* Used in GRZ_TAC                         *)
needs "HOLMS/translations.ml";;

(* ------------------------------------------------------------------------- *)
(* 1. Axiomatic presentations of Grzegorczyk.                                *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Definition of the axiomatic calculus Grz.                                 *)
(* ------------------------------------------------------------------------- *)

let GRZ_SCHEMA_DEF = new_definition
  `GRZ_SCHEMA p = (Box (Box (p --> Box p) --> p) --> p)`;;

let GRZ_AX = new_definition
  `GRZ_AX = {GRZ_SCHEMA p| p IN (:form)}`;;

let GRZ_IN_GRZ_AX = prove
 (`!p. Box (Box (p --> Box p) --> p) --> p IN GRZ_AX`,
  REWRITE_TAC[GRZ_AX; GRZ_SCHEMA_DEF; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]);;

let GRZ_AX_GRZ = prove
 (`!p. [GRZ_AX. {} |~ Box (Box (p --> Box p) --> p) --> p]`,
  MESON_TAC[MODPROVES_RULES; GRZ_IN_GRZ_AX]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the axiomatic calculus S4GRZ.                               *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_AX = new_definition
  `S4GRZ_AX = {FOUR_SCHEMA p| p IN (:form)} UNION
              {T_SCHEMA p |p IN (:form)} UNION
              {GRZ_SCHEMA p| p IN (:form)}`;;

let GRZ_IN_S4GRZ_AX = prove
 (`!p. Box (Box (p --> Box p) --> p) --> p IN S4GRZ_AX`,
  REWRITE_TAC[S4GRZ_AX; GRZ_SCHEMA_DEF; IN_ELIM_THM; IN_UNIV; UNION] THEN
  MESON_TAC[]);;

let S4GRZ_AX_GRZ = prove
 (`!p. [S4GRZ_AX. {} |~ Box (Box (p --> Box p) --> p) --> p]`,
  MESON_TAC[MODPROVES_RULES; GRZ_IN_S4GRZ_AX]);;

(* ------------------------------------------------------------------------- *)
(* Proof of the equivalence between Grz and S4GRZ.                           *)
(* See Boolos §12 p.157-158.                                                 *)
(* ------------------------------------------------------------------------- *)

let GRZ_PROVES_T = prove
 (`!H p. [GRZ_AX . H |~ T_SCHEMA p]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MODPROVES_MONO2 THEN
  EXISTS_TAC `{}:form->bool` THEN
  REWRITE_TAC[EMPTY_SUBSET; T_SCHEMA_DEF] THEN
  MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `Box (Box (p --> Box p) --> p)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC MODPROVES_MONO1 THEN
   EXISTS_TAC `{}:form->bool` THEN
   CONJ_TAC THENL [ASM_MESON_TAC[EMPTY_SUBSET]; HOLMS_TAC];
   ASM_MESON_TAC[MODPROVES_RULES; GRZ_IN_GRZ_AX]]);;

let GRZ_PROVES_4 = prove
 (`!H p.[GRZ_AX . H |~ FOUR_SCHEMA p]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MODPROVES_MONO2 THEN
  EXISTS_TAC `{}:form->bool` THEN
  REWRITE_TAC[EMPTY_SUBSET; FOUR_SCHEMA_DEF] THEN
  ABBREV_TAC `C = (FOUR_SCHEMA p) && p` THEN MATCH_MP_TAC MLK_frege THEN
  EXISTS_TAC `Box p` THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `C:form` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MLK_imp_trans THEN
    EXISTS_TAC `Box (Box (C --> Box C) --> C)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC MODPROVES_MONO1 THEN EXISTS_TAC `{}:form->bool` THEN
     CONJ_TAC THENL
      [MESON_TAC[EMPTY_SUBSET];
       EXPAND_TAC "C" THEN RULE_ASSUM_TAC SYM THEN
       ASM_REWRITE_TAC[FOUR_SCHEMA_DEF] THEN HOLMS_TAC];
     ASM_MESON_TAC[MODPROVES_RULES; GRZ_IN_GRZ_AX; FOUR_SCHEMA_DEF]];
    ASM_MESON_TAC[MLK_and_left_th; FOUR_SCHEMA_DEF]];
   ASM_MESON_TAC[MODPROVES_RULES; KAXIOM_RULES; FOUR_SCHEMA_DEF]]);;

let S4GRZ_prove_S4 = prove
 (`!H p. [S4_AX . H |~ p] ==> [S4GRZ_AX . H |~ p]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MODPROVES_MONO1 THEN
  EXISTS_TAC `S4_AX` THEN ASM_REWRITE_TAC[S4GRZ_AX; S4_AX] THEN SET_TAC[]);;

let GRZ_EQ_S4GRZ = prove
 (`!H p. [GRZ_AX . H |~ p] <=> [S4GRZ_AX . H |~ p]`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [DISCH_TAC THEN MATCH_MP_TAC MODPROVES_MONO1 THEN EXISTS_TAC `GRZ_AX` THEN
   CONJ_TAC THENL [SET_TAC[GRZ_AX; S4GRZ_AX]; ASM_REWRITE_TAC[]];
   SUBGOAL_THEN `!H p. [S4GRZ_AX . H |~ p] ==> [GRZ_AX . H |~ p]` MP_TAC THENL
   [MATCH_MP_TAC MODPROVES_INDUCT THEN REPEAT CONJ_TAC THENL
    [MESON_TAC[MODPROVES_RULES];
     REWRITE_TAC[IN_ELIM_THM; S4GRZ_AX; IN_UNION] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[GRZ_PROVES_4];
      ASM_MESON_TAC[GRZ_PROVES_T];
      ASM_MESON_TAC[EMPTY_SUBSET; MODPROVES_RULES;
                    GRZ_IN_GRZ_AX; GRZ_SCHEMA_DEF]];
     MESON_TAC[MODPROVES_RULES];
     MESON_TAC[MODPROVES_RULES];
     MESON_TAC[MODPROVES_RULES]];
    MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 2. Semantic presentations of Grzegorczyk.                                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Alternative characterization for posets.                                  *)
(* ------------------------------------------------------------------------- *)

let POSET_EQ = prove
 (`!(<<) W.
     poset (<<) /\ fld (<<) = W <=>
     (!x y:W. x << y ==> x IN W /\ y IN W) /\
     REFLEXIVE W (<<) /\
     TRANSITIVE W (<<) /\
     ANTISYMMETRIC W (<<)`,
  REWRITE_TAC[poset; REFLEXIVE; TRANSITIVE; ANTISYMMETRIC;
              EXTENSION; SUBSET] THEN
  MESON_TAC[IN_FLD]);;

(* ------------------------------------------------------------------------- *)
(* Definition of weakly wellfoundedness for arbitrary (infix) relation <<    *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Modified WWF: restricts quantification on `P SUBSET fld`.                 *)
(* ------------------------------------------------------------------------- *)

let WWF = new_definition
  `WWF (<<) <=>
   (!P. (?x:W. P x) /\ (!x. P x ==> x IN fld (<<))
        ==> (?x. P x /\ (!y. ~(x = y) /\ y << x ==> ~P y)))`;;

let WWF_EQ = prove
 (`!(<<). WWF (<<) <=>
          !P. (!x. P x ==> x IN fld (<<))
              ==> ((?x:A. P(x)) <=>
                   (?x. P(x) /\ (!y. ~(x = y) /\ y << x ==> ~P(y))))`,
  GEN_TAC THEN REWRITE_TAC[WWF] THEN EQ_TAC THENL
  [MESON_TAC[];
   INTRO_TAC "hp; !P; ne sub" THEN
   HYP_TAC "hp: +" (SPEC `P:A->bool`) THEN
   ASM_MESON_TAC[]]);;

let WWF_IND = prove
 (`!(<<). WWF(<<) <=>
          !P. (!x:A. ~P x ==> x IN fld (<<))
              ==> (!x. (!y. y << x /\ ~(x = y) ==> P y) ==> P x) ==> !x. P x`,
  GEN_TAC THEN REWRITE_TAC[WWF] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\x:A. ~P(x)`) THEN BETA_TAC THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Equivalent formualtion.                                                   *)
(* ------------------------------------------------------------------------- *)

let WWF_ALT = prove
 (`!l. WWF l <=>
       (!s. ~(s = {}) /\ s SUBSET fld l
            ==> (?a:W. a IN s /\ (!x. x IN s ==> ~properly l x a)))`,
  REWRITE_TAC[WWF; properly; SUBSET; IN; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Finite non-empty posets are WWF (specialization of POSET_MAX).            *)
(* ------------------------------------------------------------------------- *)

let POSET_WWF = prove
 (`!l:A->A->bool. poset l /\ ~(fld l = {}) /\ FINITE (fld l) ==> WWF l`,
  INTRO_TAC "!l; l ne fin" THEN REWRITE_TAC[WWF_ALT] THEN
  MP_TAC (ISPECL [`l:A->A->bool`] POSET_MIN) THEN
  INTRO_TAC "max; !s; ne sub" THEN
  HYP_TAC "max: +" (SPEC `s:A->bool`) THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[FINITE_SUBSET];
   ASM_MESON_TAC[]]);;

let POSET_WWF_ALT = prove
 (`!(<<) W. (!x y:W. x << y ==> x IN W /\ y IN W) /\
            REFLEXIVE W (<<) /\
            TRANSITIVE W (<<) /\
            ANTISYMMETRIC W (<<) /\
            FINITE W /\
            ~(W = {})
            ==> WWF (<<)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POSET_WWF THEN ASM_MESON_TAC[POSET_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Reflexive, Transitive and Weakly Noetherian Frames.                       *)
(* ------------------------------------------------------------------------- *)

let RTWN_DEF = new_definition
  `RTWN =
   {(W:W->bool,R:W->W->bool) |
    (W,R) IN FRAME /\
    REFLEXIVE W R /\
    TRANSITIVE W R /\
    WWF (\x y. R y x)}`;;

let IN_RTWN = prove
 (`(W:W->bool,R:W->W->bool) IN RTWN <=>
   (W,R) IN FRAME /\
   REFLEXIVE W R /\
   TRANSITIVE W R /\
   WWF (\x y. R y x)`,
  REWRITE_TAC[RTWN_DEF; IN_ELIM_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Reflexive, Antisymmetric, Transitive Finite Frames.                       *)
(* ------------------------------------------------------------------------- *)

let RATF_DEF = new_definition
 `RATF =
  {(W:W->bool,R:W->W->bool) |
   FINITE_FRAME (W,R) /\
   REFLEXIVE W R /\
   TRANSITIVE W R /\
   ANTISYMMETRIC W R}`;;

let IN_RATF = prove
 (`(W:W->bool,R:W->W->bool) IN RATF <=>
   (W,R) IN FINITE_FRAME /\
   REFLEXIVE W R /\
   TRANSITIVE W R /\
   ANTISYMMETRIC W R`,
  MESON_TAC[RATF_DEF; IN_ELIM_PAIR_THM; IN]);;

(* ------------------------------------------------------------------------- *)
(* RATFs Frames are RTWN Frames.                                             *)
(* ------------------------------------------------------------------------- *)

let RATF_SUBSET_RTWN = prove
 (`(RATF:(W->bool)#(W->W->bool)->bool ) SUBSET RTWN`,
  REWRITE_TAC[SUBSET; IN_RATF; IN_RTWN; FORALL_PAIR_THM;
              IN_FRAME; IN_FINITE_FRAME] THEN
  INTRO_TAC "![W] [R]; (non_empty (rel finite)) refl trans antisym" THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC POSET_WWF_ALT THEN
  EXISTS_TAC `W:W->bool` THEN ASM_REWRITE_TAC[] THEN
  HYP (MP_TAC o end_itlist CONJ) "rel refl trans antisym" [] THEN
  REWRITE_TAC[REFLEXIVE; TRANSITIVE; ANTISYMMETRIC] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 3. Soundness Lemmas.                                                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory: RTWN Frames are characteristic for S4GRZ.          *)
(* ------------------------------------------------------------------------- *)

let MODAL_RTWN = prove
 (`!W:W->bool R.
     (!x y. R x y ==> x IN W /\ y IN W)
     ==> REFLEXIVE W R /\ TRANSITIVE W R /\ WWF (\x y. R y x)
     ==> !p. holds_in (W,R) (GRZ_SCHEMA p)`,
  REWRITE_TAC[REFLEXIVE; TRANSITIVE; GRZ_SCHEMA_DEF] THEN
  INTRO_TAC "!W R; wd" THEN
  INTRO_TAC "REFL TRANS WWF" THEN
  HYP_TAC "WWF" (REWRITE_RULE[WWF_IND]) THEN
  GEN_TAC THEN
  ASM_REWRITE_TAC[holds_in] THEN
  REPEAT GEN_TAC THEN
  ABBREV_TAC `X_0 = {w:W | w IN W /\
                           holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                           ~(holds (W,R) V p w)}` THEN
  ABBREV_TAC `X_1 = {w:W | w IN W /\
                           holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                           ~(holds (W,R) V (Box p) w) /\
                           holds (W,R) V p w}` THEN
  CLAIM_TAC "EMPTY_IN" `(X_0 INTER X_1) = {}:W->bool` THENL
  [REFUTE_THEN MP_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `?x. x:W IN X_0 INTER X_1` MP_TAC THENL
   [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
   INTRO_TAC "@x. NON_EMPTY" THEN
   HYP_TAC "NON_EMPTY" (REWRITE_RULE[IN_INTER]) THEN
   SUBGOAL_THEN `~(holds (W,R) V p (x:W)) /\ (holds (W,R) V p (x:W))`
     MP_TAC THENL
   [SUBGOAL_THEN `(x:W) IN
                    {w:W | w IN W /\
                           holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                           ~(holds (W,R) V p w)} /\
                    x IN
                     {w:W | w IN W /\
                            holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                            ~(holds (W,R) V (Box p) w) /\ holds (W,R) V p w}`
                  MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ASM_MESON_TAC[]];
   DISCH_TAC] THEN
  CLAIM_TAC "EMPTY_X0" `(X_0:W->bool) = {}` THENL
  [CLAIM_TAC "w'_IN_X0_THEN_x_IN_X1"
    `!w'. w' IN (X_0:W->bool) ==> ?x. ((R:W->W->bool) w' x /\ x IN X_1)` THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(w':W) IN
                  {w | w IN W /\
                       holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                       ~(holds (W,R) V p w)} ` MP_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    INTRO_TAC "IN_X0_THEN_IN_W IN_X0_THEN_ForA IN_X0_THEN_NonForB" THEN
    CLAIM_TAC "IN_X0_THEN_REFL" `((R:W->W->bool) w' w')` THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    CLAIM_TAC "For1" `holds (W,R) V (Box (p --> Box p) --> p) (w':W)` THENL
    [SUBGOAL_THEN `holds (W,R) V (Box (Box (p --> Box p) --> p)) (w':W)`
       MP_TAC THENL
     [ASM_REWRITE_TAC[];
      MODAL_SCHEMA_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    CLAIM_TAC "Not_For2" `~ holds (W,R) V (Box (p --> Box p)) (w':W)` THENL
    [SUBGOAL_THEN `~holds (W,R) V p (w':W) /\
                    holds (W,R) V (Box (p --> Box p) --> p) (w':W)` MP_TAC THENL
      [ASM_MESON_TAC[]; MODAL_SCHEMA_TAC THEN ASM_MESON_TAC[]];
     ALL_TAC] THEN
    SUBGOAL_THEN `?x. ((R:W->W->bool) w' x /\ holds (W,R) V (p) (x:W) /\
                       ~holds (W,R) V (Box p) (x:W))` MP_TAC THENL
    [SUBGOAL_THEN `~holds (W,R) V (Box (p --> Box p)) (w':W)` MP_TAC THENL
     [ASM_MESON_TAC[];
      MODAL_SCHEMA_TAC THEN ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
      INTRO_TAC "@z. a b @k. c" THEN EXISTS_TAC `z:W` THEN
      REPEAT CONJ_TAC THEN ASM_MESON_TAC[]];
     ALL_TAC] THEN
    INTRO_TAC "@x. REL_x p Not_Box_p" THEN EXISTS_TAC `(x:W)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `(x:W) IN {w | w IN W /\
                     holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                     ~holds (W,R) V (Box p) w /\ holds (W,R) V p w}`
      MP_TAC THENL
    [ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      SUBGOAL_THEN `!z:W. R x z ==> holds (W,R) V (Box (p --> Box p) --> p) z`
        MP_TAC THENL
      [GEN_TAC THEN DISCH_TAC THEN CLAIM_TAC "REL_z" `(R:W->W->bool) w' z` THENL
       [ASM_MESON_TAC[];
        SUBGOAL_THEN `holds (W,R) V (Box (Box (p --> Box p) --> p)) (w':W)`
          MP_TAC THENL
        [ASM_REWRITE_TAC[];
         MODAL_SCHEMA_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
         ASM_MESON_TAC[]]];
        MODAL_SCHEMA_TAC THEN ASM_MESON_TAC[]]];
     ASM_MESON_TAC[]];
    ALL_TAC] THEN
   CLAIM_TAC "w'_IN_X1_THEN_x_IN_X0 "
              `! w'. w' IN (X_1:W->bool) ==>
                     ?x. ((R:W->W->bool) w' x /\ x IN X_0)` THENL
    [REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `(w':W) IN
                     {w | w IN W /\
                          holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                          ~holds (W,R) V (Box p) w /\ holds (W,R) V p w} ` MP_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
     ASM_REWRITE_TAC[IN_ELIM_THM] THEN
     INTRO_TAC "IN_X1_THEN_IN_W IN_X1_THEN_ForA IN_X1_THEN_NonForB IN_X1_THEN_ForC" THEN
     SUBGOAL_THEN `?x. (R:W->W->bool) w' x /\ ~holds (W,R) V p (x:W)` MP_TAC THENL
      [SUBGOAL_THEN `~holds (W,R) V (Box p) (w':W)` MP_TAC THENL
        [ASM_MESON_TAC[]; MODAL_SCHEMA_TAC THEN ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
         INTRO_TAC "@z. (a b) c" THEN EXISTS_TAC `z:W` THEN ASM_MESON_TAC[]];
       ALL_TAC] THEN
     INTRO_TAC "@x. REL_x Not_p" THEN EXISTS_TAC `(x:W)` THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `(x:W) IN
                   {w | w IN W /\
                        holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                        ~(holds (W,R) V p w)}` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
      [ASM_MESON_TAC[];
       SUBGOAL_THEN `!z. R x z ==> (holds (W,R) V (Box (p --> Box p) --> p) (z:W))` MP_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN CLAIM_TAC "REL_z" `(R:W->W->bool) w' z` THENL
        [ASM_MESON_TAC[];
         SUBGOAL_THEN `holds (W,R) V (Box (Box (p --> Box p) --> p)) (w':W)` MP_TAC THENL
         [ASM_REWRITE_TAC[]; MODAL_SCHEMA_TAC THEN DISCH_TAC THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]];
        MODAL_SCHEMA_TAC THEN ASM_MESON_TAC[]]];
      ASM_MESON_TAC[]];
     ALL_TAC] THEN
   ABBREV_TAC `(X:W->bool) = X_0 UNION X_1` THEN
   CLAIM_TAC "EMPTY_UN" `(X:W->bool) = {}` THENL
    [SUBGOAL_THEN `WWF (\x y. (R:W->W->bool) y x)` MP_TAC THENL
      [ASM_MESON_TAC[WWF_IND]; ALL_TAC] THEN
     REWRITE_TAC[WWF_EQ] THEN DISCH_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `(\x:W. x IN X)`) THEN
     REWRITE_TAC[IN_FLD] THEN ANTS_TAC THENL
      [REWRITE_TAC[IN_FLD] THEN CLAIM_TAC "+" `X:W->bool SUBSET W` THENL
        [MAP_EVERY EXPAND_TAC ["X"; "X_0"; "X_1"] THEN SET_TAC[]; HYP SET_TAC "REFL" []];
       DISCH_TAC] THEN
     SUBGOAL_THEN `~ ?x. x:W IN X` MP_TAC THENL
      [ASM_REWRITE_TAC[] THEN
       ASM_REWRITE_TAC[MEMBER_NOT_EMPTY;
                       NOT_EXISTS_THM; DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP] THEN
       REWRITE_TAC[TAUT `(~p \/ q) <=> (p ==> q)`] THEN GEN_TAC THEN DISCH_TAC THEN
       SUBGOAL_THEN `(x:W IN X_0 \/ x IN X_1) /\ ~(x IN X_0 /\ x IN X_1)` MP_TAC THENL
        [ASM_MESON_TAC[IN_UNION; DISJOINT; IN_DISJOINT]; ALL_TAC] THEN
       STRIP_TAC THENL
        [SUBGOAL_THEN `(?y. (R:W->W->bool) x y /\ y IN X_1)` MP_TAC THENL
          [ASM_MESON_TAC[]; INTRO_TAC "@y. REL IN" THEN EXISTS_TAC `y:W` THEN
           ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_UNION]];
         SUBGOAL_THEN `(?y. (R:W->W->bool) x y /\ y IN X_0)` MP_TAC THENL
          [ASM_MESON_TAC[]; INTRO_TAC "@y. REL IN" THEN EXISTS_TAC `y:W` THEN
           ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_UNION]]];
       ASM_MESON_TAC[MEMBER_NOT_EMPTY]];
     ASM_MESON_TAC[EMPTY_UNION]];
   ALL_TAC] THEN
  SUBGOAL_THEN `~(?x. x IN {w | w IN (W:W->bool) /\
                      holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                      ~holds (W,R) V p w})` MP_TAC THENL
  [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  REFUTE_THEN MP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?(x:W). (holds (W,R) V (Box (Box (p --> Box p) --> p)) x /\
                         ~holds (W,R) V p x) /\
                        x IN W` MP_TAC THENL
  [UNDISCH_TAC `~holds (W,R) V (Box (Box (p --> Box p) --> p) --> p) (w:W)` THEN
   MODAL_SCHEMA_TAC THEN ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
   DISCH_TAC THEN EXISTS_TAC `w:W` THEN
   CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[];
   ASM_MESON_TAC[]]);;

let RTWN_SUBSET_CHAR_S4GRZ = prove
 (`RTWN:(W->bool)#(W->W->bool)->bool SUBSET CHAR S4GRZ_AX`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CHAR; IN_RTWN] THEN
  REWRITE_TAC[S4GRZ_AX; FORALL_IN_UNION; FORALL_IN_GSPEC; IN_UNIV] THEN
  REPEAT STRIP_TAC THENL
  [ASM_REWRITE_TAC[];
   ASM_MESON_TAC[MODAL_TRANS];
   ASM_MESON_TAC[MODAL_REFL];
   ASM_MESON_TAC[MODAL_RTWN; IN_FRAME]]);;

(* ------------------------------------------------------------------------- *)
(* Soundness Lemma for S4GRZ.                                                *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_RTWN_VALID = prove
 (`!H p. [S4GRZ_AX . H |~ p] /\
         (!q. q IN H ==> RTWN:(W->bool)#(W->W->bool)->bool |= q)
         ==> RTWN:(W->bool)#(W->W->bool)->bool |= p`,
  MESON_TAC[GEN_SUBS_CHAR_VALID; RTWN_SUBSET_CHAR_S4GRZ]);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. RATF.                                           *)
(* ------------------------------------------------------------------------- *)

let RTWN_VALID_IMPLIES_RATF_VALID = prove
 (`!p. RTWN :(W->bool)#(W->W->bool)->bool |= p
         ==> RATF:(W->bool)#(W->W->bool)->bool |= p`,
  REWRITE_TAC[valid] THEN MESON_TAC[RATF_SUBSET_RTWN; SUBSET]);;

let S4GRZ_RATF_VALID = prove
 (`!p. [S4GRZ_AX . {} |~ p] ==> RATF:(W->bool)#(W->W->bool)->bool |= p`,
  INTRO_TAC "!p; prove" THEN MATCH_MP_TAC RTWN_VALID_IMPLIES_RATF_VALID THEN
  MATCH_MP_TAC S4GRZ_RTWN_VALID THEN EXISTS_TAC `{}:form->bool` THEN
  ASM_MESON_TAC[NOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Proof of Consistency of S4GRZ.                                            *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_CONSISTENT = prove
 (`~ [S4GRZ_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP(INST_TYPE[`:num`,`:W`] S4GRZ_RATF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM; IN_RATF;
    IN_FINITE_FRAME; REFLEXIVE; TRANSITIVE; ANTISYMMETRIC; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. x = 0 /\ x = y`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 4. Completeness Theorem                                                   *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* S4GRZ standard worlds, frames and models.                                 *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_STANDARD_WORLDS_DEF = new_definition
  `S4GRZ_STANDARD_WORLDS p =
   {w | MAXIMAL_CONSISTENT S4GRZ_AX p w /\
        (!q. MEM q w  ==> (q SUBSENTENCE p \/
                           ?C. Box C SUBFORMULA p /\
                               (q = Box (C --> Box C) \/
                                q = Not Box (C --> Box C))))}`;;

let GEN_STANDARD_FRAME_DEF = new_definition
  `GEN_STANDARD_FRAME S p =
   APPR S INTER
   {(W,R) | W = {w | MAXIMAL_CONSISTENT S p w /\
            (!q. MEM q w ==> q SUBSENTENCE p)} /\
            (!q w. Box q SUBFORMULA p /\ w IN W
                   ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))}`;;

let Q_REL_DEF = new_definition
  `Q_REL p w x <=>
    w IN S4GRZ_STANDARD_WORLDS p  /\
    x IN S4GRZ_STANDARD_WORLDS p  /\
    (!B. (B SUBSENTENCE p \/
          (?C. Box C SUBFORMULA p /\
           (Box B = Box(C --> Box C)))) ==>
         (MEM (Box B) w ==> MEM (Box B) x))`;;

let TRANSITIVE_Q_REL = prove
 (`!p. TRANSITIVE (S4GRZ_STANDARD_WORLDS p) (Q_REL p)`,
  REWRITE_TAC[TRANSITIVE; Q_REL_DEF] THEN MESON_TAC[]);;

let S4GRZ_STANDARD_REL_DEF = new_definition
  `S4GRZ_STANDARD_REL p w x <=>
    w IN S4GRZ_STANDARD_WORLDS p  /\
    x IN S4GRZ_STANDARD_WORLDS p  /\
    Q_REL p w x /\ (Q_REL p x w ==> w = x)`;;

(* ------------------------------------------------------------------------- *)
(* The standard relation for S4GRZ is Reflexive, Antisymmetric               *)
(* and Transitive.                                                           *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_STANDARD_REL_PROP = prove
 (`!p. REFLEXIVE (S4GRZ_STANDARD_WORLDS p) (S4GRZ_STANDARD_REL p) /\
       ANTISYMMETRIC (S4GRZ_STANDARD_WORLDS p) (S4GRZ_STANDARD_REL p) /\
       TRANSITIVE (S4GRZ_STANDARD_WORLDS p) (S4GRZ_STANDARD_REL p)`,
  GEN_TAC THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC[REFLEXIVE; S4GRZ_STANDARD_REL_DEF; Q_REL_DEF];
   REWRITE_TAC[ANTISYMMETRIC; S4GRZ_STANDARD_REL_DEF] THEN
   INTRO_TAC "!w w'; w w' (w w' (wQw' w'Qw_then)) (w w' (w'Qw wqw'_then))" THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[TRANSITIVE; S4GRZ_STANDARD_REL_DEF] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[TRANSITIVE_Q_REL; TRANSITIVE];
    DISCH_TAC THEN
    SUBGOAL_THEN `(w':(form)list) = w'' /\ w = w'` MP_TAC THENL
    [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_MESON_TAC[TRANSITIVE_Q_REL; TRANSITIVE];
     ASM_MESON_TAC[]]]]);;

let S4GRZ_STANDARD_FRAME_DEF = new_definition
 `S4GRZ_STANDARD_FRAME p =
  {(W,R) | W = S4GRZ_STANDARD_WORLDS p /\
           R = S4GRZ_STANDARD_REL p}`;;

let S4GRZ_STANDARD_MODEL_DEF = new_definition
 `S4GRZ_STANDARD_MODEL p (W,R) V <=>
  (W,R) IN S4GRZ_STANDARD_FRAME p /\
  (!a w. w IN W
         ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`;;

(* ------------------------------------------------------------------------- *)
(* Maximal Consistent Lemmas.                                                *)
(* ------------------------------------------------------------------------- *)

let EXTEND_MAXIMAL_CONSISTENT'' = prove
 (`!S p X. CONSISTENT S X /\
           (!q. MEM q X ==> q SUBSENTENCE p \/
                            (?C. Box C SUBFORMULA p /\
                                 (q = Box (C --> Box C) \/
                                  q = Not Box (C --> Box C))))
           ==> ?M. MAXIMAL_CONSISTENT S p M /\
                   (!q. MEM q M ==> q SUBSENTENCE p  \/
                            (?C. Box C SUBFORMULA p /\
                                 (q = Box (C --> Box C) \/
                                  q = Not Box (C --> Box C)))) /\
                   X SUBLIST M`,
  GEN_TAC THEN GEN_TAC THEN SUBGOAL_THEN
    `!L X. CONSISTENT S X /\ NOREPETITION X /\
           (!q. MEM q X ==> q SUBSENTENCE p \/
                            (?C. Box C SUBFORMULA p /\
                                 (q = Box (C --> Box C) \/
                                  q = Not Box (C --> Box C)))) /\
           (!q. MEM q L ==> q SUBFORMULA p) /\
           (!q. q SUBFORMULA p ==> MEM q L \/ MEM q X \/ MEM (Not q) X)
           ==> ?M. MAXIMAL_CONSISTENT S p M /\
                   (!q. MEM q M ==> q SUBSENTENCE p \/
                            (?C. Box C SUBFORMULA p /\
                                 (q = Box (C --> Box C) \/
                                  q = Not Box (C --> Box C)))) /\
                   X SUBLIST M`
    (LABEL_TAC "P") THENL
  [ALL_TAC;
   INTRO_TAC "![X']; cons' subf'" THEN
   DESTRUCT_TAC "@X. uniq sub1 sub2"
     (ISPEC `X':form list` EXISTS_NOREPETITION) THEN
   DESTRUCT_TAC "@L'. uniq L'" (SPEC `p:form` SUBFORMULA_LIST) THEN
   HYP_TAC "P: +" (SPECL[`L':form list`; `X:form list`]) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[CONSISTENT_SUBLIST]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBLIST];
    ALL_TAC] THEN
   INTRO_TAC "@M. max sub" THEN EXISTS_TAC `M:form list` THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBLIST_TRANS]] THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[MEM] THEN INTRO_TAC "!X; X uniq max subf" THEN
   EXISTS_TAC `X:form list` THEN
   ASM_REWRITE_TAC[SUBLIST_REFL; MAXIMAL_CONSISTENT];
   ALL_TAC] THEN
  POP_ASSUM (LABEL_TAC "hpind") THEN REWRITE_TAC[MEM] THEN
  INTRO_TAC "!X; cons uniq qmem qmem' subf" THEN
  LABEL_ASM_CASES_TAC "hmemX" `MEM (h:form) X` THENL
  [REMOVE_THEN "hpind" (MP_TAC o SPEC `X:form list`) THEN
   ASM_MESON_TAC[]; ALL_TAC] THEN
  LABEL_ASM_CASES_TAC "nhmemX" `MEM (Not h) X` THENL
  [REMOVE_THEN "hpind" (MP_TAC o SPEC `X:form list`) THEN
   ASM_MESON_TAC[]; ALL_TAC] THEN
  LABEL_ASM_CASES_TAC "consh" `CONSISTENT S (CONS (h:form) X)` THENL
  [REMOVE_THEN "hpind" (MP_TAC o SPEC `CONS (h:form) X`) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[NOREPETITION_CLAUSES; MEM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_MESON_TAC[SUBLIST; SUBFORMULA_IMP_SUBSENTENCE];
    ALL_TAC] THEN
   INTRO_TAC "@M. max sub" THEN EXISTS_TAC `M:form list` THEN
   ASM_REWRITE_TAC[] THEN REMOVE_THEN "sub" MP_TAC THEN
   REWRITE_TAC[SUBLIST; MEM] THEN MESON_TAC[];
   ALL_TAC] THEN
  REMOVE_THEN "hpind" (MP_TAC o SPEC `CONS (Not h) X`) THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[NOREPETITION_CLAUSES] THEN
   CONJ_TAC THENL [ASM_MESON_TAC[CONSISTENT_EM]; ALL_TAC] THEN
   REWRITE_TAC[MEM] THEN ASM_MESON_TAC[SUBLIST; SUBSENTENCE_RULES];
   ALL_TAC] THEN
  INTRO_TAC "@M. max sub" THEN EXISTS_TAC `M:form list` THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "sub" MP_TAC THEN
  REWRITE_TAC[SUBLIST; MEM] THEN MESON_TAC[]);;

let NONEMPTY_MAXIMAL_CONSISTENT'' = prove
 (`!S p. ~ [S . {} |~ p]
         ==> ?M. MAXIMAL_CONSISTENT S p M /\
                 MEM (Not p) M /\
                 (!q. MEM q M ==> q SUBSENTENCE p \/
                                   (?C. Box C SUBFORMULA p /\
                                       (q = Box (C --> Box C) \/
                                        q = Not Box (C --> Box C))))`,
  INTRO_TAC "!S p; p" THEN
  MP_TAC (SPECL [`S:form->bool`; `p:form`; `[Not p]`]
    EXTEND_MAXIMAL_CONSISTENT'') THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[CONSISTENT_SING] THEN ASM_MESON_TAC[MLK_DOUBLENEG_CL];
    ALL_TAC] THEN
   GEN_TAC THEN REWRITE_TAC[MEM] THEN
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
   MESON_TAC[SUBFORMULA_IMP_NEG_SUBSENTENCE; SUBFORMULA_REFL];
   ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `M:form list` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBLIST; MEM]);;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_TRUTH_LEMMA = prove
 (`!W R p V q. ~[S4GRZ_AX . {} |~ p] /\
     q SUBFORMULA p /\ S4GRZ_STANDARD_MODEL p (W,R) V
     ==> !w. w IN W  ==> (MEM q w <=> holds (W,R) V q w)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[S4GRZ_STANDARD_MODEL_DEF; S4GRZ_STANDARD_FRAME_DEF;
              S4GRZ_STANDARD_WORLDS_DEF; S4GRZ_STANDARD_REL_DEF;
              IN_ELIM_THM; PAIR_EQ] THEN
  INTRO_TAC "np q (@W' R'. (W' R') WW' RR' ) val" THEN
  REMOVE_THEN "WW'" SUBST_VAR_TAC THEN
  REMOVE_THEN "RR'" SUBST_VAR_TAC THEN
  REMOVE_THEN "W'" SUBST_ALL_TAC THEN
  REMOVE_THEN "R'" SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
  HYP_TAC "val" (REWRITE_RULE[FORALL_IN_GSPEC]) THEN
  REMOVE_THEN "q" MP_TAC THEN
  GEN_FORM_INDUCT_TAC `q:form` THEN REWRITE_TAC[holds]  THEN
  INTRO_TAC "sub; !w; max_cons mem" THEN
  TRY
    (REMOVE_THEN "q1_hpind" MP_TAC THEN
     MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
     CONJ_TAC THENL
     [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
      INTRO_TAC "sub1 +" THEN DISCH_THEN (MP_TAC o SPEC `w:form list`)] THEN
     REMOVE_THEN "q2_hpind" MP_TAC THEN
     MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
     CONJ_TAC THENL
     [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
      INTRO_TAC "sub2 +" THEN DISCH_THEN (MP_TAC o SPEC `w:form list`)] THEN
     ASM_REWRITE_TAC[] THEN
     INTRO_TAC "a; b" THEN
     HYP_TAC "a" (GSYM) THEN ASM_REWRITE_TAC[] THEN
     HYP_TAC "b" (GSYM) THEN ASM_REWRITE_TAC[] THEN
     CLAIM_TAC "rmk"
       `!q. q SUBFORMULA p
            ==> (MEM q w <=> [S4GRZ_AX. {} |~ CONJLIST w --> q])` THENL
     [ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE];
      ALL_TAC]) THENL
  [
   (* q = False *)
   HYP_TAC "max_cons -> cons memq" (REWRITE_RULE[MAXIMAL_CONSISTENT]) THEN
   ASM_MESON_TAC[FALSE_IMP_NOT_CONSISTENT]
  ;
   (* q = True *)
   HYP_TAC "max_cons: (cons (norep mem))"
         (REWRITE_RULE[MAXIMAL_CONSISTENT]) THEN
   HYP_TAC "mem: t | nt" (C MATCH_MP (ASSUME `True SUBFORMULA p`)) THEN
   ASM_REWRITE_TAC[] THEN REFUTE_THEN (K ALL_TAC) THEN
   HYP MESON_TAC "cons nt" [NOT_CONSISTENT_1; MLK_DOUBLENEG; MLK_truth_th]
  ;
   (* q = Atom *)
   ASM_SIMP_TAC[]
  ;
   (* q = Not a *)
   REMOVE_THEN "q_hpind" MP_TAC THEN
   MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
   INTRO_TAC "sub1 q" THEN
   EQ_TAC THENL
   [REMOVE_THEN "q" (MP_TAC o SPEC `w: form list`) THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT];
    REMOVE_THEN "q" (MP_TAC o SPEC `w: form list`) THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT]]]
  ;
   (* q = q1 && q2 *)
   ASM_SIMP_TAC[] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE;
    MLK_and_intro; MLK_and_left_th; MLK_and_right_th; MLK_imp_trans]
  ;
   (* q = q1 || q2 *)
   EQ_TAC THENL
   [INTRO_TAC "q1q2" THEN
     CLAIM_TAC "wq1q2" `[S . {} |~ CONJLIST w --> q1 || q2]` THENL
     [ASM_SIMP_TAC[CONJLIST_IMP_MEM]; ALL_TAC] THEN
     CLAIM_TAC "hq1 | hq1" `MEM q1 w \/ MEM (Not q1) w` THENL
     [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CLAIM_TAC "hq2 | hq2" `MEM q2 w \/ MEM (Not q2) w` THENL
     [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
      ASM_REWRITE_TAC[]; REFUTE_THEN (K ALL_TAC)] THEN
     SUBGOAL_THEN `~ ([S4GRZ_AX . {} |~ (CONJLIST w --> False)])` MP_TAC THENL
     [REWRITE_TAC[GSYM MLK_not_def] THEN
      HYP_TAC "max_cons : not norep sub" (REWRITE_RULE[MAXIMAL_CONSISTENT; CONSISTENT]) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLK_frege THEN EXISTS_TAC `q1 || q2` THEN
     ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN MATCH_MP_TAC MLK_imp_swap THEN
     REWRITE_TAC[MLK_disj_imp] THEN CONJ_TAC THEN MATCH_MP_TAC MLK_imp_swap THEN
     ASM_MESON_TAC[CONJLIST_IMP_MEM; MLK_axiom_not; MLK_iff_imp1; MLK_imp_trans];
    ASM_MESON_TAC[MLK_or_left_th; MLK_or_right_th; MLK_imp_trans;
                  MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE]]
  ;
  (* q = q1 --> q2 *)
  EQ_TAC THENL
  [ASM_MESON_TAC[MLK_frege; CONJLIST_IMP_MEM;
                 MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE];
   INTRO_TAC "imp" THEN
    CLAIM_TAC "hq1 | hq1" `MEM q1 w \/ MEM (Not q1) w` THENL
    [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
     ASM_MESON_TAC[CONJLIST_IMP_MEM; MLK_imp_swap; MLK_add_assum;
     MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE];
     ALL_TAC] THEN
    MP_TAC (SPECL[`S4GRZ_AX`; `p:form`; `w:form list`; `q1 --> q2`]
            MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MLK_shunt THEN MATCH_MP_TAC MLK_imp_trans THEN
          EXISTS_TAC `q1 && Not q1` THEN CONJ_TAC THENL
          [ALL_TAC; MESON_TAC[MLK_nc_th; MLK_imp_trans; MLK_ex_falso_th]] THEN
          MATCH_MP_TAC MLK_and_intro THEN REWRITE_TAC[MLK_and_right_th] THEN
          ASM_MESON_TAC[CONJLIST_IMP_MEM; MLK_imp_trans; MLK_and_left_th]]
  ;
   (* q = q1 <-> q2 *)
   ASM_SIMP_TAC[] THEN REMOVE_THEN "sub" (K ALL_TAC) THEN EQ_TAC THENL
   [MESON_TAC[MLK_frege; MLK_add_assum; MLK_modusponens_th;
           MLK_axiom_iffimp1; MLK_axiom_iffimp2];
   ALL_TAC] THEN
   INTRO_TAC "iff" THEN MATCH_MP_TAC MLK_imp_trans THEN
   EXISTS_TAC `(q1 --> q2) && (q2 --> q1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MLK_and_intro; MESON_TAC[MLK_iff_def_th; MLK_iff_imp2]] THEN
   CLAIM_TAC "rmk'"
     `!q. q SUBFORMULA p
         ==> (MEM (Not q) w <=> [S4GRZ_AX. {} |~ CONJLIST w --> Not q])` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_NEG_EQ_DERIVABLE];
    ALL_TAC] THEN
   CLAIM_TAC "hq1 | hq1"
    `[S4GRZ_AX. {} |~ (CONJLIST w --> q1)] \/
     [S4GRZ_AX. {} |~ CONJLIST w --> Not q1]` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
    ASM_MESON_TAC[MLK_imp_swap; MLK_add_assum];
    ALL_TAC] THEN
  CLAIM_TAC "hq2 | hq2"
     `[S4GRZ_AX. {} |~ (CONJLIST w --> q2)] \/
     [S4GRZ_AX. {} |~ (CONJLIST w --> Not q2)]` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
    ASM_MESON_TAC[MLK_imp_swap; MLK_add_assum];
    ALL_TAC] THEN
   ASM_MESON_TAC[MLK_nc_th; MLK_imp_trans; MLK_and_intro;
                  MLK_ex_falso_th; MLK_imp_swap; MLK_shunt]
  ;
  (* q = Box q1*)
  CLAIM_TAC "suba" `q SUBFORMULA p` THENL
  [MATCH_MP_TAC SUBFORMULA_TRANS THEN EXISTS_TAC `Box q` THEN
   ASM_REWRITE_TAC[SUBFORMULA_INVERSION; SUBFORMULA_REFL];
   ALL_TAC] THEN
  ASM_CASES_TAC `MEM (Box q)  (w:form list)` THENL
  [ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    INTRO_TAC "!w'; (max_cons_w mem_w') ww'" THEN
    CLAIM_TAC "memw'" `MEM q  (w':form list)` THENL
    [MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA THEN
     EXISTS_TAC `S4GRZ_AX` THEN
     EXISTS_TAC `p:form` THEN
     EXISTS_TAC `[Box q]` THEN
     ASM_REWRITE_TAC[MEM] THEN
     CONJ_TAC THENL
     [INTRO_TAC "!q'; eq" THEN ASM_REWRITE_TAC[] THEN
       HYP_TAC "ww': w w' (w w' wQw') w'Qw_then"
         (REWRITE_RULE[S4GRZ_STANDARD_REL_DEF; Q_REL_DEF; SUBSENTENCE_CASES]) THEN
       ASM_MESON_TAC[];
      ASM_MESON_TAC[CONJLIST; GRZ_PROVES_T; T_SCHEMA_DEF; GRZ_EQ_S4GRZ]]; ALL_TAC] THEN
    HYP_TAC "q_hpind" (C MATCH_MP (ASSUME `q SUBFORMULA p`)) THEN
    HYP_TAC "q_hpind: +" (SPEC `w':form list`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN (SUBST1_TAC o GSYM) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
   ASM_REWRITE_TAC[IN_ELIM_THM; NOT_FORALL_THM; NOT_IMP] THEN
   CLAIM_TAC "NotBox_mem" `MEM (Not Box q) (w:form list)` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT]; ALL_TAC] THEN
   ASM_CASES_TAC `~(MEM q (w:form list))` THENL
   [EXISTS_TAC `w:form list` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MP_TAC (SPEC `p:form` S4GRZ_STANDARD_REL_PROP) THEN
      ASM_REWRITE_TAC[REFLEXIVE] THEN
      INTRO_TAC "refl antsym trans" THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[S4GRZ_STANDARD_WORLDS_DEF; IN_ELIM_THM; S4GRZ_STANDARD_REL_PROP];
     HYP_TAC "q_hpind" (C MATCH_MP (ASSUME `q SUBFORMULA p`)) THEN
     HYP_TAC "q_hpind: +" (SPEC `w:form list`) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     DISCH_THEN (SUBST1_TAC o GSYM) THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  FIRST_ASSUM MP_TAC THEN REWRITE_TAC[] THEN INTRO_TAC "q_mem" THEN
  CLAIM_TAC "Box_imp_Box_not_mem" `~(MEM (Box (q --> Box q)) (w:form list))` THENL
  [REFUTE_THEN MP_TAC THEN INTRO_TAC "Box_imp_Box_mem" THEN
   SUBGOAL_THEN `MEM (Box q) (w:form list)` MP_TAC THENL
   [MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA THEN
    EXISTS_TAC `S4GRZ_AX` THEN
    EXISTS_TAC `p:form` THEN
    EXISTS_TAC `[Box (q --> Box q); q]` THEN
    ASM_REWRITE_TAC[MEM] THEN
    CONJ_TAC THENL
    [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[CONJLIST; NOT_CONS_NIL] THEN MATCH_MP_TAC S4GRZ_prove_S4 THEN
      HOLMS_TAC] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
   CLAIM_TAC "consistent_X"
             `CONSISTENT S4GRZ_AX
               (CONS (Not q)
                     (APPEND (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
                             [Box (q --> Box q)]))` THENL
   [REFUTE_THEN MP_TAC THEN
    INTRO_TAC "non_cons" THEN
    HYP_TAC "non_cons" (REWRITE_RULE[CONSISTENT; CONJLIST; APPEND_EQ_NIL; NOT_CONS_NIL]) THEN
    CLAIM_TAC "1" `[S4GRZ_AX . {} |~ Not (Not q &&
                                          (CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w) &&
                                           CONJLIST [Box (q --> Box q)]))]` THENL
    [MATCH_MP_TAC MLK_not_subst_th THEN
     EXISTS_TAC `Not q &&
                 CONJLIST (APPEND (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
                                   [Box (q --> Box q)])` THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC MLK_and_subst_th THEN
     ASM_REWRITE_TAC[MLK_iff_refl_th; CONJLIST_APPEND; CONJLIST]; ALL_TAC] THEN
    HYP_TAC "1" (REWRITE_RULE[CONJLIST]) THEN
    CLAIM_TAC "2" `[S4GRZ_AX . {} |~ Box Box CONJLIST (FLATMAP (\x. match x with Box c -> [ Box c] | _ -> []) w) --> Box q]` THENL
    [MATCH_MP_TAC MLK_imp_box THEN
     MATCH_MP_TAC MLK_imp_trans THEN
     EXISTS_TAC `Box (Box (q --> Box q) --> q)` THEN
     ASM_REWRITE_TAC[S4GRZ_AX_GRZ] THEN
     MATCH_MP_TAC MLK_imp_box THEN
     MATCH_MP_TAC MLK_iff_mp THEN
     EXISTS_TAC `Not (Not q &&
                      CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w) &&
                                Box (q --> Box q))` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC S4GRZ_prove_S4 THEN
       CLAIM_TAC "s4" `!a b c. [S4_AX . {} |~ Not (Not a && b && c) <-> b --> (c --> a)]` THENL
       [HOLMS_TAC; ALL_TAC] THEN
       ASM_MESON_TAC[];
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    CLAIM_TAC "3" `[S4GRZ_AX . {} |~ CONJLIST (FLATMAP (\x. match x with Box c -> [ Box c] | _ -> []) w) --> Box q]` THENL
    [MATCH_MP_TAC MLK_imp_trans THEN
     EXISTS_TAC `Box Box CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)` THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC MLK_imp_mp_subst THEN
     EXISTS_TAC `CONJLIST (MAP (Box)
                               (FLATMAP (\x. match x with Box c -> [c] | _ -> [])w))` THEN
     EXISTS_TAC `Box Box CONJLIST (MAP (Box)
                              (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w))` THEN
     REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MLK_iff_sym] THEN
       MATCH_ACCEPT_TAC (CONJLIST_FLATMAP_DOT_BOX_LEMMA_3);
      MATCH_MP_TAC MLK_box_subst THEN
       MATCH_MP_TAC MLK_box_subst THEN
       REWRITE_TAC[MLK_iff_sym] THEN
       MATCH_ACCEPT_TAC (CONJLIST_FLATMAP_DOT_BOX_LEMMA_3);
      MATCH_MP_TAC MLK_imp_mp_subst]
     THEN
     EXISTS_TAC `Box CONJLIST
                      (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)` THEN
     EXISTS_TAC `Box Box Box CONJLIST
                              (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)`THEN
     REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC I [MLK_iff_sym] THEN
       ASM_REWRITE_TAC[CONJLIST_MAP_BOX];
      GEN_REWRITE_TAC I [MLK_iff_sym] THEN
       MATCH_MP_TAC MLK_box_subst THEN
       MATCH_MP_TAC MLK_box_subst THEN
       ASM_REWRITE_TAC[CONJLIST_MAP_BOX];
      MATCH_MP_TAC S4GRZ_prove_S4 THEN
       CLAIM_TAC "s4" `!q. [S4_AX . {} |~  Box q --> Box Box Box q]` THENL
       [HOLMS_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[]]; ALL_TAC] THEN
    SUBGOAL_THEN `MEM (Box q) w` MP_TAC THENL
    [MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA THEN
     EXISTS_TAC `S4GRZ_AX` THEN
     EXISTS_TAC `p:form` THEN
     EXISTS_TAC `FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w` THEN
     ASM_MESON_TAC[MEM_FLATMAP_LEMMA_2]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]; ALL_TAC]  THEN
   CLAIM_TAC "@x. max_cons_x mem_x subl"
             `?x. MAXIMAL_CONSISTENT S4GRZ_AX p x /\
                  (!q. MEM q x ==> q SUBSENTENCE p \/
                                   (?C. Box C SUBFORMULA p /\
                                       (q = Box (C --> Box C) \/
                                         q = Not Box (C --> Box C)))) /\
                  (CONS (Not q) (APPEND (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
                                        [Box (q --> Box q)]))
                   SUBLIST x` THENL
   [MATCH_MP_TAC (EXTEND_MAXIMAL_CONSISTENT'') THEN
    ASM_REWRITE_TAC[MEM; MEM_APPEND; CONSISTENT] THEN
    REPEAT STRIP_TAC THENL
    [DISJ1_TAC THEN
      ASM_REWRITE_TAC[SUBSENTENCE_CASES] THEN
      DISJ2_TAC THEN
      EXISTS_TAC `q:form` THEN
      ASM_REWRITE_TAC[];
     CLAIM_TAC "@r. Box mem_w" `?r. q' = Box r /\ MEM q' w` THENL
      [ASM_MESON_TAC[MEM_FLATMAP_LEMMA_2]; ALL_TAC] THEN
      ASM_MESON_TAC[];
     ASM_MESON_TAC[]]; ALL_TAC] THEN
   EXISTS_TAC `x: form list` THEN
   ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[S4GRZ_STANDARD_REL_DEF; S4GRZ_STANDARD_WORLDS_DEF; IN_ELIM_THM] THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[Q_REL_DEF; S4GRZ_STANDARD_WORLDS_DEF; IN_ELIM_THM] THEN
       REPEAT STRIP_TAC THENL
      [SUBGOAL_THEN `MEM (Box B) (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)` MP_TAC THENL
         [ASM_REWRITE_TAC[MEM_FLATMAP_LEMMA_2] THEN
          ASM_MESON_TAC[]; ALL_TAC] THEN
         HYP_TAC "subl" (REWRITE_RULE[SUBLIST; MEM; MEM_APPEND]) THEN
         ASM_MESON_TAC[];
        ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN `MEM (Box B) (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)` MP_TAC THENL
         [ASM_REWRITE_TAC[MEM_FLATMAP_LEMMA_2] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
         HYP_TAC "subl" (REWRITE_RULE[SUBLIST; MEM; MEM_APPEND]) THEN ASM_MESON_TAC[]];
      GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
       DISCH_TAC THEN
       ASM_REWRITE_TAC[Q_REL_DEF; DE_MORGAN_THM; TAUT `(~p \/ ~q \/ ~r) <=> (p /\ q ==> ~ r)`;
                               NOT_FORALL_THM; NOT_IMP] THEN
       DISJ2_TAC THEN DISJ2_TAC THEN
       EXISTS_TAC `q --> Box q` THEN
       CONJ_TAC THENL
       [DISJ2_TAC THEN EXISTS_TAC `q:form` THEN
         ASM_REWRITE_TAC[];
        REWRITE_TAC[TAUT `~(p <=> q) <=> (p /\ ~q) \/ (~p /\ q)`] THEN
        CONJ_TAC THENL
        [HYP_TAC "subl" (REWRITE_RULE[SUBLIST; MEM; MEM_APPEND]) THEN
          ASM_MESON_TAC[];
         ASM_REWRITE_TAC[]]]];
   SUBGOAL_THEN `~(MEM (q:form) x)` MP_TAC THENL
   [SUBGOAL_THEN `MEM (Not q) x` MP_TAC THENL
    [HYP_TAC "subl" (REWRITE_RULE[SUBLIST; MEM; MEM_APPEND]) THEN
     ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT]; ALL_TAC] THEN
   HYP_TAC "q_hpind -> +" (REWRITE_RULE[]) THEN
   MATCH_MP_TAC (MESON[] `P /\ (Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
   ASM_REWRITE_TAC[] THEN
   INTRO_TAC "a" THEN
   HYP_TAC "a" (SPEC `x: form list`) THEN
   ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Proof of Completeness w.r.t. RATF.                                        *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_COMPLETENESS_THM = prove
 (`!p. RATF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [S4GRZ_AX . {} |~ p]`,
  GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  INTRO_TAC "p_not_theor" THEN
  REWRITE_TAC[valid; NOT_FORALL_THM] THEN
  EXISTS_TAC `(S4GRZ_STANDARD_WORLDS p,
                S4GRZ_STANDARD_REL p)` THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
  [ASM_REWRITE_TAC[IN_RATF; S4GRZ_STANDARD_REL_PROP; IN_FINITE_FRAME;
                   S4GRZ_STANDARD_WORLDS_DEF] THEN
  CONJ_TAC THENL (* non empty *)
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    SUBGOAL_THEN `(?M. MAXIMAL_CONSISTENT S4GRZ_AX p M /\
                          MEM (Not p) M /\
                          (!q. MEM q M ==>
                               q SUBSENTENCE p \/
                               (?C. Box C SUBFORMULA p /\
                                (q = Box (C --> Box C) \/
                                 q = Not Box (C --> Box C)))))`
                   MP_TAC THENL
    [MATCH_MP_TAC NONEMPTY_MAXIMAL_CONSISTENT'' THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
    INTRO_TAC "@M. max mem sub" THEN
    EXISTS_TAC`M:form list` THEN
    ASM_REWRITE_TAC[];
   CONJ_TAC THENL (* well define *)
   [REWRITE_TAC[S4GRZ_STANDARD_REL_DEF; S4GRZ_STANDARD_WORLDS_DEF] THEN
   INTRO_TAC "!x y; x y Q" THEN ASM_REWRITE_TAC[];
    (* finite *)
  MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `{l | NOREPETITION l /\
                    !q. MEM q l ==>
                        q IN {q | q SUBSENTENCE p \/
                                  (?C. Box C SUBFORMULA p /\
                                       (q = Box (C --> Box C) \/
                                        q = Not Box (C --> Box C)))}}` THEN
   CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[MAXIMAL_CONSISTENT]] THEN
   MATCH_MP_TAC FINITE_NOREPETITION THEN
   POP_ASSUM_LIST (K ALL_TAC) THEN
   SUBGOAL_THEN `{q | q SUBSENTENCE p  \/
                      (?C. Box C SUBFORMULA p /\
                           (q = Box (C --> Box C) \/
                            q = Not Box (C --> Box C)))} =
                 {q | q SUBFORMULA p} UNION
                 IMAGE (Not) {q | q SUBFORMULA p} UNION
                 {q | ?C. (C IN {q | Box q IN {q | q SUBFORMULA p}}) /\
                                     q = Box (C --> Box C)} UNION
                 IMAGE (Not) {q | ? C. (C  IN {q | Box q IN {q | q SUBFORMULA p}}) /\
                                      q = Box (C --> Box C)}`
     SUBST1_TAC THENL
  [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_UNION;
                FORALL_IN_GSPEC; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM; SUBSENTENCE_RULES] THEN
    REPEAT CONJ_TAC THENL
    [GEN_TAC THEN REWRITE_TAC[SUBSENTENCE_CASES] THEN
     STRIP_TAC THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    MESON_TAC[SUBSENTENCE_CASES];
    MESON_TAC[SUBSENTENCE_CASES];
    MESON_TAC[SUBSENTENCE_CASES];
    MESON_TAC[SUBSENTENCE_CASES]];
   REWRITE_TAC[FINITE_UNION; FINITE_SUBFORMULA] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_SUBFORMULA];
     CONJ_TAC THENL
     [MATCH_MP_TAC     FINITE_IMAGE_EXPAND     THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{q | q SUBFORMULA p}` THEN
        REWRITE_TAC[FINITE_SUBFORMULA; SUBSET; IN_ELIM_THM] THEN
        INTRO_TAC "!x; Box_sub" THEN
        MATCH_MP_TAC SUBFORMULA_TRANS THEN
        EXISTS_TAC `Box x` THEN
        ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[SUBFORMULA_CASES_L] THEN
        DISJ2_TAC THEN EXISTS_TAC `x: form` THEN
        ASM_REWRITE_TAC[SUBFORMULA_REFL; IN_MINOR_CASES];
        MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_IMAGE_EXPAND THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{q | q SUBFORMULA p}` THEN
        REWRITE_TAC[FINITE_SUBFORMULA; SUBSET; IN_ELIM_THM] THEN
        INTRO_TAC "!x; Box_sub" THEN
        MATCH_MP_TAC SUBFORMULA_TRANS THEN
        EXISTS_TAC `Box x` THEN
        ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[SUBFORMULA_CASES_L] THEN
        DISJ2_TAC THEN EXISTS_TAC `x: form` THEN
      ASM_REWRITE_TAC[SUBFORMULA_REFL; IN_MINOR_CASES]]]]]];
  ASM_REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP] THEN
   EXISTS_TAC `\a M. Atom a SUBFORMULA p /\ MEM (Atom a) M` THEN
   DESTRUCT_TAC "@M. max mem subf"
      (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT'' (ASSUME `~ [S4GRZ_AX . {} |~ p]`)) THEN
   EXISTS_TAC `M:form list` THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[S4GRZ_STANDARD_WORLDS_DEF; IN_ELIM_THM];
   MP_TAC (ISPECL [`S4GRZ_STANDARD_WORLDS p`;
                   `S4GRZ_STANDARD_REL p`;
                   `p:form`;
                   `(\a M. Atom a SUBFORMULA p /\ MEM (Atom a) M)`;
                   `p:form`] S4GRZ_TRUTH_LEMMA) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBFORMULA_REFL] THEN
    ASM_REWRITE_TAC[S4GRZ_STANDARD_MODEL_DEF; S4GRZ_STANDARD_FRAME_DEF;
                   IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    DISCH_THEN (MP_TAC o SPEC `M:form list`) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[S4GRZ_STANDARD_WORLDS_DEF; IN_ELIM_THM];
     DISCH_THEN (SUBST1_TAC o GSYM) THEN
     ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT_NC]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Completeness Theorem for S4Grz on a generic (infinite) domain.            *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_COMPLETENESS_THM_GEN = prove
 (`!p. INFINITE (:A) /\ RATF:(A->bool)#(A->A->bool)->bool |= p
       ==> [S4GRZ_AX . {} |~ p]`,
  SUBGOAL_THEN
    `INFINITE (:A)
     ==> !p. RATF:(A->bool)#(A->A->bool)->bool |= p
             ==> RATF:(form list->bool)#(form list->form list->bool)->bool |= p`
    (fun th -> MESON_TAC[th; S4GRZ_COMPLETENESS_THM]) THEN
  INTRO_TAC "A" THEN MATCH_MP_TAC BISIMILAR_VALID THEN
  REWRITE_TAC[IN_RATF] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "(finite1 refl trans anti) w1" THEN
  CLAIM_TAC "@f. inj" `?f:form list->A. (!x y. f x = f y ==> x = y)` THENL
  [SUBGOAL_THEN `(:form list) <=_c (:A)` MP_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:num)` THEN
    ASM_REWRITE_TAC[GSYM INFINITE_CARD_LE; GSYM COUNTABLE_ALT] THEN
    ASM_SIMP_TAC[COUNTABLE_LIST; COUNTABLE_FORM];
    REWRITE_TAC[le_c; IN_UNIV]];
   ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
    [`IMAGE (f:form list->A) W1`;
     `\x y:A. ?a b:form list.
        a IN W1 /\ b IN W1 /\ x = f a /\ y = f b /\ R1 a b`;
     `\a:string w:A. ?x:form list. w = f x /\ V1 a x`;
     `f (w1:form list):A`] THEN
   CONJ_TAC THENL
  [REWRITE_TAC[IN_FINITE_FRAME] THEN
   CONJ_TAC THENL
   [CONJ_TAC THENL [HYP SET_TAC "w1" []; ALL_TAC] THEN
   CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[IN_FINITE_FRAME; FINITE_IMAGE]; ALL_TAC] THEN
   CONJ_TAC THENL
   [REWRITE_TAC[REFLEXIVE; FORALL_IN_IMAGE] THEN
    HYP_TAC "refl" (REWRITE_RULE[REFLEXIVE]) THEN
    HYP MESON_TAC "refl inj" [];
    ALL_TAC] THEN
    CONJ_TAC THENL
   [REWRITE_TAC[TRANSITIVE; FORALL_IN_IMAGE] THEN
    HYP_TAC "trans" (REWRITE_RULE[TRANSITIVE]) THEN
    HYP MESON_TAC "trans inj" [];
    ALL_TAC] THEN
    REWRITE_TAC[ANTISYMMETRIC; FORALL_IN_IMAGE] THEN
    HYP_TAC "anti" (REWRITE_RULE[ANTISYMMETRIC]) THEN
    HYP MESON_TAC "anti inj" []; ALL_TAC] THEN
    REWRITE_TAC[BISIMILAR] THEN
    EXISTS_TAC `\w1:form list w2:A. w1 IN W1 /\ w2 = f w1` THEN
    ASM_REWRITE_TAC[BISIMIMULATION] THEN REMOVE_THEN "w1" (K ALL_TAC) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    CONJ_TAC THENL [HYP MESON_TAC "inj" []; ALL_TAC] THEN
    CONJ_TAC THENL
    [REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[IN_FINITE_FRAME];
    ALL_TAC] THEN
    ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. Adequacy Theorem                                                       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Semantical Adequacy of Grz.                                               *)
(* ------------------------------------------------------------------------- *)

let GRZ_ADEQ_THM = prove
 (`!p. RATF:(form list->bool)#(form list->form list->bool)->bool |= p
       <=> [GRZ_AX . {} |~ p]`,
  GEN_TAC THEN EQ_TAC THENL
   [INTRO_TAC "RATF" THEN REWRITE_TAC [GRZ_EQ_S4GRZ] THEN
   ASM_MESON_TAC [S4GRZ_COMPLETENESS_THM]; ALL_TAC] THEN
   INTRO_TAC "Grz" THEN MATCH_MP_TAC S4GRZ_RATF_VALID THEN
   ASM_MESON_TAC [GRZ_EQ_S4GRZ]);;

let GRZ_ADEQ_THM_num = prove
 (`!p. RATF:(num->bool)#(num->num->bool)->bool |= p
       <=> [GRZ_AX . {} |~ p]`,
  GEN_TAC THEN EQ_TAC THENL
   [INTRO_TAC "RATF" THEN REWRITE_TAC [GRZ_EQ_S4GRZ] THEN
   MATCH_MP_TAC (INST_TYPE [`:num`,`:A`] S4GRZ_COMPLETENESS_THM_GEN) THEN
   ASM_REWRITE_TAC[INFINITE_CARD_LE] THEN
   MATCH_MP_TAC CARD_EQ_IMP_LE THEN
   MATCH_ACCEPT_TAC CARD_EQ_REFL; ALL_TAC] THEN
   INTRO_TAC "Grz" THEN MATCH_MP_TAC S4GRZ_RATF_VALID THEN
   ASM_MESON_TAC [GRZ_EQ_S4GRZ]);;

(* ------------------------------------------------------------------------- *)
(* 6. Translation for Grz to GL.                                             *)
(* ------------------------------------------------------------------------- *)

let R_PLUS_DEF = new_definition
  `R_PLUS (W:W->bool) (R:W->W->bool) w x <=>
     ((R w x) \/ (w IN W /\ w = x))`;;

let R_MIN_DEF = new_definition
  `R_MIN (W:W->bool) (R:W->W->bool) (w:W) (x:W) <=>
     ((R w x) /\ ~((w IN W) /\ (w  = x)))`;;

let IRREFL_THEN_EQ = prove
(`!(W:W->bool) (R:W->W->bool). IRREFLEXIVE W R ==> R = R_MIN W R`,
  REWRITE_TAC[IRREFLEXIVE] THEN INTRO_TAC "!W R; irr" THEN
   REWRITE_TAC[FUN_EQ_THM; R_MIN_DEF; R_PLUS_DEF] THEN
   ASM_MESON_TAC[]);;

let REFL_THEN_EQ = prove
(`!(W:W->bool) (R:W->W->bool). REFLEXIVE W R ==> R = R_PLUS W (R_MIN W R)`,
  REWRITE_TAC[REFLEXIVE] THEN INTRO_TAC "!W R; ref" THEN
   REWRITE_TAC[FUN_EQ_THM; R_MIN_DEF; R_PLUS_DEF] THEN
   ASM_MESON_TAC[]);;

let ITF_IMP_R_PLUS_RATF = prove
 (`!W:W->bool R. (W,R) IN ITF ==> (W,R_PLUS W R) IN RATF`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_ITF; IN_RATF; IN_FINITE_FRAME] THEN
  INTRO_TAC "(non_empty rel FINITE) IRR TRANS" THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC[R_PLUS_DEF];
     MESON_TAC[REFLEXIVE; R_PLUS_DEF];
     HYP_TAC "TRANS" (REWRITE_RULE[TRANSITIVE]) THEN
      REWRITE_TAC[TRANSITIVE; R_PLUS_DEF] THEN
      ASM_MESON_TAC[];
     HYP_TAC "IRR" (REWRITE_RULE[IRREFLEXIVE]) THEN
     HYP_TAC "TRANS" (REWRITE_RULE[TRANSITIVE]) THEN
     ASM_REWRITE_TAC[ANTISYMMETRIC; R_PLUS_DEF] THEN
     ASM_MESON_TAC[]]);;

let GRZ_TRANSL_LEMMA = prove
  (`!p W R V w. (W:W->bool,R) IN ITF /\ w IN W ==>
           (holds (W,R) V (TRANSL p) w <=> holds (W,R_PLUS W R) V p w)`,
   FORM_INDUCT_TAC THENL
   [REWRITE_TAC[TRANSL; holds];
    REWRITE_TAC[TRANSL; holds];
    REWRITE_TAC[TRANSL; holds];
    ASM_REWRITE_TAC[TRANSL; holds] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[TRANSL; holds] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[TRANSL; holds] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[TRANSL; holds] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[TRANSL; holds] THEN ASM_MESON_TAC[];
    INTRO_TAC "!W R V w; ITF w" THEN
     REWRITE_TAC[TRANSL; dotbox_DEF; holds] THEN
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC
      `!w'.  w' IN (W:W->bool) /\ R_PLUS W R w w'
           ==> holds (W,R) V (TRANSL p) w'` THEN
     ASM_MESON_TAC[R_PLUS_DEF]]);;

let RATF_TRANSL = prove
  (`!p. RATF:(form list->bool)#(form list->form list->bool)->bool |= p
       <=> [GL_AX . {} |~ TRANSL (p)]`,
  ONCE_REWRITE_TAC [TAUT `(P <=> Q) <=> (~P <=> ~Q)`] THEN
   REWRITE_TAC[valid; holds_in; FORALL_PAIR_THM; NOT_FORALL_THM; NOT_IMP] THEN
   GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[IN_RATF; IN_FINITE_FRAME;
                TRANSITIVE; ANTISYMMETRIC; REFLEXIVE] THEN
    INTRO_TAC "@W R. ((non_empty rel FINITE) REFL TRANS ANTI) (@V w. IN not)" THEN
    MP_TAC (INST_TYPE [`:form list`,`:W`] GL_ITF_VALID) THEN
    INTRO_TAC "p" THEN
    HYP_TAC "p" (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[valid; holds_in; FORALL_PAIR_THM; NOT_FORALL_THM; NOT_IMP] THEN
    EXISTS_TAC `W:form list->bool` THEN
    EXISTS_TAC `R_MIN (W: form list->bool) (R:form list->form list->bool)` THEN
    ASM_REWRITE_TAC[IN_ITF; IN_FINITE_FRAME] THEN REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC[R_MIN_DEF];
     ASM_MESON_TAC[R_MIN_DEF; IRREFLEXIVE];
     REWRITE_TAC[TRANSITIVE; R_MIN_DEF] THEN ASM_MESON_TAC[];
     EXISTS_TAC `V:(char)list->(form)list->bool` THEN
      EXISTS_TAC `w:form list` THEN ASM_REWRITE_TAC[] THEN
      CLAIM_TAC "R_MIN_IN_ITF" `(W:form list->bool, R_MIN W R) IN ITF` THENL
      [ASM_REWRITE_TAC[IN_ITF; IN_FINITE_FRAME; TRANSITIVE] THEN
       REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[R_MIN_DEF];
        ASM_MESON_TAC[IRREFLEXIVE; R_MIN_DEF];
        ASM_REWRITE_TAC[R_MIN_DEF] THEN  ASM_MESON_TAC[]]; ALL_TAC] THEN
      MP_TAC (SPECL[`p:form`;
                     `W:form list->bool`;
                     `R_MIN W (R:form list -> form list ->bool)`;
                     `V:char list->form list->bool`;
                     `w:form list`] (INST_TYPE [`:form list`,`:W`] GRZ_TRANSL_LEMMA)) THEN
      ASM_REWRITE_TAC[TAUT `(A=> (B <=>C)) => D <=> A=> (B<=>C) => D`] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      CLAIM_TAC "R_EQ" `R_PLUS W (R_MIN W R) = (R:form list->form list->bool)` THENL
      [MATCH_MP_TAC (GSYM REFL_THEN_EQ) THEN
       ASM_REWRITE_TAC[REFLEXIVE] THEN
       ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
    INTRO_TAC "not_proves" THEN
    SUBGOAL_THEN `~(ITF:(form list->bool)#(form list->form list->bool)->bool
                   |= TRANSL (p:form))` MP_TAC THENL
    [ASM_MESON_TAC[CONTRAPOS_THM; GL_COMPLETENESS_THM]; ALL_TAC] THEN
    REWRITE_TAC[valid; holds_in; FORALL_PAIR_THM; NOT_FORALL_THM; NOT_IMP] THEN
    INTRO_TAC "@W R. ITF (@V w. IN not)" THEN
    EXISTS_TAC `W:form list->bool` THEN
    EXISTS_TAC `R_PLUS (W:form list ->bool) (R:form list->form list ->bool)` THEN
    CONJ_TAC THENL
    [ASM_MESON_TAC[ITF_IMP_R_PLUS_RATF];
     EXISTS_TAC `V:(char)list->(form)list->bool` THEN
      EXISTS_TAC `w:form list` THEN
      ASM_REWRITE_TAC[] THEN
      CLAIM_TAC "R_IN_ITF"
                `(W:form list->bool, R:form list->form list->bool) IN ITF` THENL
      [ASM_REWRITE_TAC[IN_ITF; IN_FINITE_FRAME]; ALL_TAC] THEN
      ASM_MESON_TAC[GRZ_TRANSL_LEMMA]]]);;

let GRZ_TRANSL = prove
  (`!p. [GRZ_AX . {} |~ p] <=> [GL_AX . {} |~ TRANSL (p)]`,
    MESON_TAC[GRZ_ADEQ_THM; RATF_TRANSL]);;

(* ------------------------------------------------------------------------- *)
(* Decision procedure for the Grzegorczyk Logic (Grz) via translation to     *)
(* Gödel-Löb provability Logic (GL).                                         *)
(* ------------------------------------------------------------------------- *)

let GRZ_TAC : tactic =
  let vsubst_rplus = vsubst [`R_PLUS (W:num->bool) R`,`R:num->num->bool`] in
  let tac =
    GEN_REWRITE_TAC I [GRZ_TRANSL] THEN
    CONV_TAC (RAND_CONV TRANSL_CONV) THEN
    REWRITE_TAC[dotbox_DEF] THEN
    GL_TAC in
  (* Call tac and translate countermodel in case of failure *)
  fun gl ->
    try tac gl with Failure s ->
      the_HOLMS_countermodel := vsubst_rplus !the_HOLMS_countermodel;
      FAIL_TAC s gl;;

holms_register_tactic `GRZ_AX` GRZ_TAC;;

(* ------------------------------------------------------------------------- *)
(* Tests and examples.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Example: Box (Box (a --> Box a) --> a) --> a *)
let tm = `[GRZ_AX . {} |~ Box (Box (Atom a --> Box Atom a) --> Atom a)
                          --> Atom a]`;;
time HOLMS_RULE tm;;
g tm;;
time e HOLMS_TAC;;
top_thm();;

(* Example: Same as before, but with metavariables. *)
(* let tm = `[GRZ_AX . {} |~ Box (Box (a --> Box a) --> a) --> a]`;; *)
(* time HOLMS_RULE tm;; *)

(* Example: Box a --> a *)
let tm = `[GRZ_AX . {} |~ Box Atom "a" --> Atom "a"]`;;
time HOLMS_RULE tm;;

(* ------------------------------------------------------------------------- *)
(* Decision procedure.                                                       *)
(* ------------------------------------------------------------------------- *)

let GRZ_CONV : conv =
  GEN_REWRITE_CONV I [GRZ_TRANSL] THENC
  GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV)
                   [TRANSL; diam_DEF; dotbox_DEF] THENC
  GL_CONV THENC
  REWRITE_CONV[];;
