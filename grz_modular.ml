(* ========================================================================= *)
(* Grzegorczyk Logic (Grz).                                                  *)
(*                                                                           *)
(* Meta-theory (soundness and completeness).                                 *)
(* Translation to GL Logic.                                                  *)
(* Decision procedure via the translation.                                   *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2026.                                  *)
(* ========================================================================= *)

needs "HOLMS/k_decid.ml";;       (* Used in GRZ_EQ_S4GRZ and its lemmas     *)
needs "HOLMS/s4_decid.ml";;      (* Used in S4GRZ_TRUTH_LEMMA               *)
needs "HOLMS/gl_decid.ml";;      (* Used in GRZ_TAC                         *)
needs "HOLMS/translations.ml";;
needs "HOLMS/wwf.ml";;

(* ------------------------------------------------------------------------- *)
(* 1. Axiomatic presentations of Grzegorczyk.                                *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Definition of the axiomatic calculus Grz.                                 *)
(* ------------------------------------------------------------------------- *)

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

(* Nuova dimostrazione che non usa CONJ_TAC. *)
(* TODO: Aggiustare o cancellare. *)
let GRZ_PROVES_T = prove
 (`!H p. [GRZ_AX . H |~ T_SCHEMA p]`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MODPROVES_MONO2 THEN
  EXISTS_TAC `{}:form->bool` THEN
  SHOW_TAC `{} SUBSET H:form->bool` THENL [REWRITE_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
  SHOW_TAC `[GRZ_AX . {} |~ T_SCHEMA p]` THEN
  REWRITE_TAC[T_SCHEMA_DEF] THEN
  MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `Box (Box (p --> Box p) --> p)` THEN
  SHOW_TAC `[GRZ_AX . {} |~ Box (Box (p --> Box p) --> p) --> p]` THENL
  [ASM_MESON_TAC[MODPROVES_RULES; GRZ_IN_GRZ_AX]; ALL_TAC] THEN
  SHOW_TAC `[GRZ_AX . {} |~ Box p --> Box (Box (p --> Box p) --> p)]` THEN
  MATCH_MP_TAC MODPROVES_MONO1 THEN
  EXISTS_TAC `{}:form->bool` THEN
  SHOW_TAC `{} SUBSET GRZ_AX` THENL [ASM_MESON_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
  SHOW_TAC `[{} . {} |~ Box p --> Box (Box (p --> Box p) --> p)]` THEN HOLMS_TAC);;

(* Dimostrazione originaria. *)
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
(* Correspondence Theory: RTWN Frames are characteristic for S4GRZ.          *)
(* ------------------------------------------------------------------------- *)

let RTWN_CHAR_S4GRZ = prove
 (`RTWN:(W->bool)#(W->W->bool)->bool = CHAR S4GRZ_AX`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_CHAR; IN_RTWN] THEN
  REWRITE_TAC[S4GRZ_AX; FORALL_IN_UNION; FORALL_IN_GSPEC; IN_UNIV] THEN
  ASM_MESON_TAC[MODAL_REFL; MODAL_TRANS; MODAL_RTWN; IN_FRAME]);;

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

let IN_RATF_ALT = prove
 (`!f:(W->bool)#(W->W->bool).
       f IN RATF <=>
       f IN FINITE_FRAME /\
       UNCURRY REFLEXIVE f /\
       UNCURRY TRANSITIVE f /\
       UNCURRY ANTISYMMETRIC f`,
  REWRITE_TAC[FORALL_PAIR_THM; IN_RATF; UNCURRY_DEF]);;

(* ------------------------------------------------------------------------- *)
(* RATF Frames are RTWN Frames.                                              *)
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
(* Correspondence Theory: RATF Frames are appropriate for S4GRZ.             *)
(* ------------------------------------------------------------------------- *)

let RATF_APPR_S4GRZ = prove
 (`RATF: (W->bool)#(W->W->bool)->bool = APPR S4GRZ_AX`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN
  REWRITE_TAC[APPR_CAR; ITF_FIN_TRANSNT] THEN
  REWRITE_TAC[GSYM RTWN_CHAR_S4GRZ] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [ASM_MESON_TAC[RATF_SUBSET_RTWN; SUBSET; IN_RATF; IN_FINITE_FRAME];
   REWRITE_TAC[IN_RTWN; IN_RATF; IN_FINITE_FRAME; IN_FRAME] THEN
   INTRO_TAC "(frm refl trans wwf) fin" THEN
   ASM_REWRITE_TAC[IN_FRAME; ANTISYMMETRIC] THEN
   REFUTE_THEN MP_TAC THEN
   INTRO_TAC "RAA" THEN
   HYP_TAC "RAA: @x y. RATF" (REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
   HYP_TAC "wwf -> +" (REWRITE_RULE[WWF]) THEN
   ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM; DE_MORGAN_THM;
                   TAUT `~p \/ q <=> p ==> q`; fld; IN_ELIM_THM] THEN
   EXISTS_TAC `{w:W | w = x \/ w = y}` THEN
   ASM_REWRITE_TAC[IN_ELIM_THM] THEN
   ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. Soundness Lemmas.                                                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Soundness Lemma for S4GRZ.                                                *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_RTWN_VALID = prove
 (`!H p. [S4GRZ_AX . H |~ p] /\
         (!q. q IN H ==> RTWN:(W->bool)#(W->W->bool)->bool |= q)
         ==> RTWN:(W->bool)#(W->W->bool)->bool |= p`,
  MESON_TAC[GEN_CHAR_VALID; RTWN_CHAR_S4GRZ]);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. RATF.                                           *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_RATF_VALID = prove
 (`!p. [S4GRZ_AX . {} |~ p] ==> RATF:(W->bool)#(W->W->bool)->bool |= p`,
  ASM_MESON_TAC[GEN_APPR_VALID; RATF_APPR_S4GRZ]);;

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

let S4GRZ_FRAME_SCHEMA = new_definition
  `S4GRZ_FRAME_SCHEMA p = {q | q SUBSENTENCE p \/
                               ?C. Box C SUBFORMULA p /\
                                   (q = Box (C --> Box C) \/
                                    q = Not Box (C --> Box C))}`;;

let S4GRZ_STANDARD_WORLDS = new_definition
  `S4GRZ_STANDARD_WORLDS p =
   PARAMETRIC_STD_WORLD S4GRZ_AX S4GRZ_FRAME_SCHEMA p`;;

let S4GRZ_STANDARD_WORLDS_DEF = prove
 (`S4GRZ_STANDARD_WORLDS p =
   {w | MAXIMAL_CONSISTENT S4GRZ_AX p w /\
        (!q. MEM q w  ==> (q SUBSENTENCE p \/
                           ?C. Box C SUBFORMULA p /\
                               (q = Box (C --> Box C) \/
                                q = Not Box (C --> Box C))))}`,
  REWRITE_TAC[S4GRZ_STANDARD_WORLDS; PARAMETRIC_STD_WORLD;
              S4GRZ_FRAME_SCHEMA; IN_ELIM_THM]);;

(* TODO: Questo dovrebbe chiamarsi invece S4GRZ_STANDARD_FRAMES (S finale) *)
(* TODO: Dopo la rinomina di questo, rinominare anche S4GRZ_STD_FRAME. *)
let S4GRZ_STANDARD_FRAME = new_definition
  `S4GRZ_STANDARD_FRAME p =
   PARAMETRIC_STANDARD_FRAME S4GRZ_AX S4GRZ_FRAME_SCHEMA p`;;

(* TODO: Usare questo teorema per rimpiazzare il teorema subito sotto
   S4GRZ_STANDARD_FRAME_DEF.  *)
let S4GRZ_STANDARD_FRAME_ALT = prove
 (`!p. S4GRZ_STANDARD_FRAME p =
       APPR S4GRZ_AX INTER
       {W,R | W = S4GRZ_STANDARD_WORLDS p /\
              (!q w. Box q SUBFORMULA p /\ w IN W
                     ==> (MEM (Box q) w <=> (!x. R w x ==> MEM q x)))}`,
  REWRITE_TAC[S4GRZ_STANDARD_FRAME; S4GRZ_STANDARD_WORLDS;
              PARAMETRIC_STANDARD_FRAME_DEF]);;

(* TODO: Usare S4GRZ_STANDARD_WORLDS, vedi S4GRZ_STANDARD_FRAME_ALT sopra.  *)
let S4GRZ_STANDARD_FRAME_DEF = prove
 (`S4GRZ_STANDARD_FRAME p =
   APPR S4GRZ_AX INTER
   {W,R | W = {w | MAXIMAL_CONSISTENT S4GRZ_AX p w /\
                   (!q. MEM q w
                        ==> q SUBSENTENCE p \/
                            (?C. Box C SUBFORMULA p /\
                                 (q = Box (C --> Box C) \/
                                  q = Not Box (C --> Box C))))} /\
          (!q w. Box q SUBFORMULA p /\ w IN W
                 ==> (MEM (Box q) w <=> (!x. R w x ==> MEM q x)))}`,
  REWRITE_TAC[S4GRZ_STANDARD_FRAME; S4GRZ_FRAME_SCHEMA;
    PARAMETRIC_STANDARD_FRAME_DEF; PARAMETRIC_STD_WORLD; IN_ELIM_THM]);;

(* TODO: Valutazione standard. *)
let S4GRZ_STANDARD_MODEL_DEF = new_definition
 `S4GRZ_STANDARD_MODEL p (W,R) V <=>
  (W,R) IN S4GRZ_STANDARD_FRAME p /\
  (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`;;

let Q_REL_DEF = new_definition
  `Q_REL p w x <=>
   w IN S4GRZ_STANDARD_WORLDS p  /\
   x IN S4GRZ_STANDARD_WORLDS p  /\
   (!B. B SUBSENTENCE p \/
        (?C. Box C SUBFORMULA p /\ (Box B = Box(C --> Box C)))
        ==> (MEM (Box B) w ==> MEM (Box B) x))`;;

let TRANSITIVE_Q_REL = prove
 (`!p. TRANSITIVE (S4GRZ_STANDARD_WORLDS p) (Q_REL p)`,
  REWRITE_TAC[TRANSITIVE; Q_REL_DEF] THEN MESON_TAC[]);;

let S4GRZ_STANDARD_REL_DEF = new_definition
  `S4GRZ_STANDARD_REL p w x <=>
    w IN S4GRZ_STANDARD_WORLDS p  /\
    x IN S4GRZ_STANDARD_WORLDS p  /\
    Q_REL p w x /\ (Q_REL p x w ==> w = x)`;;

(* TODO; Questo dovrebbe invece chiamarsi S4GRZ_STANDARD_FRAME, ma per il momento c'è un conflitto di nomi. *)
let S4GRZ_STD_FRAME = new_definition
  `S4GRZ_STD_FRAME p = (S4GRZ_STANDARD_WORLDS p, S4GRZ_STANDARD_REL p)`;;

(* ------------------------------------------------------------------------- *)
(* The standard relation for S4GRZ is Reflexive, Antisymmetric               *)
(* and Transitive.                                                           *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_STANDARD_REL_REFL = prove
 (`!p w. S4GRZ_STANDARD_REL p w w <=> w IN S4GRZ_STANDARD_WORLDS p`,
  REWRITE_TAC[S4GRZ_STANDARD_REL_DEF; Q_REL_DEF]);;

let REFLEXIVE_S4GRZ_STANDARD_REL = prove
 (`!p. REFLEXIVE (S4GRZ_STANDARD_WORLDS p) (S4GRZ_STANDARD_REL p)`,
  REWRITE_TAC[REFLEXIVE; S4GRZ_STANDARD_REL_REFL]);;

let S4GRZ_STANDARD_REL_PROP = prove
 (`!p. REFLEXIVE (S4GRZ_STANDARD_WORLDS p) (S4GRZ_STANDARD_REL p) /\
       ANTISYMMETRIC (S4GRZ_STANDARD_WORLDS p) (S4GRZ_STANDARD_REL p) /\
       TRANSITIVE (S4GRZ_STANDARD_WORLDS p) (S4GRZ_STANDARD_REL p)`,
  FIX_TAC "p" THEN
  THEN1
    (SHOW_TAC `REFLEXIVE (S4GRZ_STANDARD_WORLDS p) (S4GRZ_STANDARD_REL p)`)
    (REWRITE_TAC[REFLEXIVE_S4GRZ_STANDARD_REL]) THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[ANTISYMMETRIC; S4GRZ_STANDARD_REL_DEF] THEN
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

(* ------------------------------------------------------------------------- *)
(* Maximal Consistent Lemmas.                                                *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_EXTEND_MAXIMAL_SETCONSISTENT = prove
 (`!S p X. SETCONSISTENT S X /\
           FINITE X /\
           (!q. q IN X ==> q SUBSENTENCE p \/
                           (?C. Box C SUBFORMULA p /\
                                (q = Box (C --> Box C) \/
                                 q = Not Box (C --> Box C))))
           ==> ?M. MAXIMAL_SETCONSISTENT S p M /\
                   FINITE M /\
                   (!q. q IN M ==> q SUBSENTENCE p  \/
                                   (?C. Box C SUBFORMULA p /\
                                        (q = Box (C --> Box C) \/
                                         q = Not Box (C --> Box C)))) /\
                   X SUBSET M`,
  GEN_TAC THEN GEN_TAC THEN SUBGOAL_THEN
    `!L. FINITE L
         ==> !X. SETCONSISTENT S X /\ FINITE X /\
                 (!q. q IN X ==> q SUBSENTENCE p \/
                                 (?C. Box C SUBFORMULA p /\
                                      (q = Box (C --> Box C) \/
                                       q = Not Box (C --> Box C)))) /\
                 (!q. q IN L ==> q SUBFORMULA p) /\
                 (!q. q SUBFORMULA p ==> q IN L \/ q IN X \/ Not q IN X)
                 ==> ?M. MAXIMAL_SETCONSISTENT S p M /\
                         FINITE M /\
                         (!q. q IN M ==> q SUBSENTENCE p \/
                                         (?C. Box C SUBFORMULA p /\
                                              (q = Box (C --> Box C) \/
                                               q = Not Box (C --> Box C)))) /\
                         X SUBSET M`
    (LABEL_TAC "P") THENL
  [ALL_TAC;
   INTRO_TAC "!X; cons fin subf" THEN
   HYP_TAC "P: +" (SPEC `{f | f SUBFORMULA p}`) THEN
   ANTS_TAC THENL [REWRITE_TAC[FINITE_SUBFORMULA]; ALL_TAC] THEN
   DISCH_THEN (MP_TAC o SPEC `X:form->bool`) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[SETCONSISTENT_SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL [HYP REWRITE_TAC "fin" []; ALL_TAC] THEN
    CONJ_TAC THENL [HYP REWRITE_TAC "subf" []; ALL_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
   INTRO_TAC "@M. max fin sub" THEN EXISTS_TAC `M:form->bool` THEN
   ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN
  CONJ_TAC THENL
  [REWRITE_TAC[NOT_IN_EMPTY] THEN
   INTRO_TAC "!X; X fin max subf" THEN
   EXISTS_TAC `X:form->bool` THEN
   ASM_REWRITE_TAC[SUBSET_REFL; MAXIMAL_SETCONSISTENT];
   ALL_TAC] THEN
  INTRO_TAC "![q] [Y]; hpind" THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  REWRITE_TAC[IN_INSERT] THEN
  INTRO_TAC "!X; cons fin qin (qsub Ysub) max" THEN
  LABEL_ASM_CASES_TAC "hmemX" `q:form IN X` THENL
  [REMOVE_THEN "hpind" (MP_TAC o SPEC `X:form->bool`) THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_MESON_TAC[]; ALL_TAC] THEN
  LABEL_ASM_CASES_TAC "nhmemX" `Not q IN X` THENL
  [REMOVE_THEN "hpind" (MP_TAC o SPEC `X:form->bool`) THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  LABEL_ASM_CASES_TAC "consh" `SETCONSISTENT S (q:form INSERT X)` THENL
  [REMOVE_THEN "hpind" (MP_TAC o SPEC `(q:form) INSERT X`) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT] THEN
    REWRITE_TAC[IN_INSERT] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_MESON_TAC[SUBSET; SUBFORMULA_IMP_SUBSENTENCE];
    ALL_TAC] THEN
   INTRO_TAC "@M. max fin sub" THEN EXISTS_TAC `M:form->bool` THEN
   ASM_REWRITE_TAC[] THEN
   REMOVE_THEN "sub" MP_TAC THEN
   SET_TAC[];
   ALL_TAC] THEN
  REMOVE_THEN "hpind" (MP_TAC o SPEC `Not q INSERT X`) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[FINITE_INSERT] THEN
   CONJ_TAC THENL [
    ASM_MESON_TAC[SETCONSISTENT_EXTEND_CASES];
    ALL_TAC] THEN
   REWRITE_TAC[FORALL_IN_INSERT] THEN
   REWRITE_TAC[IN_INSERT] THEN
   ASM_MESON_TAC[SUBSET; SUBSENTENCE_RULES];
   ALL_TAC] THEN
  REWRITE_TAC[INSERT_SUBSET] THEN
  INTRO_TAC "@M. max sub" THEN EXISTS_TAC `M:form->bool` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* TODO: Rimuovere questo e il successivo?                                   *)
(* Versione che usa le liste anziché gli insiemi finiti.                     *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_EXTEND_MAXIMAL_CONSISTENT = prove
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

let GRZ_NONEMPTY_MAXIMAL_CONSISTENT = prove
 (`!S p. ~ [S . {} |~ p]
         ==> ?M. MAXIMAL_CONSISTENT S p M /\
                 MEM (Not p) M /\
                 (!q. MEM q M ==> q SUBSENTENCE p \/
                                   (?C. Box C SUBFORMULA p /\
                                       (q = Box (C --> Box C) \/
                                        q = Not Box (C --> Box C))))`,
  INTRO_TAC "!S p; p" THEN
  MP_TAC (SPECL [`S:form->bool`; `p:form`; `[Not p]`]
    S4GRZ_EXTEND_MAXIMAL_CONSISTENT) THEN
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
(* S4GRZ_STD_FRAME_IN_RATF                                                   *)
(* ------------------------------------------------------------------------- *)

let S4GRZ_STANDARD_WORLDS_NONEMPTY = prove
 (`!p. ~[S4GRZ_AX . {} |~ p] ==> ~(S4GRZ_STANDARD_WORLDS p = {})`,
  INTRO_TAC "!p; p" THEN
  HYP_TAC "p: @M. max mem hp" (MATCH_MP GRZ_NONEMPTY_MAXIMAL_CONSISTENT) THEN
  REWRITE_TAC[S4GRZ_STANDARD_WORLDS; PARAMETRIC_STD_WORLD] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `M:form list` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  INTRO_TAC "!q; q" THEN REMOVE_THEN "q" (ANTE_RES_THEN MP_TAC) THEN
  REWRITE_TAC[S4GRZ_FRAME_SCHEMA; IN_ELIM_THM]);;

let IN_APPR_S4GRZ = prove
 (`!W:W->bool R.
     W,R IN APPR S4GRZ_AX <=>
     ~(W = {}) /\
     FINITE W /\
     (!x y. R x y ==> x IN W /\ y IN W) /\
     (!x. x IN W ==> R x x) /\
     (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z) /\
     (!x y. x IN W /\ y IN W /\ R x y /\ R y x ==> x = y)`,
  REWRITE_TAC[GSYM RATF_APPR_S4GRZ; IN_RATF; IN_FINITE_FRAME;
              REFLEXIVE; TRANSITIVE; ANTISYMMETRIC] THEN
  MESON_TAC[]);;

let FINITE_S4GRZ_FRAME_SCHEMA = prove
 (`!p. FINITE (S4GRZ_FRAME_SCHEMA p)`,
  GEN_TAC THEN REWRITE_TAC[S4GRZ_FRAME_SCHEMA] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  ABBREV_TAC `s = {q | q SUBSENTENCE p}` THEN
  ABBREV_TAC
    `t = IMAGE (\C. Box (C --> Box C)) {C | Box C SUBFORMULA p}` THEN
  ABBREV_TAC `u = IMAGE (Not) t` THEN
  CLAIM_TAC "fin_s" `FINITE (s:form->bool)` THENL
    [EXPAND_TAC "s" THEN REWRITE_TAC[FINITE_SUBSENTENCE];
     ALL_TAC] THEN
  CLAIM_TAC "fin_t" `FINITE (t:form->bool)` THENL
    [EXPAND_TAC "t" THEN MATCH_MP_TAC FINITE_IMAGE THEN
     MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{q | q SUBFORMULA p}` THEN
     REWRITE_TAC[FINITE_SUBFORMULA] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
     INTRO_TAC "![q]; q" THEN GEN_REWRITE_TAC I [SUBFORMULA_CASES_R] THEN
     DISJ2_TAC THEN EXISTS_TAC `Box q` THEN
     HYP REWRITE_TAC "q" [MINOR_CLAUSES; IN_INSERT];
     ALL_TAC] THEN
  CLAIM_TAC "fin_u" `FINITE (u:form->bool)` THENL
    [EXPAND_TAC "u" THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
  EXISTS_TAC `s UNION t UNION u:form->bool` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[FINITE_UNION]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
  INTRO_TAC "![q]; q | @C. C q" THENL
   [DISJ1_TAC THEN EXPAND_TAC "s" THEN HYP SET_TAC "q" [];
    DISJ2_TAC] THEN
  REMOVE_THEN "q" (DESTRUCT_TAC "q | q") THEN REMOVE_THEN "q" SUBST_VAR_TAC THENL
    [DISJ1_TAC THEN EXPAND_TAC "t" THEN
     REWRITE_TAC[IN_IMAGE; injectivity "form"] THEN
     HYP SET_TAC "C" [];
     DISJ2_TAC THEN EXPAND_TAC "u" THEN
     REWRITE_TAC[IN_IMAGE; injectivity "form"] THEN CONV_TAC UNWIND_CONV THEN
     EXPAND_TAC "t" THEN REWRITE_TAC[IN_IMAGE; injectivity "form"] THEN
     HYP SET_TAC "C" []]);;

let FINITE_S4GRZ_STANDARD_WORLDS = prove
 (`!p. FINITE (S4GRZ_STANDARD_WORLDS p)`,
  GEN_TAC THEN REWRITE_TAC[S4GRZ_STANDARD_WORLDS; PARAMETRIC_STD_WORLD] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{w | NOREPETITION w /\ (!q. MEM q w ==>q IN S4GRZ_FRAME_SCHEMA p)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC FINITE_NOREPETITION THEN
   REWRITE_TAC[FINITE_S4GRZ_FRAME_SCHEMA];
   REWRITE_TAC[MAXIMAL_CONSISTENT] THEN SET_TAC[]]);;

let S4GRZ_STD_FRAME_IN_FINITE_FRAME = prove
 (`!p. ~[S4GRZ_AX . {} |~ p] ==> S4GRZ_STD_FRAME p IN FINITE_FRAME`,
  INTRO_TAC "!p; p" THEN REWRITE_TAC[S4GRZ_STD_FRAME; IN_FINITE_FRAME] THEN
  REWRITE_TAC[FINITE_S4GRZ_STANDARD_WORLDS] THEN
  ASM_SIMP_TAC[S4GRZ_STANDARD_WORLDS_NONEMPTY] THEN
  REWRITE_TAC[S4GRZ_STANDARD_REL_DEF] THEN
  MESON_TAC[]);;

let S4GRZ_STD_FRAME_IN_RATF = prove
 (`!p. ~[S4GRZ_AX . {} |~ p] ==> S4GRZ_STD_FRAME p IN RATF`,
  INTRO_TAC "!p; p" THEN REWRITE_TAC[IN_RATF_ALT] THEN
  ASM_SIMP_TAC[S4GRZ_STD_FRAME_IN_FINITE_FRAME] THEN
  REWRITE_TAC[S4GRZ_STD_FRAME; UNCURRY_DEF; S4GRZ_STANDARD_REL_PROP]);;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

(* TODO: Aggiustare con la nuova definizione di S4GRZ_STANDARD_FRAME *)
let S4GRZ_TRUTH_LEMMA = prove
 (`!W R p V q.
     ~[S4GRZ_AX . {} |~ p] /\
     q SUBFORMULA p /\
     S4GRZ_STANDARD_MODEL p (W,R) V
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[S4GRZ_STANDARD_MODEL_DEF; S4GRZ_STANDARD_FRAME_ALT] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_PAIR_THM; GSYM RATF_APPR_S4GRZ] THEN
  INTRO_TAC "np q (ratf W wd) val" THEN
  GEN_FORM_INDUCT_TAC `q:form` THEN INTRO_TAC "sub" THEN
  USE_THEN "sub" (fun sub -> MAP_EVERY ASSUME_TAC
    (mapfilter (C MATCH_MP sub) (CONJUNCTS MINOR_SUBFORMULA))) THEN
  INTRO_TAC "!w; w" THEN USE_THEN "w" MP_TAC THEN
  HYP (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)) "W" [] THEN
  REWRITE_TAC[S4GRZ_STANDARD_WORLDS_DEF; IN_ELIM_THM] THEN
  INTRO_TAC "max_cons wsub" THEN
  HYP_TAC "max_cons: maxcons _"
    (REWRITE_RULE [MAXIMAL_CONSISTENT_IFF_MAXIMAL_SETCONSISTENT]) THEN
  HYP_TAC "maxcons -> cons" (MATCH_MP MAXIMAL_SETCONSISTENT_IMP_SETCONSISTENT) THEN
  REWRITE_TAC[holds] THEN
  TRY (USE_THEN "q_hpind" (REPEAT_GTCL IMP_RES_THEN (SUBST1_TAC o GSYM))) THEN
  TRY (REMOVE_THEN "q1_hpind" (REPEAT_GTCL IMP_RES_THEN (SUBST1_TAC o GSYM))) THEN
  TRY (REMOVE_THEN "q2_hpind"
    (REPEAT_GTCL IMP_RES_THEN (SUBST1_TAC o GSYM))) THENL
  [
   (* q = False *)
   HYP_TAC "cons: +" (REWRITE_RULE[SETCONSISTENT]) THEN
   MESON_TAC[MODPROVES_HP; IN_SET_OF_LIST]
  ;
   (* q = True *)
   REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN
   HYP_SUFFICE_TAC `[S4GRZ_AX . set_of_list w |~ True]` "maxcons sub"
    [MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE] THEN
   MATCH_ACCEPT_TAC MLK_truth_th
  ;
   (* q = Atom s *)
   HYP SIMP_TAC "val sub w" []
  ;
   (* q = Not q *)
   REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN
   MATCH_MP_TAC MAXIMAL_SETCONSISTENT_NOT_CLOSED THEN
   HYP MESON_TAC "maxcons sub" []
  ;
   (* q = q1 && q2 *)
   HYP MESON_TAC "cons maxcons sub"
     [MAXIMAL_SETCONSISTENT_AND_MIONOR_CLOSED; IN_SET_OF_LIST]
  ;
   (* q = q1 || q2 *)
   HYP MESON_TAC "cons maxcons sub"
     [MAXIMAL_SETCONSISTENT_MINOR_OR_CLOSED; IN_SET_OF_LIST]
  ;
   (* q = q1 --> q2 *)
   HYP MESON_TAC "cons maxcons sub"
    [MAXIMAL_SETCONSISTENT_IMP_CLOSED; IN_SET_OF_LIST]
  ;
   (* q = q1 <-> q2 *)
   HYP MESON_TAC "cons maxcons sub"
     [MAXIMAL_SETCONSISTENT_IFF_CLOSED; IN_SET_OF_LIST]
   (* q = Box *)
  ;
   C SUBGOAL_THEN SUBST1_TAC `MEM (Box q) w <=> (!x. R w x ==> MEM q x)` THENL
   [REMOVE_THEN "wd" MATCH_MP_TAC THEN BY (HYP REWRITE_TAC "sub w" []);
    ALL_TAC] THEN
   MATCH_MP_TAC
     (MESON[] `!P Q. (!w. P w <=> Q w) ==> ((!w. P w) <=> (!w. Q w))`) THEN
   INTRO_TAC "!x" THEN
   LABEL_ASM_CASES_TAC "wx" `R (w:form list) (x:form list):bool` THEN
   HYP REWRITE_TAC "wx" [] THEN
   CLAIM_TAC "x" `x:form list IN W` THENL
   [HYP_TAC "ratf: +" (REWRITE_RULE[IN_RATF]) THEN INTRO_TAC "+ _" THEN
    REWRITE_TAC[IN_FINITE_FRAME] THEN HYP MESON_TAC "wx" [];
    HYP REWRITE_TAC "x" []] THEN
   REMOVE_THEN "q_hpind" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP; GSYM RIGHT_FORALL_IMP_THM]) THEN
   FIND_ASSUM (fun th -> REWRITE_TAC[th]) `q SUBFORMULA p` THEN
   HYP_TAC "ratf: +" (REWRITE_RULE[IN_RATF]) THEN
   HYP REWRITE_TAC "x" [] THEN HYP MESON_TAC "wx" []
  ]);;

(* ------------------------------------------------------------------------- *)
(* Proof of Completeness w.r.t. RATF.                                        *)
(* ------------------------------------------------------------------------- *)

let MAXIMAL_SETCONSISTENT_LEMMA = prove
 (`!S p X A b. MAXIMAL_SETCONSISTENT S p X /\
               A SUBSET X /\
               b SUBFORMULA p /\
               [S . A |~ b]
               ==> b IN X`,
  REPEAT GEN_TAC THEN INTRO_TAC "X A b hp" THEN
  HYP_SUFFICE_TAC `[S . X |~ b]` "X b"
    [MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE] THEN
  HYP MESON_TAC "A hp" [MODPROVES_MONO2]);;

let dest_box_fun = new_recursive_definition form_RECURSION
  `dest_box_fun (Box C) = C`;;

let S4GRZ_ACCESSIBILITY_SETCONSISTENT = prove
 (`!p w q. ~[S4GRZ_AX . {} |~ p] /\
           Box q SUBFORMULA p /\
           MAXIMAL_SETCONSISTENT S4GRZ_AX p w /\
           FINITE w /\
           (!q. q IN w
                ==> q SUBSENTENCE p \/
                    (?C. Box C SUBFORMULA p /\
                         (q = Box (C --> Box C) \/ q = Not Box (C --> Box C)))) /\
           ~(Box q IN w)
           ==> SETCONSISTENT S4GRZ_AX
                 (Not q INSERT Box (q --> Box q) INSERT {Box C | Box C IN w})`,
  INTRO_TAC "!p w q; p box_q maxcons finw hp boxq_in_w" THEN
  REFUTE_THEN (LABEL_TAC "contra") THEN
  REMOVE_THEN "boxq_in_w" MP_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC MAXIMAL_SETCONSISTENT_LEMMA THEN
  MAP_EVERY EXISTS_TAC [`S4GRZ_AX`; `p:form`; `{Box C | Box C IN w}`] THEN
  HYP REWRITE_TAC "maxcons box_q" [] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  HYP_TAC "contra" (REWRITE_RULE[SETCONSISTENT]) THEN
  CLAIM_TAC "finboxw" `FINITE {Box C | Box C IN w}` THENL
  [HYP_SUFFICE_TAC `{Box C | Box C IN w} SUBSET w` "finw" [FINITE_SUBSET] THEN
   SET_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "1" `[S4GRZ_AX . {} |~ CONJLIST (list_of_set {Box C | Box C IN w}) --> (Box (q --> Box q) --> q)]` THENL
  [HYP SIMP_TAC "finboxw" [MODPROVES_DEDUCTION_LEMMA_CONJLIST_EMPTY_ALT] THEN
   REWRITE_TAC[MODPROVES_DEDUCTION_LEMMA] THEN
   ONCE_REWRITE_TAC[GSYM MLK_DOUBLENEG_IFF] THEN
   ONCE_REWRITE_TAC[MLK_not_def] THEN
   REWRITE_TAC[MODPROVES_DEDUCTION_LEMMA] THEN
   REMOVE_THEN "contra" MATCH_ACCEPT_TAC;
   ALL_TAC] THEN
  CLAIM_TAC "2" `[S4GRZ_AX . {} |~ Box (CONJLIST (list_of_set {Box C | Box C IN w}) --> (Box (q --> Box q) --> q))]` THENL
  [MATCH_MP_TAC MLK_necessitation THEN USE_THEN "1" MATCH_ACCEPT_TAC; ALL_TAC] THEN
  CLAIM_TAC "3" `[S4GRZ_AX . {} |~ Box (CONJLIST (list_of_set {Box C | Box C IN w})) --> Box (Box (q --> Box q) --> q)]` THENL
  [MATCH_MP_TAC MLK_boximp THEN
   USE_THEN "2" MATCH_ACCEPT_TAC;
   ALL_TAC] THEN
  CLAIM_TAC "4" `[S4GRZ_AX . {} |~ Box (CONJLIST (list_of_set {Box C | Box C IN w})) --> q]` THENL
  [MATCH_MP_TAC MLK_imp_trans THEN HYP MESON_TAC "3" [S4GRZ_AX_GRZ]; ALL_TAC] THEN
  CLAIM_TAC "5" `[S4GRZ_AX . {} |~ Box (Box (CONJLIST (list_of_set {Box C | Box C IN w})) --> q)]` THENL
  [MATCH_MP_TAC MLK_necessitation THEN
   USE_THEN "4" ACCEPT_TAC;
   ALL_TAC] THEN
  CLAIM_TAC "6" `[S4GRZ_AX . {} |~ Box Box CONJLIST (list_of_set {Box C | Box C IN w}) --> Box q]` THENL
  [MATCH_MP_TAC MLK_boximp THEN
   USE_THEN "5" ACCEPT_TAC;
   ALL_TAC] THEN
  CLAIM_TAC "7" `[S4GRZ_AX . {} |~ CONJLIST (list_of_set {Box C | Box C IN w}) --> Box q]` THENL
  [MATCH_MP_TAC MLK_imp_trans THEN
    EXISTS_TAC `Box Box CONJLIST (list_of_set {Box C | Box C IN w})` THEN
    HYP REWRITE_TAC "6" [] THEN
    MATCH_MP_TAC MLK_imp_trans THEN
    EXISTS_TAC `Box CONJLIST (list_of_set {Box C | Box C IN w})` THEN
    CONJ_TAC THENL
    [ALL_TAC; MESON_TAC[GRZ_EQ_S4GRZ; GRZ_PROVES_4; FOUR_SCHEMA_DEF]] THEN
    MATCH_MP_TAC MLK_imp_mp_subst THEN
    EXISTS_TAC `Box CONJLIST (list_of_set {C | Box C IN w})` THEN
    EXISTS_TAC `Box Box CONJLIST (list_of_set {C | Box C IN w})` THEN
    SHOW_TAC `[S4GRZ_AX . {} |~ Box CONJLIST (list_of_set {C | Box C IN w}) -->
               Box Box CONJLIST (list_of_set {C | Box C IN w})]` THENL
    [MESON_TAC[GRZ_EQ_S4GRZ; GRZ_PROVES_4; FOUR_SCHEMA_DEF]; ALL_TAC] THEN
    SUFFICE_TAC `[S4GRZ_AX . {} |~ Box CONJLIST (list_of_set {C | Box C IN w}) 
                  <-> CONJLIST (list_of_set {Box C | Box C IN w})]` [MLK_box_subst] THEN
    MATCH_MP_TAC MLK_iff_trans THEN
    EXISTS_TAC `CONJLIST (MAP (Box) (list_of_set {C | Box C IN w}))` THEN
    CONJ_TAC THENL
    [MESON_TAC [CONJLIST_MAP_BOX; MLK_iff_sym]; ALL_TAC] THEN
    MATCH_MP_TAC SET_OF_LIST_EQ_CONJLIST_EQ THEN
    ASM_REWRITE_TAC[ SET_OF_LIST_MAP] THEN
    SUFFICE_TAC `FINITE {Box C | Box C IN w} /\ FINITE {C | Box C IN w} /\ 
                 IMAGE (Box) {C | Box C IN w} = {Box C | Box C IN w}`
               [SET_OF_LIST_OF_SET] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]]  THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{y | ?x. x IN w /\ y = dest_box_fun x}` THEN
    CONJ_TAC THENL 
    [MATCH_MP_TAC FINITE_IMAGE_EXPAND THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      GEN_TAC THEN DISCH_TAC THEN
      EXISTS_TAC `Box x` THEN ASM_REWRITE_TAC[dest_box_fun]]; ALL_TAC] THEN
  HYP_SUFFICE_TAC `FINITE {Box C | Box C IN w}` "7"
    [MODPROVES_DEDUCTION_LEMMA_CONJLIST_EMPTY; SET_OF_LIST_OF_SET] THEN
  HYP REWRITE_TAC "finboxw" []);; 

let S4GRZ_ACCESSIBILITY_LEMMA = prove
 (`!p w q. ~[S4GRZ_AX . {} |~ p] /\
           w IN S4GRZ_STANDARD_WORLDS p /\
           Box q SUBFORMULA p /\
           (!x. S4GRZ_STANDARD_REL p w x ==> MEM q x)
           ==> MEM (Box q) w`,
  INTRO_TAC "!p w q; p w q hp" THEN
  HYP_TAC "w : max_cons w" (REWRITE_RULE[S4GRZ_STANDARD_WORLDS_DEF; IN_ELIM_THM]) THEN
  REFUTE_THEN (LABEL_TAC "box_w") THEN
  REMOVE_THEN "hp" MP_TAC THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  ABBREV_TAC `X = Not q INSERT Box (q --> Box q) INSERT {Box C | Box C IN set_of_list w}` THEN
  THEN1
   (DESTRUCT_TAC "nqw | qw" (MESON[] `~MEM (q:form) w \/ MEM q w`))
   (HYP_SUFFICE_TAC `w IN S4GRZ_STANDARD_WORLDS p` "nqw max_cons" [S4GRZ_STANDARD_REL_REFL] THEN
    HYP REWRITE_TAC "max_cons w" [S4GRZ_STANDARD_WORLDS_DEF; IN_ELIM_THM]) THEN
  THEN1
   (CLAIM_TAC "@M. Mmax Mfin M Msuper"
    `?M. MAXIMAL_SETCONSISTENT S4GRZ_AX p M /\
         FINITE M /\
         (!q. q IN M
              ==> q SUBSENTENCE p \/
                  (?C. Box C SUBFORMULA p /\
                       (q = Box (C --> Box C) \/
                        q = Not Box (C --> Box C)))) /\
                  X SUBSET M`)
   (
    MATCH_MP_TAC S4GRZ_EXTEND_MAXIMAL_SETCONSISTENT THEN
    THEN1
      (SHOW_TAC `SETCONSISTENT S4GRZ_AX X`)
      (EXPAND_TAC "X" THEN
       MATCH_MP_TAC S4GRZ_ACCESSIBILITY_SETCONSISTENT THEN
       EXISTS_TAC `p:form` THEN
       HYP_TAC "max_cons: max norep" (REWRITE_RULE[MAXIMAL_CONSISTENT_IFF_MAXIMAL_SETCONSISTENT]) THEN
       ASM_REWRITE_TAC[IN_SET_OF_LIST; FINITE_SET_OF_LIST]) THEN
    THEN1 (SHOW_TAC `FINITE (X:form->bool)`)
     (EXPAND_TAC "X" THEN REWRITE_TAC[FINITE_INSERT] THEN
      SUFFICE_TAC `{Box C | Box C IN set_of_list w} SUBSET set_of_list w`
        [FINITE_SUBSET; FINITE_SET_OF_LIST] THEN
      SET_TAC[]) THEN
    SHOW_TAC
        `!q. q IN X
             ==> q SUBSENTENCE p \/
                 (?C. Box C SUBFORMULA p /\
                      (q = Box (C --> Box C) \/
                       q = Not Box (C --> Box C)))` THEN
    EXPAND_TAC "X" THEN
    REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_GSPEC; IN_SET_OF_LIST] THEN
    THEN1
      (SHOW_TAC `Not q SUBSENTENCE p`)
      (SUFFICE_TAC `q SUBFORMULA p` [SUBSENTENCE_RULES] THEN
       HYP MESON_TAC "q" [MINOR_SUBFORMULA]) THEN
    THEN1
      (SHOW_TAC
        `?C. Box C SUBFORMULA p /\
             (Box (q --> Box q) = Box (C --> Box C) \/
             Box (q --> Box q) = Not Box (C --> Box C))`)
      (SUFFICE_TAC `Box q SUBFORMULA p` [] THEN
       HYP MESON_TAC "q" []) THEN
    SHOW_TAC
     `!C.
      MEM (Box C) w
      ==> Box C SUBSENTENCE p \/
          (?C'.
               Box C' SUBFORMULA p /\
               (Box C = Box (C' --> Box C') \/
                Box C = Not Box (C' --> Box C')))` THEN
    HYP MESON_TAC "w" []
   ) THEN
  SUFFICE_TAC `S4GRZ_STANDARD_REL p w (list_of_set M) /\ ~MEM q (list_of_set M)` [] THEN
  SHOW_TAC `~MEM (q:form) (list_of_set M)` THENL
  [HYP_SUFFICE_TAC `~(q:form IN M)` "Mfin" [MEM_LIST_OF_SET] THEN
   HYP_SUFFICE_TAC `Not q IN M` "Mmax" [IN_SETCONSISTENT_NC; MAXIMAL_SETCONSISTENT_IMP_SETCONSISTENT] THEN
   HYP_SUFFICE_TAC `Not q IN X` "Msuper" [SUBSET] THEN
   EXPAND_TAC "X" THEN REWRITE_TAC[IN_INSERT];
   ALL_TAC] THEN
  SHOW_TAC `S4GRZ_STANDARD_REL p w (list_of_set M)` THEN
  REWRITE_TAC[S4GRZ_STANDARD_REL_DEF] THEN
  CLAIM_TAC "w_std" `w IN S4GRZ_STANDARD_WORLDS p` THENL
  [REWRITE_TAC[S4GRZ_STANDARD_WORLDS_DEF; IN_ELIM_THM] THEN
   FROM_TAC ["max_cons"; "w"] THEN BY ASM_CLEAR_TAC;
   USE_THEN "w_std" CLEAR_TAC] THEN
  CLAIM_TAC "M_std" `list_of_set M IN S4GRZ_STANDARD_WORLDS p` THENL
  [REWRITE_TAC[S4GRZ_STANDARD_WORLDS_DEF; IN_ELIM_THM] THEN
   REWRITE_TAC[MAXIMAL_CONSISTENT_IFF_MAXIMAL_SETCONSISTENT] THEN
   HYP SIMP_TAC "Mfin" [SET_OF_LIST_OF_SET; NOREPETITION_LIST_OF_SET; MEM_LIST_OF_SET] THEN
   FROM_TAC ["Mmax"; "M"] THEN BY ASM_CLEAR_TAC;
   USE_THEN "M_std" CLEAR_TAC] THEN
  SHOW_TAC `Q_REL p w (list_of_set M)` THENL
  [HYP REWRITE_TAC "w_std M_std" [Q_REL_DEF] THEN
   GEN_TAC THEN REWRITE_TAC[form_INJ] THEN
   LABEL_CASES_TAC "BoxB_w" `MEM (Box B) w` THEN (USE_THEN "BoxB_w" CLEAR_TAC) THEN
   STRIP_TAC THEN
   HYP_SUFFICE_TAC `Box B IN M` "Mfin" [MEM_LIST_OF_SET] THEN
    HYP_SUFFICE_TAC `Box B IN X` "Msuper" [SUBSET] THEN
    EXPAND_TAC "X" THEN
    REWRITE_TAC[IN_INSERT] THEN
    SUFFICE_TAC `Box B IN {Box C | Box C IN set_of_list w}` [] THEN
    SUFFICE_WITH_TAC `Box B IN set_of_list w` SET_TAC [] THEN
    REWRITE_TAC[IN_SET_OF_LIST] THEN
    FROM_TAC ["BoxB_w"] THEN BY ASM_CLEAR_TAC
    ; ALL_TAC] THEN
  SHOW_TAC `Q_REL p (list_of_set M) w ==> w = list_of_set M` THEN
    SUFFICE_TAC `~(Q_REL p (list_of_set M) w)` [] THEN
    HYP REWRITE_TAC "w_std M_std" [Q_REL_DEF; NOT_FORALL_THM; NOT_IMP] THEN
    EXISTS_TAC `q --> Box q` THEN
    CONJ_TAC THENL
    [DISJ2_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
    [HYP_SUFFICE_TAC `Box (q --> Box q) IN M` "Mfin" [MEM_LIST_OF_SET] THEN
      HYP_SUFFICE_TAC `Box (q --> Box q) IN X` "Msuper" [SUBSET] THEN
      EXPAND_TAC "X" THEN SET_TAC[];
     REFUTE_THEN (LABEL_TAC "mem") THEN
      REMOVE_THEN "box_w" MP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA THEN
      MAP_EVERY EXISTS_TAC [`S4GRZ_AX`; `p:form`; `[Box (q --> Box q); q]`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MEM] THEN
      CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[CONJLIST; NOT_CONS_NIL] THEN MATCH_MP_TAC S4GRZ_prove_S4 THEN
      HOLMS_TAC]]);;

(* let NOT_HOLDS_S4GRZ_STANDARD_FRAME = prove
 (`!p. ~[S4GRZ_AX . {} |~ p]
       ==> ?w. w IN S4GRZ_STANDARD_WORLDS p /\
               ~holds (S4GRZ_STD_FRAME p) (STANDARD_EVAL' p) p w`,
  INTRO_TAC "!p; p" THEN
  CLAIM_TAC "@w. max_cons hp sub"
     `?M. MAXIMAL_CONSISTENT S4GRZ_AX p M /\
          (!q. MEM q M
               ==> q SUBSENTENCE p \/
                   (?C.
                        Box C SUBFORMULA p /\
                        (q = Box (C --> Box C) \/
                         q = Not Box (C --> Box C)))) /\
          [Not p] SUBLIST M` THENL
   [MATCH_MP_TAC S4GRZ_EXTEND_MAXIMAL_CONSISTENT THEN
    CONJ_TAC THENL [
     REWRITE_TAC[CONSISTENT_IFF_SETCONSISTENT; set_of_list] THEN
     ASM_REWRITE_TAC[SETCONSISTENT_SING; MLK_DOUBLENEG_IFF];
     REWRITE_TAC[MEM; SUBSENTENCE_CASES] THEN
     MESON_TAC[SUBFORMULA_REFL]];
    ALL_TAC]
  EXISTS_TAC `w:form list`

  HYP_TAC "sub" (REWRITE_RULE[CONS_SUBLIST; NIL_SUBLIST]) *)



(* let NOT_HOLDS_IN_S4GRZ_STANDARD_FRAME = prove
 (`!p. ~[S4GRZ_AX . {} |~ p] ==> ~holds_in (S4GRZ_STD_FRAME p) p`,
  REWRITE_TAC[S4GRZ_STD_FRAME; HOLDS_IN]
  INTRO_TAC "!p; hp" THEN
  REWRITE_TAC[WORLDS]
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP]
  EXISTS_TAC `STANDARD_EVAL' p` *)


let S4GRZ_STD_IN_S4GRZ_STANDARD_FRAME = prove
 (`!p. ~ [S4GRZ_AX . {} |~ p]
       ==> (S4GRZ_STD_FRAME p) IN S4GRZ_STANDARD_FRAME p`,
  INTRO_TAC "!p; not_theor_p" THEN
  REWRITE_TAC [S4GRZ_STANDARD_FRAME; PARAMETRIC_STANDARD_FRAME_DEF; IN_INTER] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[RATF_APPR_S4GRZ; S4GRZ_STD_FRAME_IN_RATF]; ALL_TAC] THEN
   REWRITE_TAC[IN_ELIM_PAIR_THM; S4GRZ_STD_FRAME] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[S4GRZ_STANDARD_WORLDS]; ALL_TAC] THEN
  INTRO_TAC "!q w; boxq stdw" THEN
  EQ_TAC THENL
  [ALL_TAC; ASM_MESON_TAC[S4GRZ_ACCESSIBILITY_LEMMA]] THEN
  ASM_REWRITE_TAC[S4GRZ_STANDARD_REL_DEF] THEN
  INTRO_TAC "mem_boxw; !x; stdx Q Q_imp" THEN
  HYP_TAC "Q: stdw stdx Q" (REWRITE_RULE[Q_REL_DEF; S4GRZ_STANDARD_WORLDS;
                            PARAMETRIC_STD_WORLD; IN_ELIM_THM]) THEN
  MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA THEN
  MAP_EVERY EXISTS_TAC [`S4GRZ_AX`; `p:form`; `[Box q]`] THEN
  ASM_REWRITE_TAC[MEM] THEN
  HYP_SUFFICE_TAC
   `q SUBFORMULA p /\  [S4GRZ_AX . {} |~ CONJLIST [Box q] --> q]`
   "Q mem_boxw" [SUBFORMULA_IMP_SUBSENTENCE] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
   MESON_TAC[GRZ_EQ_S4GRZ; GRZ_PROVES_T; T_SCHEMA_DEF; CONJLIST]]);;

(* S4GRZ counterpart of GEN_COUNTERMODEL theorem. *)
let S4GRZ_COUNTERMODEL = prove
 (`!W R V M p. ~ [S4GRZ_AX . {} |~ p] /\
               M IN S4GRZ_STANDARD_WORLDS p /\
               MEM (Not p) M /\
               S4GRZ_STANDARD_MODEL p (W,R) V
               ==> ~holds (W,R) V p M`,
 REPEAT GEN_TAC THEN
 INTRO_TAC "p_not_theor stdworld mem_notp standard_model" THEN
 MP_TAC (ISPECL [`W: (form)list->bool`;
                   `R: (form)list-> (form)list ->bool`;
                   `p:form`;
                   `V:((char)list->(form)list->bool)`;
                   `p:form`] S4GRZ_TRUTH_LEMMA) THEN
 ANTS_TAC THEN
  ASM_REWRITE_TAC[SUBFORMULA_REFL] THEN
  DISCH_THEN (MP_TAC o SPEC `M:form list`) THEN
 ANTS_TAC THEN
  HYP_TAC "standard_model" (REWRITE_RULE[S4GRZ_STANDARD_MODEL_DEF; S4GRZ_STANDARD_FRAME_ALT]) THEN
  HYP_TAC "standard_model: (appr w 1) 2" (REWRITE_RULE[IN_INTER; IN_ELIM_PAIR_THM]) THEN
  REMOVE_THEN "w" SUBST_ALL_TAC THEN
  HYP REWRITE_TAC "stdworld" [] THEN
 DISCH_THEN (SUBST1_TAC o GSYM) THEN
 HYP_TAC "stdworld: maxcons _" (REWRITE_RULE[S4GRZ_STANDARD_WORLDS_DEF; IN_ELIM_THM]) THEN
 ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT_NC]);;

let STANDARD_EVAL = new_definition
  `STANDARD_EVAL p a w <=> Atom a SUBFORMULA p /\ MEM (Atom a) w`;;

let S4GRZ_COUNTERMODEL_ALT = prove
 (`!W R p. ~[S4GRZ_AX . {} |~ p] /\ W,R IN S4GRZ_STANDARD_FRAME p
           ==> ~holds_in (W,R) p`,
  INTRO_TAC "!W R p; p_not_theor stand_fm" THEN
  REWRITE_TAC[HOLDS_IN; NOT_FORALL_THM; NOT_IMP] THEN
  EXISTS_TAC `STANDARD_EVAL p` THEN
  DESTRUCT_TAC "@M. max mem subs"
     (MATCH_MP GRZ_NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ [S4GRZ_AX . {} |~ p]`)) THEN
  EXISTS_TAC `M:form list` THEN ASM_REWRITE_TAC[] THEN
  SHOW_TAC `M:form list IN WORLDS (W,R)` THENL
  [REWRITE_TAC[WORLDS; IN_ELIM_THM] THEN
  HYP_TAC "stand_fm" (REWRITE_RULE[S4GRZ_STANDARD_FRAME_ALT]) THEN
  HYP_TAC "stand_fm: appr w_wd w_subs" (REWRITE_RULE[IN_INTER; IN_ELIM_PAIR_THM]) THEN
  REMOVE_THEN "w_wd" SUBST_ALL_TAC THEN
  HYP REWRITE_TAC "max subs" [S4GRZ_STANDARD_WORLDS_DEF; IN_ELIM_THM]; ALL_TAC] THEN
  MATCH_MP_TAC S4GRZ_COUNTERMODEL THEN
  ASM_REWRITE_TAC[S4GRZ_STANDARD_WORLDS_DEF; IN_ELIM_THM] THEN
  ASM_MESON_TAC[S4GRZ_STANDARD_MODEL_DEF; STANDARD_EVAL]);;

let S4GRZ_COMPLETENESS_THM = prove
 (`!p. RATF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [S4GRZ_AX . {} |~ p]`,
  GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  INTRO_TAC "p_not_theor" THEN
  REWRITE_TAC[valid; NOT_FORALL_THM] THEN
  EXISTS_TAC `S4GRZ_STD_FRAME p` THEN
  REWRITE_TAC[NOT_IMP] THEN 
  CONJ_TAC THENL
  [ASM_MESON_TAC[S4GRZ_STD_FRAME_IN_RATF];
   REWRITE_TAC[S4GRZ_STD_FRAME] THEN
    MATCH_MP_TAC S4GRZ_COUNTERMODEL_ALT THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC [S4GRZ_STD_FRAME; S4GRZ_STD_IN_S4GRZ_STANDARD_FRAME]]);;

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
  ASM_MESON_TAC[RATF_APPR_S4GRZ; GEN_LEMMA_FOR_GEN_COMPLETENESS]);;

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

let GRZ_PROOF_SEARCH_TAC : tactic =
  GEN_REWRITE_TAC I [GRZ_TRANSL] THEN
  CONV_TAC (RAND_CONV TRANSL_CONV) THEN
  REWRITE_TAC[dotbox_DEF] THEN
  GL_PROOF_SEARCH_TAC;;

let itf_to_ratf =
  let refl_worlds =
    let dest_in = dest_binary "IN"
    and worlds_tm = `W:num->bool`
    and accrel_tm = `R:num->num->bool` in
    fun tm -> let ltm,rtm = dest_in tm in
              if rtm <> worlds_tm then fail() else
              mk_binop accrel_tm ltm ltm in
  let subst_ratf_for_itf =
    subst[`RATF:(num->bool)#(num->num->bool)->bool`,
           `ITF:(num->bool)#(num->num->bool)->bool`] in
  fun ctm ->
    let ctm' = subst_ratf_for_itf ctm in
    let l = striplist dest_conj ctm' in
    let l' = mapfilter refl_worlds l @ l in
    end_itlist (curry mk_conj) l';;

let ITF_TO_RATF_TAC : tactic =
  fun gl ->
    the_HOLMS_countermodel := itf_to_ratf !the_HOLMS_countermodel;
    ALL_TAC gl;;
  
(* Call GRZ_PROOF_SEARCH_TAC and translate countermodel in case of failure *)
let GRZ_TAC : tactic =
  GRZ_PROOF_SEARCH_TAC THEN
  TRY HOLMS_COLLECT_COUNTERMODEL THEN
  ITF_TO_RATF_TAC THEN
  FAIL_TAC "GRZ_TAC: Proof not found";;

holms_register_tactic `GRZ_AX` GRZ_TAC;;

let GRZ_HOLMS_CERTIFY_COUNTERMODEL : term -> term -> thm =
  let ltm = `RATF:(num->bool)#(num->num->bool)->bool` in
  fun ctm tm ->
    let fm = rand (snd (strip_forall tm))
    and eth = mk_countermodel_existence_thm ctm in
    prove (mk_not_valid_ptm ltm fm,
           CERTIFY_COUNTERMODEL_TAC eth);;

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

(* ------------------------------------------------------------------------- *)
(* Instrument the countermodel certifier to address GRZ.                     *)
(* ------------------------------------------------------------------------- *)

let IN_RATF_ALT2 = prove
 (`!W:A->bool R.
     (W,R) IN RATF <=>
     ~(W = {}) /\
     (!x y. R x y ==> x IN W /\ y IN W) /\
     FINITE W /\
     (!x. x IN W ==> R x x) /\
     (!x y. R x y /\ R y x ==> x = y) /\
     (!x y z. R x y /\ R y z ==> R x z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_RATF; IN_FINITE_FRAME; REFLEXIVE; ANTISYMMETRIC; TRANSITIVE] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let MK_IN_RATF_THM : thm -> thm =
  let rule = CONV_RULE (REWR_CONV (GSYM IN_RATF_ALT2)) in
  fun eth ->
    rule (end_itlist CONJ
                     [MK_WORLDS_NOT_EMPTY_THM eth;
                      MK_ACCREL_WD_THM eth;
                      MK_WORLDS_FINITE_THM eth;
                      MK_ACCREL_REFL_THM eth;
                      MK_ACCREL_ANTISYM_THM eth;
                      MK_ACCREL_TRANS_THM eth]);;


let () =
  let p =
    `RATF:(num->bool)#(num->num->bool)->bool`,
    MK_IN_RATF_THM
  in
  in_frames_assoc := p :: !in_frames_assoc;;
