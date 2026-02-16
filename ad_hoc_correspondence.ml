(* ========================================================================= *)
(* Correspondence Theory: Ad Hoc Polimorphic Code.                           *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

needs "HOLMS/calculus.ml";;

(* ------------------------------------------------------------------------- *)
(* Axiom Schemata.                                                           *)
(* ------------------------------------------------------------------------- *)

let D_SCHEMA_DEF = new_definition
  `D_SCHEMA p = (Box p --> Diam p)`;;

let T_SCHEMA_DEF = new_definition
  `T_SCHEMA p = (Box p --> p)`;;

let FOUR_SCHEMA_DEF = new_definition
  `FOUR_SCHEMA p = (Box p --> Box Box p)`;;

let B_SCHEMA_DEF = new_definition
  `B_SCHEMA p = (p --> Box (Diam p))`;;

let FIVE_SCHEMA_DEF = new_definition
   `FIVE_SCHEMA p = (Diam p --> Box Diam p)`;;

let LOB_SCHEMA_DEF = new_definition
  `LOB_SCHEMA p = Box (Box p --> p) --> Box p`;;

(* ------------------------------------------------------------------------- *)
(* Properties of Binary Relationship.                                        *)
(* ------------------------------------------------------------------------- *)

let SERIAL = new_definition
  `SERIAL W R <=> (!w:W. w IN W ==> ?y:W. y IN W /\ (R w y))`;;

let REFLEXIVE = new_definition
  `REFLEXIVE W R <=> (!w:W. w IN W ==> R w w)`;;

let IRREFLEXIVE = new_definition
  `IRREFLEXIVE W R <=> (!x:W. x IN W ==> ~R x x)`;;

let TRANSITIVE = new_definition
  `TRANSITIVE W R <=>
   (!w w' w'':W. w IN W /\ w' IN W /\ w'' IN W /\
                 R w w' /\ R w' w''
                 ==> R w w'')`;;

let SYMMETRIC = new_definition
  `SYMMETRIC W R <=>
   (!w w':W. w IN W /\ w' IN W /\ R w w' ==> R w' w)`;;

let ANTISYMMETRIC = new_definition
  `ANTISYMMETRIC W R <=>
   (!w w':W. w IN W /\ w' IN W /\ R w w' /\ R w' w ==> w = w')`;;

let EUCLIDEAN = new_definition
  `EUCLIDEAN W R <=>
   (!w w' w'':W. w IN W /\ w' IN W /\ w'' IN W /\
                 R w w' /\ R w w''
                 ==> R w'' w')`;;

(* ------------------------------------------------------------------------- *)
(* Correspondence Lemmata.                                                   *)
(* ------------------------------------------------------------------------- *)

let MODAL_SER = prove
 (`!W:W->bool R. SERIAL W R <=>
                 (!p. holds_in (W,R) (D_SCHEMA p))`,
  REWRITE_TAC[diam_DEF; D_SCHEMA_DEF] THEN MODAL_SCHEMA_TAC THEN
  MESON_TAC[SERIAL]);;

let MODAL_REFL = prove
 (`!W:W->bool R. REFLEXIVE W R <=> (!p. holds_in (W,R) (T_SCHEMA p))`,
  REWRITE_TAC[REFLEXIVE; T_SCHEMA_DEF] THEN MODAL_SCHEMA_TAC THEN
  MESON_TAC[]);;

let MODAL_TRANS = prove
 (`!W:W->bool R. TRANSITIVE W R <=> (!p. holds_in (W,R) (FOUR_SCHEMA p))`,
  REWRITE_TAC[TRANSITIVE; FOUR_SCHEMA_DEF] THEN
  MODAL_SCHEMA_TAC THEN MESON_TAC[]);;

let MODAL_SYM = prove
 (`!W:W->bool R. SYMMETRIC W R <=>
                 (!p. holds_in (W,R) (B_SCHEMA p))`,
  ASM_REWRITE_TAC[diam_DEF; SYMMETRIC; B_SCHEMA_DEF] THEN MODAL_SCHEMA_TAC THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; REPEAT STRIP_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`\v:W. v = w`; `w:W`]) THEN ASM_MESON_TAC[]);;

let MODAL_EUCL = prove
 (`!W:W->bool R. EUCLIDEAN W R <=>
                 (!p. holds_in (W,R) (FIVE_SCHEMA p))`,
  REWRITE_TAC[diam_DEF; EUCLIDEAN; FIVE_SCHEMA_DEF] THEN MODAL_SCHEMA_TAC THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; REPEAT STRIP_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`\v:W. v = w'`; `w:W`]) THEN
  ASM_MESON_TAC[]);;

let MODAL_TRANSNT = prove
 (`!W:W->bool R. (!x y. R x y ==> x IN W /\ y IN W)
                 ==> (TRANSITIVE W R /\ WF(\x y. R y x) <=>
                      !p. holds_in (W,R) (LOB_SCHEMA p))`,
  REWRITE_TAC[TRANSITIVE; LOB_SCHEMA_DEF] THEN MODAL_SCHEMA_TAC THEN
  DISCH_TAC THEN EQ_TAC THENL
  [INTRO_TAC "TRANS WF" THEN HYP_TAC "WF" (REWRITE_RULE[WF_IND]) THEN
   REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "U" THEN CONJ_TAC THENL
  [X_GEN_TAC `w:W` THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`\v:W. v IN W /\ R w v /\ !w''. w'' IN W /\ R v w'' ==> R w w''`;
    `w:W`]) THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[WF_IND] THEN X_GEN_TAC `P:W->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\x:W. !w:W. x IN W /\ R w x ==> P x`) THEN
  MATCH_MP_TAC MONO_FORALL THEN ASM_MESON_TAC[]);;
