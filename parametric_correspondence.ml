(* ========================================================================= *)
(* Correspondence Theory: Parametric Polimorphic Code.                       *)
(*                                                                           *)
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
 (`!W:W->bool R:W->W->bool.
     (W,R) IN FINITE_FRAME <=>
     ~(W = {}) /\ (!x y:W. R x y ==> x IN W /\ y IN W) /\ FINITE W`,
  REWRITE_TAC[FINITE_FRAME_DEF; IN_FRAME; IN_ELIM_THM; PAIR_EQ] THEN
  MESON_TAC[]);;

let IN_FINITE_FRAME_INTER = prove
 (`!W:W->bool R:W->W->bool.
     (W,R) IN FINITE_FRAME <=>
     (W,R) IN FRAME /\ FINITE W`,
  REWRITE_TAC[IN_ELIM_THM; IN_FINITE_FRAME; IN_FRAME] THEN
  MESON_TAC[]);;

let FINITE_FRAME_SUBSET_FRAME = prove
 (`FINITE_FRAME:(W->bool)#(W->W->bool)->bool SUBSET FRAME`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_FINITE_FRAME; IN_FRAME] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Frames characteristic to certain axioms schemata S: CHAR S.               *)
(* ------------------------------------------------------------------------- *)

let CHAR_DEF = new_definition
  `CHAR S = {(W:W->bool,R:W->W->bool) |
                    (W,R) IN FRAME /\
                    (!p. p IN S ==> holds_in (W:W->bool,R:W->W->bool) p)}`;;

let IN_CHAR = prove
 (`!S. (W:W->bool,R:W->W->bool) IN CHAR S <=>
       (W,R) IN FRAME /\
       !p. p IN S ==> holds_in (W:W->bool,R:W->W->bool) p`,
  REWRITE_TAC[CHAR_DEF; IN_ELIM_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* General Validity.                                                         *)
(* ------------------------------------------------------------------------- *)
(*TODO: rivedere*)

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