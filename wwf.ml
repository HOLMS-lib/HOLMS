(* ========================================================================= *)
(* Weakly wellfounded relation.                                              *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2026.                                  *)
(* ========================================================================= *)

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
