(* ========================================================================= *)
(* Consistent and maximal consistent sets of formulas.                       *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2026.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* TODO: Sarebbe meglio se questo file non dipendensse da CONJLIST.          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Consistent sets of formulae.                                              *)
(* ------------------------------------------------------------------------- *)

let SETCONSISTENT = new_definition
  `SETCONSISTENT S X <=> ~[S . X |~ False]`;;

let SETCONSISTENT_NC = prove
 (`!S w p. SETCONSISTENT S w ==> ~[S . w |~ p] \/ ~[S . w |~ Not p]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SETCONSISTENT] THEN
  MESON_TAC[MLK_NC_ALT]);;

let IN_SETCONSISTENT_NC = prove
 (`!S w p. SETCONSISTENT S w ==> ~(p IN w) \/ ~(Not p IN w)`,
  MESON_TAC[SETCONSISTENT_NC; MODPROVES_HP]);;

let SETCONSISTENT_SUBSET = prove
 (`!S X Y. SETCONSISTENT S X /\ Y SUBSET X ==> SETCONSISTENT S Y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SETCONSISTENT] THEN
  MESON_TAC[MODPROVES_MONO2]);;

(* TODO: Eliminare? *)
let NOT_SETCONSISTENT_SUBSET = prove
 (`!S X Y. ~SETCONSISTENT S X /\ X SUBSET Y ==> ~SETCONSISTENT S Y`,
  MESON_TAC[SETCONSISTENT_SUBSET]);;

let SETCONSISTENT_SING = prove
 (`!S p. SETCONSISTENT S {p} <=> ~[S . {} |~ Not p]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SETCONSISTENT] THEN
  REWRITE_TAC[GSYM (REWRITE_CONV[set_of_list] `set_of_list [p]`)] THEN
  REWRITE_TAC[GSYM MODPROVES_DEDUCTION_LEMMA_CONJLIST_EMPTY] THEN
  REWRITE_TAC[CONJLIST; MLK_not_def]);;

let SETCONSISTENT_EXTEND_CASES = prove
 (`!S p X. SETCONSISTENT S X
           ==> SETCONSISTENT S (p INSERT X) \/
               SETCONSISTENT S (Not p INSERT X)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SETCONSISTENT] THEN
  C SUBGOAL_THEN (fun th -> MESON_TAC[th])
   `[S . p INSERT X |~ False] /\
    [S . Not p INSERT X |~ False]
    ==> [S . X |~ False]` THEN
  REWRITE_TAC[GSYM MODPROVES_DEDUCTION_LEMMA; GSYM MLK_disj_imp] THEN
  MESON_TAC[MLK_modusponens; MLK_tnd_th]);;

(* ------------------------------------------------------------------------- *)
(* Maximal consistent sets of formulae.                                      *)
(* ------------------------------------------------------------------------- *)

let MAXIMAL_SETCONSISTENT = new_definition
  `MAXIMAL_SETCONSISTENT S p X <=>
   SETCONSISTENT S X /\
   (!q. q SUBFORMULA p ==> q IN X \/ Not q IN X)`;;

let MAXIMAL_SETCONSISTENT_IMP_SETCONSISTENT = prove
 (`!S p X. MAXIMAL_SETCONSISTENT S p X ==> SETCONSISTENT S X`,
  REWRITE_TAC[MAXIMAL_SETCONSISTENT] THEN MESON_TAC[]);;

let IN_MAXIMAL_SETCONSISTENT_CASES = prove
 (`!S X p q. MAXIMAL_SETCONSISTENT S p X /\ q SUBFORMULA p
             ==> q IN X \/ Not q IN X`,
  REWRITE_TAC[MAXIMAL_SETCONSISTENT] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Subsentences.                                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("SUBSENTENCE",get_infix_status "SUBFORMULA");;

let SUBSENTENCE_RULES,SUBSENTENCE_INDUCT,SUBSENTENCE_CASES =
  new_inductive_definition
  `(!p q. p SUBFORMULA q ==> p SUBSENTENCE q) /\
   (!p q. p SUBFORMULA q ==> Not p SUBSENTENCE q)`;;

let SUBFORMULA_IMP_SUBSENTENCE = prove
 (`!p q. p SUBFORMULA q ==> p SUBSENTENCE q`,
  REWRITE_TAC[SUBSENTENCE_RULES]);;

let SUBFORMULA_IMP_NEG_SUBSENTENCE = prove
 (`!p q. p SUBFORMULA q ==> Not p SUBSENTENCE q`,
  REWRITE_TAC[SUBSENTENCE_RULES]);;

let SUBSENTENCE_EQ_SUBFORMULA = prove
 (`!p. {q | q SUBSENTENCE p} = {q | q SUBFORMULA p} UNION
                               IMAGE (Not) {q | q SUBFORMULA p}`,
  REWRITE_TAC[SUBSENTENCE_CASES] THEN SET_TAC[]);;

let FINITE_SUBSENTENCE = prove
 (`!p. FINITE {q | q SUBSENTENCE p}`,
  GEN_TAC THEN
  REWRITE_TAC[SUBSENTENCE_EQ_SUBFORMULA; FINITE_UNION; FINITE_SUBFORMULA] THEN
  MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_SUBFORMULA]);;

let MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE = prove
 (`!S p w q. MAXIMAL_SETCONSISTENT S p w /\ q SUBFORMULA p
             ==> (q IN w <=> [S . w |~ q])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAXIMAL_SETCONSISTENT; SETCONSISTENT] THEN
  INTRO_TAC "(w em) sub" THEN
  REMOVE_THEN "em" (X_IMP_RES_THEN (LABEL_TAC "em")) THEN
  LABEL_ASM_CASES_TAC "q" `q:form IN w` THEN HYP REWRITE_TAC "q" [] THENL
  [MATCH_MP_TAC MODPROVES_HP THEN HYP REWRITE_TAC "q" [];
   ASM_MESON_TAC[MLK_NC_ALT; MODPROVES_HP]]);;

let MAXIMAL_SETCONSISTENT_NOT_SUBFORMULA_MEMBER_IFF_DERIVABLE = prove
 (`!S p w q. MAXIMAL_SETCONSISTENT S p w /\ q SUBFORMULA p
             ==> (Not q IN w <=> [S . w |~ Not q])`,
  MESON_TAC[MAXIMAL_SETCONSISTENT_IMP_SETCONSISTENT;
    IN_MAXIMAL_SETCONSISTENT_CASES; SETCONSISTENT_NC; MODPROVES_HP]);;

(* ------------------------------------------------------------------------- *)
(* Maximal consistent sets are closed wrt minors.                            *)
(* ------------------------------------------------------------------------- *)

let MAXIMAL_SETCONSISTENT_TRUE_CLOSED = prove
 (`!S p w. MAXIMAL_SETCONSISTENT S p w /\ True SUBFORMULA p ==> True IN w`,
  REPEAT GEN_TAC THEN INTRO_TAC "maxcons sub" THEN
  ASM_SUFFICE_TAC `~(Not True IN w)` [IN_MAXIMAL_SETCONSISTENT_CASES] THEN
  ASM_SUFFICE_TAC `~[S . w |~ Not True]`
   [MAXIMAL_SETCONSISTENT_NOT_SUBFORMULA_MEMBER_IFF_DERIVABLE] THEN
  SUFFICE_TAC `SETCONSISTENT S w` [SETCONSISTENT; MLK_not_true] THEN
  MATCH_MP_TAC MAXIMAL_SETCONSISTENT_IMP_SETCONSISTENT THEN
  HYP MESON_TAC "maxcons" []);;

let MAXIMAL_SETCONSISTENT_NOT_CLOSED = prove
 (`!S p w q. MAXIMAL_SETCONSISTENT S p w /\ Not q SUBFORMULA p
             ==> (Not q IN w <=> ~(q IN w))`,
  REPEAT GEN_TAC THEN INTRO_TAC "maxcons sub" THEN
  CLAIM_TAC "cons" `SETCONSISTENT S w` THENL
  [HYP MESON_TAC "maxcons" [MAXIMAL_SETCONSISTENT_IMP_SETCONSISTENT];
   ALL_TAC] THEN
  CLAIM_TAC "q" `q SUBFORMULA p` THENL
  [HYP MESON_TAC "sub" [MINOR_SUBFORMULA]; ALL_TAC] THEN
  ASM_MESON_TAC[IN_MAXIMAL_SETCONSISTENT_CASES; IN_SETCONSISTENT_NC]);;

let MAXIMAL_SETCONSISTENT_AND_MIONOR_CLOSED = prove
 (`!S p w q1 q2. MAXIMAL_SETCONSISTENT S p w /\ q1 && q2 SUBFORMULA p
                 ==> (q1 && q2 IN w <=> q1 IN w /\ q2 IN w)`,
  REPEAT GEN_TAC THEN INTRO_TAC "maxcons sub" THEN
  TRANS_TAC EQ_TRANS `[S . w |~ q1 && q2]` THEN CONJ_TAC THENL
  [MATCH_MP_TAC MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE THEN
   ASM_MESON_TAC[];
   REWRITE_TAC[MLK_and]] THEN
  ASM_MESON_TAC[MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE;
                MINOR_SUBFORMULA]);;

let MAXIMAL_SETCONSISTENT_MINOR_OR_CLOSED = prove
 (`!S p w q1 q2. MAXIMAL_SETCONSISTENT S p w /\ q1 || q2 SUBFORMULA p
                 ==> (q1 || q2 IN w <=> q1 IN w \/ q2 IN w)`,
  REPEAT GEN_TAC THEN INTRO_TAC "maxcons sub" THEN EQ_TAC THENL
  [
   SUFFICE_TAC `~(q1 IN w) /\ ~(q2 IN w) ==> ~(q1 || q2 IN w)` [] THEN
   CLAIM_TAC "cons" `SETCONSISTENT S w` THENL
   [MATCH_MP_TAC MAXIMAL_SETCONSISTENT_IMP_SETCONSISTENT THEN
    HYP MESON_TAC "maxcons" [];
    ALL_TAC] THEN
   INTRO_TAC "hp" THEN
   ASM_SUFFICE_TAC `Not (q1 || q2) IN w` [IN_SETCONSISTENT_NC] THEN
   ASM_SUFFICE_TAC `[S . w |~ Not (q1 || q2)]`
    [MAXIMAL_SETCONSISTENT_NOT_SUBFORMULA_MEMBER_IFF_DERIVABLE] THEN
   SUFFICE_TAC `[S . w |~ Not q1] /\ [S . w |~ Not q2]` [MLK_proves_not_or] THEN
   SUFFICE_TAC `Not q1 IN w /\ Not q2 IN w` [MODPROVES_HP] THEN
   ASM_MESON_TAC[IN_MAXIMAL_SETCONSISTENT_CASES; MINOR_SUBFORMULA]
  ;
   INTRO_TAC "hp" THEN
   ASM_SUFFICE_TAC `[S . w |~ q1 || q2]`
    [MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE] THEN
   HYP MESON_TAC "hp" [MLK_or_introl; MLK_or_intror; MODPROVES_HP]
  ]);;

let MAXIMAL_SETCONSISTENT_IMP_CLOSED = prove
 (`!S p w q1 q2. MAXIMAL_SETCONSISTENT S p w /\ q1 --> q2 SUBFORMULA p
                 ==> (q1 --> q2 IN w <=> (q1 IN w ==> q2 IN w))`,
  REPEAT GEN_TAC THEN INTRO_TAC "maxcons sub" THEN EQ_TAC THENL
  [
   SUFFICE_TAC `q1 --> q2 IN w /\ q1 IN w ==> q2 IN w` [] THEN
   INTRO_TAC "hp1 hp2" THEN
   ASM_SUFFICE_TAC `[S . w |~ q2]`
    [MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE;
     MINOR_SUBFORMULA] THEN
   MATCH_MP_TAC MLK_modusponens THEN
   ASM_MESON_TAC[MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE;
                 MINOR_SUBFORMULA]
  ;
   INTRO_TAC "hp" THEN
   ASM_SUFFICE_TAC `[S . w |~ q1 --> q2]`
    [MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE] THEN
   HYP_SUFFICE_TAC `Not q1 IN w \/ q2 IN w` "hp"
    [MLK_imp_introl; MLK_add_assum; MODPROVES_HP] THEN
   ASM_MESON_TAC[IN_MAXIMAL_SETCONSISTENT_CASES; MINOR_SUBFORMULA]
  ]);;

let MAXIMAL_SETCONSISTENT_IFF_CLOSED = prove
 (`!S p w q1 q2. MAXIMAL_SETCONSISTENT S p w /\ q1 <-> q2 SUBFORMULA p
                 ==> (q1 <-> q2 IN w <=> (q1 IN w <=> q2 IN w))`,
  REPEAT GEN_TAC THEN INTRO_TAC "maxcons sub" THEN
  CLAIM_TAC "q1 q2" `q1 SUBFORMULA p /\ q2 SUBFORMULA p` THENL
  [HYP MESON_TAC "sub" [MINOR_SUBFORMULA]; ALL_TAC] THEN
  EQ_TAC THENL
  [ASM_SUFFICE_TAC `[S . w |~ q1 <-> q2] ==> ([S . w |~ q1] <=> [S . w |~ q2])`
    [MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE] THEN
   MESON_TAC[MLK_iff_mp; MLK_iff_sym];
   ALL_TAC] THEN
   SUFFICE_TAC `(q1 IN w /\ q2 IN w ==> q1 <-> q2 IN w) /\
                (~(q1 IN w) /\ ~(q2 IN w) ==> q1 <-> q2 IN w)` [] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[MLK_proves_iff_pos;
                  MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE];
    ALL_TAC] THEN
   INTRO_TAC "hp" THEN
   ASM_SUFFICE_TAC `[S . w |~ q1 <-> q2]`
    [MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE] THEN
   ASM_SUFFICE_TAC `[S . w |~ Not q1] /\ [S . w |~ Not q2]`
    [MLK_proves_iff_neg] THEN
   ASM_SUFFICE_TAC `Not q1 IN w /\ Not q2 IN w` [MODPROVES_HP] THEN
   ASM_MESON_TAC[IN_MAXIMAL_SETCONSISTENT_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Maximal extension of a consistent set of formulae.                        *)
(* ------------------------------------------------------------------------- *)

let EXTEND_MAXIMAL_SETCONSISTENT = prove
 (`!S p X. SETCONSISTENT S X /\
           (!q. q IN X ==> q SUBSENTENCE p)
           ==> ?M. MAXIMAL_SETCONSISTENT S p M /\
                   (!q. q IN M ==> q SUBSENTENCE p) /\
                   X SUBSET M`,
  FIX_TAC "S p" THEN CLAIM_TAC "rmk"
    `!s. FINITE s
         ==> !X. SETCONSISTENT S X /\
                 (!q. q IN X ==> q SUBSENTENCE p) /\
                 (!q. q IN s ==> q SUBFORMULA p) /\
                 (!q. q SUBFORMULA p ==> q IN s \/ q IN X \/ Not q IN X)
                 ==> ?M. MAXIMAL_SETCONSISTENT S p M /\
                         (!q. q IN M ==> q SUBSENTENCE p) /\
                         X SUBSET M` THENL
  [MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY] THEN
    MESON_TAC[MAXIMAL_SETCONSISTENT; SUBSET_REFL];
    ALL_TAC] THEN
   INTRO_TAC "!x s; s_ind x_fresh _" THEN REWRITE_TAC[FORALL_IN_INSERT] THEN
   REWRITE_TAC[IN_INSERT] THEN
   INTRO_TAC "!X; X_cons X_sub (x_sub s_sub) X_max" THEN
   CLAIM_TAC "@y. y y_cons"
     `?y. (y = x \/ y = Not x) /\ SETCONSISTENT S (y INSERT X)` THENL
   [IMP_RES_THEN MP_TAC SETCONSISTENT_EXTEND_CASES THEN MESON_TAC[]; ALL_TAC] THEN
   HYP_TAC "s_ind: +" (SPEC `y:form INSERT X`) THEN
   ASM_REWRITE_TAC[FORALL_IN_INSERT] THEN REWRITE_TAC[IN_INSERT] THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [REWRITE_TAC[SUBSENTENCE_CASES] THEN HYP MESON_TAC "x_sub y" [];
     HYP MESON_TAC "y X_max x_sub" []];
    REWRITE_TAC[INSERT_SUBSET] THEN INTRO_TAC "@M. M_max M_sub y_M X_M"] THEN
   EXISTS_TAC `M:form->bool` THEN HYP REWRITE_TAC "M_max M_sub X_M" [];
   ALL_TAC] THEN
  INTRO_TAC "!X; X_cons X_sub" THEN
  SUBGOAL_THEN `FINITE {q | q SUBFORMULA p}` (X_ANTE_RES_THEN MP_TAC) THENL
  [MATCH_ACCEPT_TAC FINITE_SUBFORMULA; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPEC `X:form->bool`) THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN SIMP_TAC[IN_ELIM_THM]);;

let NONEMPTY_MAXIMAL_SETCONSISTENT = prove
 (`!S p. ~[S . {} |~ p]
         ==> (?M. MAXIMAL_SETCONSISTENT S p M /\
                  Not p IN M /\
                  (!q. q IN M ==> q SUBSENTENCE p))`,
  INTRO_TAC "!S p; p" THEN
  MP_TAC (SPECL [`S:form->bool`; `p:form`; `{Not p}`]
    EXTEND_MAXIMAL_SETCONSISTENT) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[SETCONSISTENT_SING; MLK_DOUBLENEG_IFF] THEN
   SET_TAC[SUBSENTENCE_CASES; injectivity "form"; SUBFORMULA_REFL];
   INTRO_TAC "@M. +"] THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN STRIP_TAC THEN
  EXISTS_TAC `M:form->bool` THEN ASM_REWRITE_TAC[]);;
