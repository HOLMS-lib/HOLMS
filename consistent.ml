(* ========================================================================= *)
(* Consistent list of formulas.                                              *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

let CONSISTENT = new_definition
  `CONSISTENT S (l:form list) <=> ~[S . {} |~ Not (CONJLIST l)]`;;

let CONSISTENT_SING = prove
 (`!S p. CONSISTENT S [p] <=> ~[S . {} |~ Not p]`,
  REWRITE_TAC[CONSISTENT; CONJLIST]);;

let CONSISTENT_LEMMA = prove
 (`!S X p. MEM p X /\ MEM (Not p) X ==> [S. {} |~ Not (CONJLIST X)]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLK_not_def] THEN
  MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `p && Not p` THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_and_intro THEN
   ASM_MESON_TAC[CONJLIST_IMP_MEM; MLK_imp_trans; MLK_and_pair_th];
   MESON_TAC[MLK_nc_th]]);;

let CONSISTENT_SUBLIST = prove
 (`!S X Y. CONSISTENT S X /\ Y SUBLIST X ==> CONSISTENT S Y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONSISTENT] THEN
  SUBGOAL_THEN `[S . {} |~ CONJLIST Y --> False]/\ Y SUBLIST X
                ==> [S . {} |~  CONJLIST X --> False]`
    (fun th -> ASM_MESON_TAC[th; MLK_not_def]) THEN
  INTRO_TAC "inc sub" THEN MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `CONJLIST Y` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CONJLIST_IMP_SUBLIST]);;

let CONSISTENT_CONS = prove
 (`!S h t. CONSISTENT S (CONS h t) <=> ~[S . {} |~ Not h || Not CONJLIST t]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONSISTENT] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MLK_iff THEN MATCH_MP_TAC MLK_iff_trans THEN
  EXISTS_TAC `Not (h && CONJLIST t)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_not_subst THEN MATCH_ACCEPT_TAC CONJLIST_CONS;
   MATCH_ACCEPT_TAC MLK_de_morgan_and_th]);;

let CONSISTENT_NC = prove
 (`!S X p. MEM p X /\ MEM (Not p) X ==> ~CONSISTENT S X`,
  INTRO_TAC "!S X p; p np" THEN REWRITE_TAC[CONSISTENT; MLK_not_def] THEN
  MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `p && Not p` THEN
  REWRITE_TAC[MLK_nc_th] THEN MATCH_MP_TAC MLK_and_intro THEN
  ASM_SIMP_TAC[CONJLIST_IMP_MEM]);;

let CONSISTENT_EM = prove
 (`!S h t. CONSISTENT S t
           ==> CONSISTENT S (CONS h t) \/ CONSISTENT S (CONS (Not h) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONSISTENT_CONS] THEN
  REWRITE_TAC[CONSISTENT] THEN
  SUBGOAL_THEN
    `[S . {} |~ (Not h || Not CONJLIST t) --> (Not Not h || Not CONJLIST t)
                --> Not CONJLIST t]`
    (fun th -> MESON_TAC[th; MLK_modusponens]) THEN
  REWRITE_TAC[MLK_disj_imp] THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_imp_swap THEN REWRITE_TAC[MLK_disj_imp] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC MLK_imp_swap THEN MATCH_MP_TAC MLK_shunt THEN
    MATCH_MP_TAC MLK_frege THEN EXISTS_TAC `False` THEN
    REWRITE_TAC[MLK_nc_th] THEN
    MATCH_MP_TAC MLK_add_assum THEN MATCH_ACCEPT_TAC MLK_ex_falso_th;
    MATCH_ACCEPT_TAC MLK_axiom_addimp];
   MATCH_MP_TAC MLK_imp_swap THEN REWRITE_TAC[MLK_disj_imp] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC MLK_add_assum THEN MATCH_ACCEPT_TAC MLK_imp_refl_th;
    MATCH_ACCEPT_TAC MLK_axiom_addimp]]);;

let FALSE_IMP_NOT_CONSISTENT = prove
 (`!S X. MEM False X ==> ~ CONSISTENT S X`,
  SIMP_TAC[CONSISTENT; FALSE_NOT_CONJLIST]);;

(* ------------------------------------------------------------------------- *)
(* Maximal Consistent Sets.                                                  *)
(* See Boolos p.79 (pdf p.118).  D in the text is p here.                    *)
(* ------------------------------------------------------------------------- *)

let MAXIMAL_CONSISTENT = new_definition
  `MAXIMAL_CONSISTENT S p X <=>
   CONSISTENT S X /\ NOREPETITION X /\
   (!q. q SUBFORMULA p ==> MEM q X \/ MEM (Not q) X)`;;

let MAXIMAL_CONSISTENT_LEMMA = prove
 (`!S p X A b. MAXIMAL_CONSISTENT S p X /\
               (!q. MEM q A ==> MEM q X) /\
               b SUBFORMULA p /\
               [S . {} |~ CONJLIST A --> b]
               ==> MEM b X`,
  INTRO_TAC "!S p X A b; mconst subl b Ab" THEN REFUTE_THEN ASSUME_TAC THEN
  CLAIM_TAC "rmk" `MEM (Not b) X` THENL
  [ASM_MESON_TAC[MAXIMAL_CONSISTENT]; ALL_TAC] THEN
  CLAIM_TAC "rmk2" `[S . {} |~ CONJLIST X --> b && Not b]` THENL
  [MATCH_MP_TAC MLK_and_intro THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONJLIST_MONO; MLK_imp_trans];
    ASM_MESON_TAC[CONJLIST_IMP_MEM]];
   ALL_TAC] THEN
  CLAIM_TAC "rmk3" `[S . {} |~ CONJLIST X --> False]` THENL
  [ASM_MESON_TAC[MLK_imp_trans; MLK_nc_th]; ALL_TAC] THEN
  SUBGOAL_THEN `~CONSISTENT S X`
    (fun th -> ASM_MESON_TAC[th; MAXIMAL_CONSISTENT]) THEN
  ASM_REWRITE_TAC[CONSISTENT; MLK_not_def]);;

let MAXIMAL_CONSISTENT_MEM_NOT = prove
 (`!S X p q. MAXIMAL_CONSISTENT S p X /\ q SUBFORMULA p
             ==> (MEM (Not q) X <=> ~ MEM q X)`,
  REWRITE_TAC[MAXIMAL_CONSISTENT] THEN MESON_TAC[CONSISTENT_NC]);;

let MAXIMAL_CONSISTENT_MEM_CASES = prove
 (`!S X p q. MAXIMAL_CONSISTENT S p X /\ q SUBFORMULA p
             ==> (MEM q X \/ MEM (Not q) X)`,
  REWRITE_TAC[MAXIMAL_CONSISTENT] THEN MESON_TAC[CONSISTENT_NC]);;

let MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE = prove
 (`!S p w q. MAXIMAL_CONSISTENT S p w /\ q SUBFORMULA p
             ==> (MEM q w <=> [S . {} |~ CONJLIST w --> q])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAXIMAL_CONSISTENT; CONSISTENT] THEN
  INTRO_TAC "(w em) sub" THEN LABEL_ASM_CASES_TAC "q" `MEM (q:form) w` THEN
  ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN CLAIM_TAC "nq" `MEM (Not q) w` THENL
  [ASM_MESON_TAC[]; INTRO_TAC "deriv"] THEN
  SUBGOAL_THEN `[S . {} |~  Not (CONJLIST w)]` (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[MLK_not_def] THEN MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `q && Not q` THEN REWRITE_TAC[MLK_nc_th] THEN
  ASM_SIMP_TAC[MLK_and_intro; CONJLIST_IMP_MEM]);;

let MAXIMAL_CONSISTENT_SUBFORMULA_MEM_NEG_EQ_DERIVABLE = prove
 (`!S p w q. MAXIMAL_CONSISTENT S p w /\ q SUBFORMULA p
             ==> (MEM (Not q) w <=> [S . {} |~  CONJLIST w --> Not q])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAXIMAL_CONSISTENT; CONSISTENT] THEN
  INTRO_TAC "(w em) sub" THEN LABEL_ASM_CASES_TAC "q" `MEM (Not q) w` THEN
  ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN CLAIM_TAC "nq" `MEM (q:form) w` THENL
  [ASM_MESON_TAC[]; INTRO_TAC "deriv"] THEN
  SUBGOAL_THEN `[ S . {} |~  (Not (CONJLIST w))]` (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[MLK_not_def] THEN MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `q && Not q` THEN REWRITE_TAC[MLK_nc_th] THEN
  ASM_SIMP_TAC[MLK_and_intro; CONJLIST_IMP_MEM]);;

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

(* ------------------------------------------------------------------------- *)
(* Extension Lemma.                                                          *)
(* Every consistent list of formulae can be extended to a maximal consistent *)
(* list by a construction similar to Lindenbaum's extension.                 *)
(* ------------------------------------------------------------------------- *)

let EXTEND_MAXIMAL_CONSISTENT = prove
 (`!S p X. CONSISTENT S X /\
           (!q. MEM q X ==> q SUBSENTENCE p)
           ==> ?M. MAXIMAL_CONSISTENT S p M /\
                   (!q. MEM q M ==> q SUBSENTENCE p) /\
                   X SUBLIST M`,
  GEN_TAC THEN GEN_TAC THEN SUBGOAL_THEN
    `!L X. CONSISTENT S X /\ NOREPETITION X /\
           (!q. MEM q X ==> q SUBSENTENCE p) /\
           (!q. MEM q L ==> q SUBFORMULA p) /\
           (!q. q SUBFORMULA p ==> MEM q L \/ MEM q X \/ MEM (Not q) X)
           ==> ?M. MAXIMAL_CONSISTENT S p M /\
                   (!q. MEM q M ==> q SUBSENTENCE p) /\
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

let NONEMPTY_MAXIMAL_CONSISTENT = prove
 (`!S p. ~ [S . {} |~ p]
         ==> ?M. MAXIMAL_CONSISTENT S p M /\
                 MEM (Not p) M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)`,
  INTRO_TAC "!S p; p" THEN
  MP_TAC (SPECL [`S:form->bool`; `p:form`; `[Not p]`]
    EXTEND_MAXIMAL_CONSISTENT) THEN
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
