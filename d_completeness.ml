(* ========================================================================= *)
(* Proof of the consistency and modal completeness of D.                     *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2026.                                  *)
(* ========================================================================= *)

needs "HOLMS/k_decid.ml";;       (* Used in  D_EQ_D' and  D_EQ_D_bot         *)

(* ------------------------------------------------------------------------- *)
(* Axiomatisation of D.                                                      *)
(* ------------------------------------------------------------------------- *)

let D_AX = new_definition
  `D_AX = {D_SCHEMA p | p IN (:form)}`;; 

let D_IN_D_AX = prove
 (`!q. Box q --> Diam q IN D_AX`,
  REWRITE_TAC[D_AX; D_SCHEMA_DEF; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]);;

let D_AX_D= prove
 (`!q. [D_AX. {} |~ (Box q --> Diam q)]`,
  MESON_TAC[MODPROVES_RULES; D_IN_D_AX]);;

(* ------------------------------------------------------------------------- *)
(* Alternative axiomatisation.                                               *)
(* ------------------------------------------------------------------------- *)

let D_not_box_bot_SCHEMA_DEF = new_definition
  `D_SCHEMA_not_box_bot = Not Box False`;;

let D_bot_AX = new_definition
  `D_bot_AX = {D_SCHEMA False}`;;

let D_bot_IN_D_bot_AX = prove
 (`Box False --> Diam False IN D_bot_AX`,
  REWRITE_TAC[D_bot_AX; D_SCHEMA_DEF; IN_ELIM_THM; IN_UNIV] THEN SET_TAC[]);;

let D_bot_AX_D_bot= prove
 (`[D_bot_AX. {} |~ (Box False --> Diam False)]`,
  MESON_TAC[MODPROVES_RULES; D_bot_IN_D_bot_AX]);;


let D'_AX = new_definition
  `D'_AX = {D_SCHEMA_not_box_bot}`;;

let D'_IN_D'_AX = prove
 (`Not Box False IN D'_AX`,
  REWRITE_TAC[D'_AX; D_not_box_bot_SCHEMA_DEF; IN_ELIM_THM; IN_UNIV] THEN 
  SET_TAC[]);;

let D'_AX_D'= prove
 (`[D'_AX. {} |~ Not Box False]`,
  MESON_TAC[MODPROVES_RULES; D'_IN_D'_AX]);;

let D_bot_prove_K = prove
 (`!H p. [{} . H |~ p] ==> [D_bot_AX . H |~ p]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MODPROVES_MONO1 THEN
  EXISTS_TAC `{}:form->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let D'_prove_K = prove
 (`!H p. [{} . H |~ p] ==> [D'_AX . H |~ p]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MODPROVES_MONO1 THEN
  EXISTS_TAC `{}:form->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let D_EQ_D_bot = prove
 (`!H p. [D_AX . H |~ p] <=> [D_bot_AX . H |~ p]`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [SUBGOAL_THEN `!H p. [D_AX . H |~ p] ==> [D_bot_AX . H |~ p]` MP_TAC THENL
   [MATCH_MP_TAC MODPROVES_INDUCT THEN REPEAT CONJ_TAC THENL
    [MESON_TAC[MODPROVES_RULES];
     REWRITE_TAC[IN_ELIM_THM; D_AX; IN_UNION] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[D_SCHEMA_DEF; diam_DEF] THEN
      MATCH_MP_TAC MLK_imp_mp_subst THEN
      EXISTS_TAC `Box p'` THEN ASM_REWRITE_TAC[MLK_iff_refl_th] THEN
      EXISTS_TAC `Box Not p' --> False` THEN
      CONJ_TAC THENL [MESON_TAC[MLK_iff_sym; MLK_axiom_not]; ALL_TAC] THEN
      MATCH_MP_TAC MLK_imp_trans2 THEN
      EXISTS_TAC `Box False` THEN CONJ_TAC THENL 
      [MATCH_MP_TAC  D_bot_prove_K THEN
        MATCH_MP_TAC MODPROVES_MONO2 THEN EXISTS_TAC `{}:form->bool` THEN 
        CONJ_TAC THENL [HOLMS_TAC; ASM_MESON_TAC[EMPTY_SUBSET]];
       MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `Diam False` THEN
        CONJ_TAC THENL
          [MESON_TAC[D_bot_AX_D_bot; MODPROVES_MONO2; EMPTY_SUBSET];
           MATCH_MP_TAC MLK_iff_mp THEN EXISTS_TAC `Not Diam False` THEN
           REWRITE_TAC[MLK_axiom_not; diam_DEF] THEN
           MATCH_MP_TAC MLK_DOUBLENEG THEN
           MATCH_MP_TAC MLK_necessitation THEN
           MATCH_MP_TAC MLK_iff_mp THEN EXISTS_TAC `False --> False` THEN
           MESON_TAC[MLK_axiom_not; MLK_iff_sym; MLK_imp_refl_th]]];
       MESON_TAC[MODPROVES_RULES];
       MESON_TAC[MODPROVES_RULES];
       MESON_TAC[MODPROVES_RULES]];
     MESON_TAC[]];
    DISCH_TAC THEN MATCH_MP_TAC MODPROVES_MONO1 THEN EXISTS_TAC `D_bot_AX` THEN
     CONJ_TAC THENL [SET_TAC[D_bot_AX; D_AX]; ASM_REWRITE_TAC[]]]);;

let D_EQ_D' = prove
 (`!H p. [D_AX . H |~ p] <=> [D'_AX . H |~ p]`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [SUBGOAL_THEN `!H p. [D_AX . H |~ p] ==> [D'_AX . H |~ p]` MP_TAC THENL
   [MATCH_MP_TAC MODPROVES_INDUCT THEN REPEAT CONJ_TAC THENL 
    [MESON_TAC[MODPROVES_RULES];
     REWRITE_TAC[IN_ELIM_THM; D_AX; IN_UNION] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[D_SCHEMA_DEF; diam_DEF] THEN
      MATCH_MP_TAC MLK_imp_mp_subst THEN
      EXISTS_TAC `Box p'` THEN ASM_REWRITE_TAC[MLK_iff_refl_th] THEN
      EXISTS_TAC `Box Not p' --> False` THEN
      CONJ_TAC THENL [MESON_TAC[MLK_iff_sym; MLK_axiom_not]; ALL_TAC] THEN
      MATCH_MP_TAC MLK_imp_trans2 THEN
      EXISTS_TAC `Box False` THEN CONJ_TAC THENL 
      [MATCH_MP_TAC  D'_prove_K THEN
        MATCH_MP_TAC MODPROVES_MONO2 THEN EXISTS_TAC `{}:form->bool` THEN 
        CONJ_TAC THENL [HOLMS_TAC; ASM_MESON_TAC[EMPTY_SUBSET]];
       MATCH_MP_TAC MLK_iff_mp THEN EXISTS_TAC `Not Box False` THEN
           CONJ_TAC THENL
           [REWRITE_TAC[MLK_axiom_not];
            MESON_TAC[D'_AX_D'; MODPROVES_MONO2; EMPTY_SUBSET]]];
     MESON_TAC[MODPROVES_RULES];
     MESON_TAC[MODPROVES_RULES];
     MESON_TAC[MODPROVES_RULES]] THEN
     MESON_TAC[]; MESON_TAC[]];
   SUBGOAL_THEN `!H p. [D'_AX . H |~ p] ==> [D_AX . H |~ p]` MP_TAC THENL
   [MATCH_MP_TAC MODPROVES_INDUCT THEN REPEAT CONJ_TAC THENL 
     [MESON_TAC[MODPROVES_RULES];
      REWRITE_TAC[IN_ELIM_THM; D'_AX; IN_SING] THEN REPEAT STRIP_TAC THEN
       ASM_REWRITE_TAC[D_not_box_bot_SCHEMA_DEF; D_EQ_D_bot] THEN
       MATCH_MP_TAC MLK_iff_mp THEN
       EXISTS_TAC `Box False --> False` THEN
       CONJ_TAC THENL [MESON_TAC[MLK_iff_sym; MLK_axiom_not]; ALL_TAC] THEN
       MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `Diam False` THEN
       CONJ_TAC THENL
       [MESON_TAC[D_bot_AX_D_bot; MODPROVES_MONO2; EMPTY_SUBSET];
        MATCH_MP_TAC MLK_iff_mp THEN EXISTS_TAC `Not Diam False` THEN
         REWRITE_TAC[MLK_axiom_not; diam_DEF] THEN
         MATCH_MP_TAC MLK_DOUBLENEG THEN
         MATCH_MP_TAC MLK_necessitation THEN
         MATCH_MP_TAC MLK_iff_mp THEN EXISTS_TAC `False --> False` THEN
         MESON_TAC[MLK_axiom_not; MLK_iff_sym; MLK_imp_refl_th]]; 
      MESON_TAC[MODPROVES_RULES];
      MESON_TAC[MODPROVES_RULES];
      MESON_TAC[MODPROVES_RULES]];
    MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Serial frames.                                                            *)
(* ------------------------------------------------------------------------- *)

let SER_DEF = new_definition
  `SER =
   {(W:W->bool,R:W->W->bool) |
    (W,R) IN FRAME /\
    SERIAL W R}`;;

let IN_SER = prove
 (`(W:W->bool,R:W->W->bool) IN SER <=>
   (W,R) IN FRAME /\
    SERIAL W R`,
  REWRITE_TAC[SER_DEF; IN_ELIM_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory: Reflexive Frames are characteristic for D.         *)
(* ------------------------------------------------------------------------- *)

let SER_CHAR_D = prove 
  (`SER:(W->bool)#(W->W->bool)->bool = CHAR D_AX`,
    REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN
    REWRITE_TAC[IN_CHAR; IN_SER] THEN 
    REWRITE_TAC[D_AX; FORALL_IN_GSPEC; MODAL_SER; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. Serial Frames                                   *)
(* ------------------------------------------------------------------------- *)

let D_SER_VALID = prove
 (`!H p. [D_AX . H |~ p] /\
         (!q. q IN H ==> SER:(W->bool)#(W->W->bool)->bool |= q)
         ==> SER:(W->bool)#(W->W->bool)->bool |= p`,
  ASM_MESON_TAC[GEN_CHAR_VALID; SER_CHAR_D]);;

(* ------------------------------------------------------------------------- *)
(* Finite Serial Frames are appropriate for D.                               *)
(* ------------------------------------------------------------------------- *)

let SERF_DEF = new_definition
 `SERF =
  {(W:W->bool,R:W->W->bool) |
   (W,R) IN FINITE_FRAME /\
    SERIAL W R}`;;

let IN_SERF = prove
 (`(W:W->bool,R:W->W->bool) IN SERF <=>
   (W,R) IN FINITE_FRAME /\
    SERIAL W R`,
  REWRITE_TAC[SERF_DEF; IN_ELIM_PAIR_THM]);;

let SERF_SUBSET_SER = prove
 (`SERF:(W->bool)#(W->W->bool)->bool SUBSET SER`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_SERF; IN_FINITE_FRAME; 
              IN_SER; IN_FRAME] THEN 
  MESON_TAC[]);;

let SERF_FIN_SER = prove
 (`SERF:(W->bool)#(W->W->bool)->bool = (SER INTER FINITE_FRAME)`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN 
  REWRITE_TAC[IN_INTER; IN_SERF; IN_FINITE_FRAME;
              IN_SER; IN_FRAME] THEN
  MESON_TAC[FINITE_FRAME_SUBSET_FRAME; SUBSET]);;

let SERF_APPR_D = prove
  (`SERF: (W->bool)#(W->W->bool)->bool = APPR D_AX`,
   REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN
   REWRITE_TAC[APPR_CAR; SERF_FIN_SER] THEN
   REWRITE_TAC[SER_CHAR_D; IN_INTER; IN_CHAR; IN_FINITE_FRAME_INTER] THEN
   MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. SERF.                                           *)
(* ------------------------------------------------------------------------- *)

let D_SERF_VALID = prove
 (`!p. [D_AX . {} |~ p] ==> SERF:(W->bool)#(W->W->bool)->bool |= p`,
  MESON_TAC[GEN_APPR_VALID; SERF_APPR_D]);;

(* ------------------------------------------------------------------------- *)
(* Proof of Consistency of D.                                                *)
(* ------------------------------------------------------------------------- *)

let D_CONSISTENT = prove
 (`~ [D_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] D_SERF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM;
              IN_SERF; IN_FINITE_FRAME; SERIAL; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. x = 0 /\ x = y`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* D standard frames and models.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Standard Frame.                                                           *)
(* ------------------------------------------------------------------------- *)

let D_STANDARD_FRAME_DEF = new_definition
  `D_STANDARD_FRAME p = GEN_STANDARD_FRAME D_AX p`;;

let IN_D_STANDARD_FRAME = prove
  (`!p W R. (W,R) IN D_STANDARD_FRAME p <=>
            W = {w | MAXIMAL_CONSISTENT D_AX p w /\
                     (!q. MEM q w ==> q SUBSENTENCE p)} /\
            (W,R) IN SERF /\
            (!q w. Box q SUBFORMULA p /\ w IN W
                   ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`,
 REPEAT GEN_TAC THEN
 REWRITE_TAC[D_STANDARD_FRAME_DEF; IN_GEN_STANDARD_FRAME] THEN
 EQ_TAC THEN MESON_TAC[SERF_APPR_D]);;

(* ------------------------------------------------------------------------- *)
(* Standard model.                                                           *)
(* ------------------------------------------------------------------------- *)

let D_STANDARD_MODEL_DEF = new_definition
  `D_STANDARD_MODEL = GEN_STANDARD_MODEL D_AX`;;

let D_STANDARD_MODEL_CAR = prove
 (`!W R p V.
     D_STANDARD_MODEL p (W,R) V <=>
     (W,R) IN D_STANDARD_FRAME p /\
     (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[D_STANDARD_MODEL_DEF; GEN_STANDARD_MODEL_DEF] THEN
  REWRITE_TAC[IN_D_STANDARD_FRAME; IN_GEN_STANDARD_FRAME] THEN
  EQ_TAC THEN ASM_MESON_TAC[SERF_APPR_D]);;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let D_TRUTH_LEMMA = prove
 (`!W R p V q.
     ~ [D_AX . {} |~ p] /\
     D_STANDARD_MODEL p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REWRITE_TAC[D_STANDARD_MODEL_DEF] THEN MESON_TAC[GEN_TRUTH_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Accessibility lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let D_STANDARD_REL_DEF = new_definition
  `D_STANDARD_REL p w x <=>
   GEN_STANDARD_REL D_AX p w x`;;

let D_STANDARD_REL_CAR = prove
 (`!p w x.
     D_STANDARD_REL p w x <=>
     MAXIMAL_CONSISTENT D_AX p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT D_AX p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
     (!B. MEM (Box B) w ==> MEM B x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[D_STANDARD_REL_DEF; GEN_STANDARD_REL] THEN
  EQ_TAC THEN REPEAT (ASM_MESON_TAC[]) THEN REPEAT (ASM_MESON_TAC[]));;

let SERF_MAXIMAL_CONSISTENT = prove
 (`!p. ~ [D_AX . {} |~ p]
         ==> ({M | MAXIMAL_CONSISTENT D_AX p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
                   D_STANDARD_REL p) IN SERF `,
  INTRO_TAC "!p; p" THEN
  MP_TAC (ISPECL [`D_AX`; `p:form`] GEN_FINITE_FRAME_MAXIMAL_CONSISTENT) THEN
  REWRITE_TAC[IN_FINITE_FRAME] THEN INTRO_TAC "gen_max_cons" THEN
  ASM_REWRITE_TAC[IN_SERF; IN_FINITE_FRAME; SERIAL] THEN
  CONJ_TAC THENL
  (* Nonempty *)
  [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Well-defined *)
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[D_STANDARD_REL_DEF] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Finite *)
  ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Seriality *)
  REWRITE_TAC[IN_ELIM_THM; D_STANDARD_REL_CAR] THEN
  INTRO_TAC "!w; (max_cons) (imp)" THEN
  MP_TAC (SPECL [`D_AX:form->bool`; `p:form`; 
                 `(FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)`]
         EXTEND_MAXIMAL_CONSISTENT) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REFUTE_THEN MP_TAC THEN INTRO_TAC "non_cons" THEN
     HYP_TAC "non_cons" (REWRITE_RULE[CONSISTENT]) THEN
     HYP_TAC "non_cons" (ONCE_REWRITE_RULE[GSYM MLK_imp_clauses]) THEN
     REMOVE_THEN "non_cons" (LABEL_TAC "non_cons" o MATCH_MP MLK_imp_box) THEN
     REMOVE_THEN "max_cons" MP_TAC THEN 
     REWRITE_TAC[MAXIMAL_CONSISTENT; DE_MORGAN_THM] THEN
     DISJ1_TAC THEN MATCH_MP_TAC NOT_CONSISTENT_SUBLIST THEN
     EXISTS_TAC `FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w` THEN
     CONJ_TAC THENL
     [REWRITE_TAC[CONSISTENT] THEN
      ONCE_REWRITE_TAC[GSYM MLK_imp_clauses] THEN
       MATCH_MP_TAC MLK_iff_mp THEN
       EXISTS_TAC `CONJLIST 
                   (MAP (Box)
                        (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w))
                    --> False` THEN
       CONJ_TAC THENL
       [ASM_MESON_TAC[MLK_imp_subst; CONJLIST_FLATMAP_DOT_BOX_LEMMA_3; 
                      MLK_iff_sym; MLK_iff_refl_th; MLK_iff_mp_subst];
        MATCH_MP_TAC MLK_iff_mp THEN
        EXISTS_TAC `Box CONJLIST 
                     (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)
                    --> False` THEN
        CONJ_TAC THENL
        [MESON_TAC [MLK_imp_subst; MLK_iff_mp; CONJLIST_MAP_BOX; 
                    MLK_iff_sym; MLK_iff_refl_th];
         MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `Box False` THEN
          ASM_REWRITE_TAC[] THEN
          MESON_TAC[D_EQ_D'; GSYM MLK_imp_clauses; D'_AX_D'; 
                    MODPROVES_MONO2; EMPTY_SUBSET]]];
      MESON_TAC[SUBLIST; MEM_FLATMAP_LEMMA_2]]; 
    REWRITE_TAC[MEM_FLATMAP_LEMMA_A] THEN
     INTRO_TAC "!q; MEM_Boxq" THEN
     USE_THEN "imp" 
              (fun th -> LABEL_TAC "subs_Boxq" 
              (MATCH_MP (ISPEC `Box q` th) (ASSUME `MEM (Box q) w`))) THEN
     HYP_TAC "subs_Boxq" (REWRITE_RULE[SUBSENTENCE_CASES; form_DISTINCT]) THEN
     ASM_MESON_TAC[SUBSENTENCE_CASES; SUBFORMULA_TRANS; 
                   SUBFORMULA_CASES_L; IN_MINOR_CASES]];
   INTRO_TAC "@y. max_cons imp subl" THEN
    EXISTS_TAC `y:(form)list ` THEN
    ASM_REWRITE_TAC[] THEN INTRO_TAC "!B; MEM_BoxB" THEN
    HYP_TAC "subl" (REWRITE_RULE[SUBLIST; MEM]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC MEM_FLATMAP_LEMMA_1 THEN
    ASM_REWRITE_TAC[]]);;

let D_ACCESSIBILITY_LEMMA = prove
(`!p w q.
   ~ [D_AX . {} |~ p] /\
   MAXIMAL_CONSISTENT D_AX p w /\
   (!q. MEM q w ==> q SUBSENTENCE p) /\
   Box q SUBFORMULA p /\
   (!x. D_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`,
  INTRO_TAC "!p w q; p maxw subw boxq rrr" THEN REMOVE_THEN "rrr" MP_TAC THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN INTRO_TAC "asd" THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN
  REWRITE_TAC[MESON[]`~(p ==> q) <=> (p /\ ~q)`] THEN
  REWRITE_TAC[D_STANDARD_REL_DEF] THEN
  MP_TAC (ISPECL [`D_AX`;`p:form`;`w:form list`;`q:form`]
          GEN_XK_FOR_ACCESSIBILITY_LEMMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  INTRO_TAC "@X. maxX subX subl" THEN
  MP_TAC (ISPECL [`D_AX`;`p:form`;`w:form list`;`q:form`]
                 GEN_ACCESSIBILITY_LEMMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  INTRO_TAC "gsr_wX notqX" THEN EXISTS_TAC `X:form list` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Modal completeness theorem for D.                                        *)
(* ------------------------------------------------------------------------- *)

let SERF_IN_D_STANDARD_FRAME = prove
  (`!p. ~ [D_AX . {} |~ p] ==>
        ({M | MAXIMAL_CONSISTENT D_AX p M /\ 
              (!q. MEM q M ==> q SUBSENTENCE p)},
          D_STANDARD_REL p)
          IN D_STANDARD_FRAME p`,
    INTRO_TAC "!p; not_theor_p" THEN
    REWRITE_TAC[IN_D_STANDARD_FRAME] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SERF_MAXIMAL_CONSISTENT THEN ASM_REWRITE_TAC[]; 
     ASM_REWRITE_TAC[IN_ELIM_THM] THEN INTRO_TAC "!q w; boxq maxw subw" THEN
      EQ_TAC THENL
      [ASM_MESON_TAC[D_STANDARD_REL_CAR];
       ASM_MESON_TAC[D_ACCESSIBILITY_LEMMA]]]);;

let D_COUNTERMODEL = prove
 (`!M p.
     ~ [D_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT D_AX p M /\
     MEM (Not p) M /\
     (!q. MEM q M ==> q SUBSENTENCE p)
     ==> ~holds ({M | MAXIMAL_CONSISTENT D_AX p M /\
                      (!q. MEM q M ==> q SUBSENTENCE p)},
                 D_STANDARD_REL p)
                (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
                p M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC GEN_COUNTERMODEL THEN
  EXISTS_TAC `D_AX` THEN ASM_REWRITE_TAC[GEN_STANDARD_MODEL_DEF] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[SERF_IN_D_STANDARD_FRAME; D_STANDARD_FRAME_DEF]; 
   ALL_TAC] THEN
  ASM_MESON_TAC[IN_ELIM_THM]);;

let D_COMPLETENESS_THM = prove
  (`!p. SERF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [D_AX . {} |~ p]`,
    GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
    INTRO_TAC "p_not_theor" THEN
    REWRITE_TAC[valid; NOT_FORALL_THM] THEN
    EXISTS_TAC `({M | MAXIMAL_CONSISTENT D_AX p M /\
                     (!q. MEM q M ==> q SUBSENTENCE p)},
                 D_STANDARD_REL p)` THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
    [MATCH_MP_TAC SERF_MAXIMAL_CONSISTENT THEN ASM_REWRITE_TAC[];
     SUBGOAL_THEN `({M | MAXIMAL_CONSISTENT D_AX p M /\
                         (!q. MEM q M ==> q SUBSENTENCE p)},
                   D_STANDARD_REL p) IN GEN_STANDARD_FRAME D_AX p`
                  MP_TAC] THENL
     [ASM_MESON_TAC[SERF_IN_D_STANDARD_FRAME; D_STANDARD_FRAME_DEF];
      ASM_MESON_TAC[GEN_COUNTERMODEL_ALT]]);;

(* ------------------------------------------------------------------------- *)
(* Modal completeness for T for models on a generic (infinite) domain.       *)
(* ------------------------------------------------------------------------- *)

let D_COMPLETENESS_THM_GEN = prove
 (`!p. INFINITE (:A) /\ SERF:(A->bool)#(A->A->bool)->bool |= p
       ==> [D_AX . {} |~ p]`,
  SUBGOAL_THEN
    `INFINITE (:A)==>
      !p. SERF:(A->bool)#(A->A->bool)->bool |= p ==>
           SERF:(form list->bool)#(form list->form list->bool)->bool |= p`
    (fun th -> MESON_TAC[th; D_COMPLETENESS_THM]) THEN
  ASM_MESON_TAC [SERF_APPR_D; GEN_LEMMA_FOR_GEN_COMPLETENESS]);;

(* ------------------------------------------------------------------------- *)
(* Simple decision procedure for T.                                          *)
(* ------------------------------------------------------------------------- *)

let D_TAC : tactic =
  MATCH_MP_TAC D_COMPLETENESS_THM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in; holds; diam_DEF;
              IN_SERF; IN_FINITE_FRAME; SERIAL; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[];;

let D_RULE tm =
  prove(tm, REPEAT GEN_TAC THEN D_TAC);;

D_RULE `!p q r. [D_AX . {} |~ p && q && r --> p && r]`;;
D_RULE `!p q. [D_AX . {} |~ Box (p --> q) --> Box p --> Box q]`;;
D_RULE `!p q. [D_AX . {} |~  Box (p --> q) && Box p --> Box q]`;;
D_RULE `!p. [D_AX . {} |~  Box p --> Diam p]`;;

(* D_RULE `!p. [D_AX . {} |~  Box p --> p]`;;*)
(* D_RULE `!p. [D_AX . {} |~ Box p --> Box (Box p)]`;;*)
(* D_RULE `!p. [D_AX . {} |~ Box (Box p --> p) --> Box p]`;; *)  
(* D_RULE `[D_AX . {} |~ Box (Box False --> False) --> Box False]`;; *)

(* D_box_iff_th *)
D_RULE `!p q. [D_AX . {} |~ Box (p <-> q) --> (Box p <-> Box q)] `;;

(* ------------------------------------------------------------------------- *)
(* Countermodel using set of formulae (instead of lists of formulae).        *)
(* ------------------------------------------------------------------------- *)

let D_STDWORLDS_RULES,D_STDWORLDS_INDUCT,D_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT D_AX p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN D_STDWORLDS p`;;

let D_STDREL_RULES,D_STDREL_INDUCT,D_STDREL_CASES = new_inductive_definition
  `!w1 w2. D_STANDARD_REL p w1 w2
           ==> D_STDREL p (set_of_list w1) (set_of_list w2)`;;

let D_STDREL_IMP_D_STDWORLDS = prove
 (`!p w1 w2. D_STDREL p w1 w2
             ==> w1 IN D_STDWORLDS p /\
                 w2 IN D_STDWORLDS p`,
  GEN_TAC THEN MATCH_MP_TAC D_STDREL_INDUCT THEN
  REWRITE_TAC[D_STANDARD_REL_CAR] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC D_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;

let SET_OF_LIST_EQ_D_STANDARD_REL = prove
 (`!p u1 u2 w1 w2.
     set_of_list u1 = set_of_list w1 /\ NOREPETITION w1 /\
     set_of_list u2 = set_of_list w2 /\ NOREPETITION w2 /\
     D_STANDARD_REL p u1 u2
     ==> D_STANDARD_REL p w1 w2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[D_STANDARD_REL_CAR] THEN STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]; ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]);;



let BISIMIMULATION_SET_OF_LIST = prove
 (`!p. BISIMIMULATION
       (
         {M | MAXIMAL_CONSISTENT D_AX p M /\
              (!q. MEM q M ==> q SUBSENTENCE p)},
         D_STANDARD_REL p,
         (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
       )
       (D_STDWORLDS p,
        D_STDREL p,
        (\a w. Atom a SUBFORMULA p /\ Atom a IN w))
       (\w1 w2.
          MAXIMAL_CONSISTENT D_AX p w1 /\
          (!q. MEM q w1 ==> q SUBSENTENCE p) /\
          w2 IN D_STDWORLDS p /\
          set_of_list w1 = w2)`,
  GEN_TAC THEN REWRITE_TAC[BISIMIMULATION] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
  [GEN_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC[IN_SET_OF_LIST];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![u1]; w1u1" THEN EXISTS_TAC `set_of_list u1:form->bool` THEN
   HYP_TAC "w1u1 -> hp" (REWRITE_RULE[D_STANDARD_REL_CAR]) THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC D_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC D_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN MATCH_MP_TAC D_STDREL_RULES THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "![u2]; w2u2" THEN EXISTS_TAC `list_of_set u2:form list` THEN
  REWRITE_TAC[CONJ_ACI] THEN
  HYP_TAC "w2u2 -> @x2 y2. x2 y2 x2y2" (REWRITE_RULE[D_STDREL_CASES]) THEN
  REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  SIMP_TAC[SET_OF_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  SIMP_TAC[MEM_LIST_OF_SET; FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
  CONJ_TAC THENL
  [HYP_TAC "x2y2 -> hp" (REWRITE_RULE[D_STANDARD_REL_CAR]) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_D_STANDARD_REL THEN
   EXISTS_TAC `x2:form list` THEN EXISTS_TAC `y2:form list` THEN
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET;
            FINITE_SET_OF_LIST] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT]; ALL_TAC] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[D_STDREL_IMP_D_STDWORLDS]; ALL_TAC] THEN
  MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN
   EXISTS_TAC `y2:form list` THEN
   SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   ASM_MESON_TAC[D_STANDARD_REL_CAR]);;

let D_COUNTERMODEL_FINITE_SETS = prove
 (`!p. ~ [D_AX . {} |~ p] ==> ~holds_in (D_STDWORLDS p, D_STDREL p) p`,
  INTRO_TAC "!p; p" THEN
  DESTRUCT_TAC "@M. max mem subf"
    (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ [D_AX . {} |~ p]`)) THEN
  REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP] THEN
  ASSUM_LIST (LABEL_TAC "hp" o MATCH_MP D_COUNTERMODEL o
                end_itlist CONJ o rev) THEN
  EXISTS_TAC `\a w. Atom a SUBFORMULA p /\ Atom a IN w` THEN
  EXISTS_TAC `set_of_list M:form->bool` THEN CONJ_TAC THENL
  [MATCH_MP_TAC D_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "hp" MP_TAC THEN
  MATCH_MP_TAC (MESON[] `(p <=> q) ==> (~p ==> ~q)`) THEN
  MATCH_MP_TAC BISIMIMULATION_HOLDS THEN
  EXISTS_TAC `(\w1 w2. MAXIMAL_CONSISTENT D_AX p w1 /\
                       (!q. MEM q w1 ==> q SUBSENTENCE p) /\
                       w2 IN D_STDWORLDS p /\
                       set_of_list w1 = w2)` THEN
  ASM_REWRITE_TAC[BISIMIMULATION_SET_OF_LIST] THEN
  MATCH_MP_TAC D_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;
