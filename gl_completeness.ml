(* ========================================================================= *)
(* Proof of the consistency and modal completeness of GL.                    *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

let GL_AX = new_definition
  `GL_AX = {LOB_SCHEMA p | p IN (:form)}`;;

let LOB_IN_GL_AX = prove
 (`!q. (Box (Box q --> q) --> Box q) IN GL_AX`,
  REWRITE_TAC[GL_AX; LOB_SCHEMA_DEF; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]);;

let GL_axiom_lob = prove
 (`!q. [GL_AX. {} |~ (Box (Box q --> q) --> Box q)]`,
  MESON_TAC[MODPROVES_RULES; LOB_IN_GL_AX]);;

(* ------------------------------------------------------------------------- *)
(* Proposition for GL.                                                       *)
(* ------------------------------------------------------------------------- *)

let GL_schema_4 = prove
 (`!p. [GL_AX . {} |~ (Box p --> Box (Box p))]`,
  MESON_TAC[GL_axiom_lob; MLK_imp_box; MLK_and_pair_th; MLK_and_intro;
            MLK_shunt; MLK_imp_trans; MLK_and_right_th; MLK_and_left_th;
            MLK_box_and_th]);;

let GL_dot_box = prove
 (`!p. [GL_AX . {} |~ (Box p --> Box p && Box (Box p))]`,
  MESON_TAC[MLK_imp_refl_th; GL_schema_4; MLK_and_intro]);;

(* ------------------------------------------------------------------------- *)
(* Transitive Noetherian frames.                                             *)
(* ------------------------------------------------------------------------- *)

let TRANSNT_DEF = new_definition
  `TRANSNT =
   {(W:W->bool,R:W->W->bool) |
    (W,R) IN FRAME /\
    TRANSITIVE W R /\
    WF(\x y. R y x)}`;;

let IN_TRANSNT_DEF = prove
 (`(W:W->bool,R:W->W->bool) IN TRANSNT <=>
   (W,R) IN FRAME /\
    TRANSITIVE W R /\
   WF(\x y. R y x)`,
  REWRITE_TAC[TRANSNT_DEF; IN_ELIM_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory:                                                    *)
(* Transitive Noetherian frames are characteristic for GL.                   *)
(* ------------------------------------------------------------------------- *)

g `TRANSNT:(W->bool)#(W->W->bool)->bool = CHAR GL_AX`;;
e (REWRITE_TAC[EXTENSION; FORALL_PAIR_THM]);;
e (REWRITE_TAC[IN_CHAR; IN_TRANSNT_DEF]);;
e (REWRITE_TAC[GL_AX; FORALL_IN_UNION; FORALL_IN_GSPEC]);;
e (REPEAT GEN_TAC THEN EQ_TAC);;
 e DISCH_TAC;;
  e (CLAIM_TAC "Rel" `(!x:W y:W. p2 x y ==> x IN p1 /\ y IN p1)`);;
    e (ASM_MESON_TAC[IN_FRAME]);;
  e (ASM_MESON_TAC[MODAL_TRANSNT; IN_UNIV; LOB_SCHEMA_DEF]);;
 e DISCH_TAC;;
  e (CLAIM_TAC "Rel" `(!x:W y:W. p2 x y ==> x IN p1 /\ y IN p1)`);;
    e (ASM_MESON_TAC[IN_FRAME]);;
  e (ASM_MESON_TAC[MODAL_TRANSNT; IN_UNIV; LOB_SCHEMA_DEF]);;
let TRANSNT_CHAR_GL = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. transitive noetherian frames.                   *)
(* ------------------------------------------------------------------------- *)

let GL_TRANSNT_VALID = prove
(`!H p. [GL_AX . H |~ p] /\
        (!q. q IN H ==> TRANSNT:(W->bool)#(W->W->bool)->bool |= q)
        ==> TRANSNT:(W->bool)#(W->W->bool)->bool |= p`,
ASM_MESON_TAC[GEN_CHAR_VALID; TRANSNT_CHAR_GL]);;

g `!W:W->bool R:W->W->bool.
     ~(W= {}) /\
     (!x y. R x y ==> x IN W /\ y IN W) /\
     (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z) /\
     WF (\x y. R y x)
     ==> (!p. holds_in (W,R) (Box(Box p --> p) --> Box p))`;;
e (MP_TAC (ISPECL [`{}: form-> bool`; `(Box(Box p --> p) --> Box p)`]
                   GL_TRANSNT_VALID));;

g ` TRANSNT:(W->bool)#(W->W->bool)->bool |= (Box(Box p --> p) --> Box p)`;;
e (MATCH_MP_TAC GL_TRANSNT_VALID);;
e (EXISTS_TAC `{}: form-> bool`);;
e (ASM_REWRITE_TAC[ NOT_IN_EMPTY; GL_axiom_lob]);;
let LOB_THM_TRANSNT = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Irreflexive Transitive Frames.                                            *)
(* ------------------------------------------------------------------------- *)

let ITF_DEF = new_definition
  `ITF =
   {(W:W->bool,R:W->W->bool) |
    (W,R) IN FINITE_FRAME /\
    IRREFLEXIVE W R /\
    TRANSITIVE W R}`;;

let IN_ITF_DEF = prove
 (`(W:W->bool,R:W->W->bool) IN ITF <=>
   (W,R) IN FINITE_FRAME /\
    IRREFLEXIVE W R /\
    TRANSITIVE W R`,
  REWRITE_TAC[ITF_DEF; IN_ELIM_PAIR_THM]);;

g `ITF:(W->bool)#(W->W->bool)->bool SUBSET TRANSNT`;;
e (REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ITF_DEF; IN_TRANSNT_DEF;
               FINITE_FRAME_SUBSET_FRAME]);;
e (REPEAT STRIP_TAC);;
 e (ASM_MESON_TAC[IN_FRAME; IN_FINITE_FRAME]);;
 e (ASM_REWRITE_TAC[]);;
 e (ASM_REWRITE_TAC[IRREFLEXIVE] THEN MATCH_MP_TAC WF_FINITE);;
  e (CONJ_TAC THENL [ASM_MESON_TAC[IRREFLEXIVE; IN_FINITE_FRAME]; ALL_TAC]);;
  e (CONJ_TAC THENL [ASM_MESON_TAC[IN_FINITE_FRAME; TRANSITIVE]; ALL_TAC]);;
  e (GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `p1:W->bool`);;
   e CONJ_TAC;;
    e (ASM_MESON_TAC[IN_FINITE_FRAME]);;
    e (ASM SET_TAC[IN_FINITE_FRAME]);;
let ITF_SUBSET_TRANSNT = top_thm();;

let ITF_FIN_TRANSNT = prove
 (`ITF:(W->bool)#(W->W->bool)->bool = (TRANSNT INTER FINITE_FRAME)`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THENL
  [ASM_MESON_TAC[IN_INTER; ITF_SUBSET_TRANSNT; SUBSET; IN_ITF_DEF];
   ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_ITF_DEF; IN_FINITE_FRAME;
              TRANSITIVE; IN_TRANSNT_DEF; IN_FRAME] THEN
  INTRO_TAC "((non_empty Rel) Trans WF) non_empty' Rel' Finite" THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[WF_REFL; IRREFLEXIVE]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory: ITF frames are appropriate to GL.                  *)
(* ------------------------------------------------------------------------- *)

g `ITF: (W->bool)#(W->W->bool)->bool = APPR GL_AX`;;
e (REWRITE_TAC[EXTENSION; FORALL_PAIR_THM]);;
e (REWRITE_TAC[APPR_CAR; ITF_FIN_TRANSNT]);;
e (REWRITE_TAC[TRANSNT_CHAR_GL; IN_INTER; IN_CHAR; IN_FINITE_FRAME_INTER]);;
e (MESON_TAC[]);;
let ITF_APPR_GL = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. ITF                                             *)
(* ------------------------------------------------------------------------- *)

let GL_ITF_VALID = prove
 (`!p. [GL_AX . {} |~ p] ==> ITF:(W->bool)#(W->W->bool)->bool |= p`,
  ASM_MESON_TAC[GEN_APPR_VALID; ITF_APPR_GL]);;

(* ------------------------------------------------------------------------- *)
(* Proof of GL Consistency                                                   *)
(* ------------------------------------------------------------------------- *)

let GL_consistent = prove
 (`~ [GL_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] GL_ITF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM; IN_ITF_DEF;
              IN_FINITE_FRAME; TRANSITIVE; IRREFLEXIVE; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* GL standard frames and models.                                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Standard Frame.                                                           *)
(* ------------------------------------------------------------------------- *)

let GL_STANDARD_FRAME_DEF = new_definition
  `GL_STANDARD_FRAME p = GEN_STANDARD_FRAME GL_AX p`;;

let IN_GL_STANDARD_FRAME = prove
  (`!p W R. (W,R) IN GL_STANDARD_FRAME p <=>
            W = {w | MAXIMAL_CONSISTENT GL_AX p w /\
                     (!q. MEM q w ==> q SUBSENTENCE p)} /\
            (W,R) IN ITF /\
            (!q w. Box q SUBFORMULA p /\ w IN W
                   ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`,
 REPEAT GEN_TAC THEN
 REWRITE_TAC[GL_STANDARD_FRAME_DEF; IN_GEN_STANDARD_FRAME] THEN
 EQ_TAC THEN MESON_TAC[ITF_APPR_GL]);;

(* ------------------------------------------------------------------------- *)
(* Standard model.                                                           *)
(* ------------------------------------------------------------------------- *)

let GL_STANDARD_MODEL_DEF = new_definition
  `GL_STANDARD_MODEL = GEN_STANDARD_MODEL GL_AX`;;

let ITF_SUBSET_FRAME = prove
 (`ITF:(W->bool)#(W->W->bool)->bool SUBSET FRAME`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM] THEN INTRO_TAC "![W] [R]" THEN
  REWRITE_TAC[IN_ITF_DEF; IN_FINITE_FRAME; IRREFLEXIVE; TRANSITIVE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_FRAME]);;

let GL_STANDARD_MODEL_CAR = prove
 (`!W R p V.
     GL_STANDARD_MODEL p (W,R) V <=>
     (W,R) IN GL_STANDARD_FRAME p /\
     (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GL_STANDARD_MODEL_DEF; GEN_STANDARD_MODEL_DEF] THEN
  REWRITE_TAC[IN_GL_STANDARD_FRAME; IN_GEN_STANDARD_FRAME] THEN
  EQ_TAC THEN ASM_MESON_TAC[ITF_APPR_GL]);;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let GL_truth_lemma = prove
 (`!W R p V q.
     ~ [GL_AX . {} |~ p] /\
     GL_STANDARD_MODEL p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REWRITE_TAC[GL_STANDARD_MODEL_DEF] THEN MESON_TAC[GEN_TRUTH_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Accessibility lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let GL_STANDARD_REL_DEF = new_definition
  `GL_STANDARD_REL p w x <=>
   GEN_STANDARD_REL GL_AX p w x /\
   (!B. MEM (Box B) w ==> MEM (Box B) x) /\
   (?E. MEM (Box E) x /\ MEM (Not (Box E)) w)`;;

let GL_STANDARD_REL_CAR = prove
 (`!p w x.
     GL_STANDARD_REL p w x <=>
     MAXIMAL_CONSISTENT GL_AX p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT GL_AX p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
     (!B. MEM (Box B) w ==> MEM (Box B) x /\ MEM B x) /\
     (?E. MEM (Box E) x /\ MEM (Not (Box E)) w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GL_STANDARD_REL_DEF; GEN_STANDARD_REL] THEN
  EQ_TAC THEN REPEAT (ASM_MESON_TAC[]) THEN REPEAT (ASM_MESON_TAC[]));;

let ITF_MAXIMAL_CONSISTENT = prove
 (`!p. ~ [GL_AX . {} |~ p]
         ==> ({M | MAXIMAL_CONSISTENT GL_AX p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
                   GL_STANDARD_REL p) IN ITF `,
  INTRO_TAC "!p; p" THEN
  MP_TAC (ISPECL [`GL_AX`; `p:form`] GEN_FINITE_FRAME_MAXIMAL_CONSISTENT) THEN
  REWRITE_TAC[IN_FINITE_FRAME] THEN INTRO_TAC "gen_max_cons" THEN
  ASM_REWRITE_TAC[IN_ITF_DEF; IN_FINITE_FRAME; IRREFLEXIVE; TRANSITIVE] THEN
  CONJ_TAC THENL
  (* Nonempty *)
  [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Well-defined *)
  CONJ_TAC THENL [ASM_REWRITE_TAC[GL_STANDARD_REL_DEF] THEN
  ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Finite *)
  ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Irreflexive *)
  CONJ_TAC THENL
  [REWRITE_TAC[FORALL_IN_GSPEC; GL_STANDARD_REL_CAR] THEN
   INTRO_TAC "!M; M sub" THEN ASM_REWRITE_TAC[] THEN
   INTRO_TAC "_ (@E. E1 E2)" THEN
   SUBGOAL_THEN `~ CONSISTENT GL_AX M`
     (fun th -> ASM_MESON_TAC[th; MAXIMAL_CONSISTENT]) THEN
   MATCH_MP_TAC CONSISTENT_NC THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Transitive *)
  REWRITE_TAC[IN_ELIM_THM; GL_STANDARD_REL_CAR] THEN
  INTRO_TAC "!w w' w''; (x1 x2) (y1 y2) (z1 z2) +" THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let GL_ACCESSIBILITY_LEMMA =
  let GL_CONJLIST_FLATMAP_DOT_BOX_LEMMA = prove
   (`!w. [GL_AX . {} |~
            CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
            -->
            CONJLIST (MAP (Box)
              (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))]`,
   MATCH_MP_TAC CONJLIST_FLATMAP_DOT_BOX_LEMMA_2 THEN
   MATCH_ACCEPT_TAC GL_dot_box)
  and XK_SUBLIST_XGL = prove
   (`!q. CONS (Not q)
           (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)
         SUBLIST
         CONS (Not q) (CONS (Box q)
           (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))`,
  GEN_TAC THEN REWRITE_TAC[CONS_SUBLIST] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[MEM] ; ALL_TAC] THEN
  REWRITE_TAC[SUBLIST] THEN INTRO_TAC "!x; a" THEN
  SUBGOAL_THEN `MEM (Box x) w` MP_TAC THENL
  [MATCH_MP_TAC MEM_FLATMAP_LEMMA THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  INTRO_TAC "memw" THEN ASM_REWRITE_TAC[MEM] THEN DISJ2_TAC THEN DISJ2_TAC THEN
  ASM_REWRITE_TAC[MEM_FLATMAP] THEN  EXISTS_TAC `Box x:form` THEN
  ASM_REWRITE_TAC[MEM]) in
 prove
 (`!p w q.
     ~ [GL_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT GL_AX p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     Box q SUBFORMULA p /\
     (!x. GL_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`,
  INTRO_TAC "!p w q; p  maxw subw boxq rrr" THEN
  REFUTE_THEN (LABEL_TAC "contra") THEN
  REMOVE_THEN "rrr" MP_TAC THEN REWRITE_TAC[NOT_FORALL_THM] THEN
  CLAIM_TAC "consistent_X"
    `CONSISTENT GL_AX (CONS (Not q) (CONS (Box q)
       (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w)))` THENL
  [REMOVE_THEN "contra" MP_TAC THEN REWRITE_TAC[CONSISTENT; CONTRAPOS_THM] THEN
   INTRO_TAC "incons" THEN MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA THEN
   MAP_EVERY EXISTS_TAC [`GL_AX`; `p:form`;
     `FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w`] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MEM_FLATMAP_LEMMA_2] THEN MESON_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `Box(Box q --> q)` THEN
   REWRITE_TAC[GL_axiom_lob] THEN MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC
     `CONJLIST (MAP (Box)
        (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[GL_CONJLIST_FLATMAP_DOT_BOX_LEMMA]; ALL_TAC] THEN
   CLAIM_TAC "XIMP"
     `!x y l.
       [GL_AX . {} |~ Not (Not y && CONJLIST (CONS x l))]
        ==> [GL_AX . {} |~ (CONJLIST (MAP (Box) l)) --> Box(x --> y)]` THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MLK_imp_trans THEN
    EXISTS_TAC `Box (CONJLIST l)` THEN CONJ_TAC THENL
    [MESON_TAC[CONJLIST_MAP_BOX;MLK_iff_imp1]; ALL_TAC] THEN
    MATCH_MP_TAC MLK_imp_box THEN MATCH_MP_TAC MLK_shunt THEN
    ONCE_REWRITE_TAC[GSYM MLK_contrapos_eq] THEN
    MATCH_MP_TAC MLK_imp_trans THEN
    EXISTS_TAC `CONJLIST (CONS x l) --> False` THEN CONJ_TAC THENL
    [ASM_MESON_TAC[MLK_shunt; MLK_not_def];
     MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `Not (CONJLIST(CONS x l))` THEN
     CONJ_TAC THENL
     [MESON_TAC[MLK_axiom_not;MLK_iff_imp2];
      MESON_TAC[MLK_contrapos_eq;CONJLIST_CONS; MLK_and_comm_th;
                MLK_iff_imp2; MLK_iff_imp1; MLK_imp_trans]]];
    ALL_TAC] THEN
   POP_ASSUM MATCH_MP_TAC THEN
   HYP_TAC "incons" (REWRITE_RULE[CONSISTENT]) THEN
   HYP_TAC "incons" (ONCE_REWRITE_RULE[CONJLIST]) THEN
   HYP_TAC "incons" (REWRITE_RULE[NOT_CONS_NIL]) THEN
   POP_ASSUM MATCH_ACCEPT_TAC;
   ALL_TAC] THEN
  MP_TAC (SPECL
    [`GL_AX`; `p:form`;
     `CONS (Not q) (CONS (Box q)
        (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))`]
    EXTEND_MAXIMAL_CONSISTENT) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[MEM] THEN GEN_TAC THEN STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THENL
   [MATCH_MP_TAC SUBFORMULA_IMP_NEG_SUBSENTENCE THEN
    REWRITE_TAC[UNWIND_THM1] THEN HYP MESON_TAC "boxq"
      [SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    MATCH_MP_TAC SUBFORMULA_IMP_SUBSENTENCE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   POP_ASSUM (DESTRUCT_TAC "@y. +" o REWRITE_RULE[MEM_FLATMAP]) THEN
   STRUCT_CASES_TAC (SPEC `y:form` (cases "form")) THEN REWRITE_TAC[MEM] THEN
   STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THENL
   [MATCH_MP_TAC SUBFORMULA_IMP_SUBSENTENCE THEN
    CLAIM_TAC "rmk" `Box a SUBSENTENCE p` THENL
    [POP_ASSUM MP_TAC THEN HYP MESON_TAC "subw" []; ALL_TAC] THEN
    HYP_TAC "rmk" (REWRITE_RULE[SUBSENTENCE_CASES; distinctness "form"]) THEN
    TRANS_TAC SUBFORMULA_TRANS `Box a` THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    POP_ASSUM MP_TAC THEN HYP MESON_TAC "subw" []];
   ALL_TAC] THEN
  INTRO_TAC "@X. maxX subX subl" THEN EXISTS_TAC `X:form list` THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN
  MP_TAC (ISPECL [`GL_AX`; `p:form`;`w: form list`; `q:form`]
                 GEN_ACCESSIBILITY_LEMMA) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[GL_STANDARD_REL_DEF] THEN
   CLAIM_TAC "subl2"
     `CONS (Not q) (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)
      SUBLIST
      CONS (Not q) (CONS (Box q)
        (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))` THENL
   [ASM_MESON_TAC[XK_SUBLIST_XGL]; ALL_TAC] THEN
   ASM_MESON_TAC[SUBLIST_TRANS];
   ALL_TAC] THEN
  INTRO_TAC "gsr_wX notqX " THEN ASM_REWRITE_TAC[GL_STANDARD_REL_DEF] THEN
  CONJ_TAC THENL
  [INTRO_TAC "!B; B" THEN HYP_TAC "subl" (REWRITE_RULE[SUBLIST]) THEN
   REMOVE_THEN "subl" MATCH_MP_TAC THEN
   REWRITE_TAC[MEM; distinctness "form"; injectivity "form"] THENL
   [DISJ2_TAC THEN REWRITE_TAC[MEM_FLATMAP] THEN EXISTS_TAC `Box B` THEN
    ASM_REWRITE_TAC[MEM]];
    ALL_TAC] THEN
  EXISTS_TAC `q:form` THEN HYP_TAC "subl" (REWRITE_RULE[SUBLIST]) THEN
  CONJ_TAC THENL
  [REMOVE_THEN "subl" MATCH_MP_TAC THEN REWRITE_TAC[MEM]; ALL_TAC] THEN
  ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT]);;

(* ------------------------------------------------------------------------- *)
(* Modal completeness theorem for GL.                                        *)
(* ------------------------------------------------------------------------- *)

g `!p. ~ [GL_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT GL_AX p M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)},
            GL_STANDARD_REL p) IN GL_STANDARD_FRAME p`;;
e (INTRO_TAC "!p; not_theor_p");;
e (REWRITE_TAC[IN_GL_STANDARD_FRAME]);;
e CONJ_TAC;;
e (MATCH_MP_TAC ITF_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (INTRO_TAC "!q w; subform max_cons_w implies_w");;
e EQ_TAC;;
 e (ASM_MESON_TAC[GL_STANDARD_REL_CAR]);;
 e (ASM_MESON_TAC[GL_ACCESSIBILITY_LEMMA]);;
let GLF_IN_GL_STANDARD_FRAME = top_thm();;

let GL_COUNTERMODEL = prove
 (`!M p.
     ~ [GL_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT GL_AX p M /\
     MEM (Not p) M /\
     (!q. MEM q M ==> q SUBSENTENCE p)
     ==>
     ~holds
        ({M | MAXIMAL_CONSISTENT GL_AX p M /\
              (!q. MEM q M ==> q SUBSENTENCE p)},
         GL_STANDARD_REL p)
        (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
        p M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC GEN_COUNTERMODEL THEN
  EXISTS_TAC `GL_AX` THEN ASM_REWRITE_TAC[GEN_STANDARD_MODEL_DEF] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[GLF_IN_GL_STANDARD_FRAME; GL_STANDARD_FRAME_DEF];
   ALL_TAC] THEN
  ASM_MESON_TAC[IN_ELIM_THM]);;

g `!p. ITF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [GL_AX . {} |~ p]`;;
e (GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM]);;
e (INTRO_TAC "p_not_theor");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC
     `({M | MAXIMAL_CONSISTENT GL_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
       GL_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC);;
e (MATCH_MP_TAC ITF_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN
     `({M | MAXIMAL_CONSISTENT GL_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
       GL_STANDARD_REL p)
      IN GEN_STANDARD_FRAME GL_AX p`
     MP_TAC);;
e (ASM_MESON_TAC[GLF_IN_GL_STANDARD_FRAME; GL_STANDARD_FRAME_DEF]);;
e (ASM_MESON_TAC[GEN_COUNTERMODEL_ALT]);;
let GL_COMPLETENESS_THM = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* Modal completeness for GL for models on a generic (infinite) domain.      *)
(* ------------------------------------------------------------------------- *)

let GL_COMPLETENESS_THM_GEN = prove
 (`!p. INFINITE (:A) /\ ITF:(A->bool)#(A->A->bool)->bool |= p
       ==> [GL_AX . {} |~ p]`,
  SUBGOAL_THEN
    `INFINITE (:A)
     ==> !p. ITF:(A->bool)#(A->A->bool)->bool |= p
             ==> ITF:(form list->bool)#(form list->form list->bool)->bool |= p`
    (fun th -> MESON_TAC[th; GL_COMPLETENESS_THM]) THEN
  ASM_MESON_TAC[ITF_APPR_GL; GEN_LEMMA_FOR_GEN_COMPLETENESS]);;

(* ------------------------------------------------------------------------- *)
(* Simple decision procedure for GL.                                         *)
(* ------------------------------------------------------------------------- *)

let GL_TAC : tactic =
  MATCH_MP_TAC GL_COMPLETENESS_THM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in; holds; IN_ITF_DEF;
              IN_FINITE_FRAME; IRREFLEXIVE; TRANSITIVE;
              GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[];;

let GL_RULE tm =
  prove(tm, REPEAT GEN_TAC THEN GL_TAC);;

GL_RULE `!p q r. [GL_AX . {} |~ p && q && r --> p && r]`;;
GL_RULE `!p. [GL_AX . {} |~ Box p --> Box (Box p)]`;;
GL_RULE `!p q. [GL_AX . {} |~  Box (p --> q) && Box p --> Box q]`;;
(* GL_RULE `!p. [GL_AX . {} |~ Box (Box p --> p) --> Box p]`;; *)
(* GL_RULE `[GL_AX . {} |~ Box (Box False --> False) --> Box False]`;; *)

(* GL_box_iff_th *)
GL_RULE `!p q. [GL_AX . {} |~ Box (p <-> q) --> (Box p <-> Box q)] `;;

(* ------------------------------------------------------------------------- *)
(* Countermodel using set of formulae (instead of lists of formulae).        *)
(* ------------------------------------------------------------------------- *)

let GL_STDWORLDS_RULES,GL_STDWORLDS_INDUCT,GL_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT GL_AX p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN GL_STDWORLDS p`;;

let GL_STDREL_RULES,GL_STDREL_INDUCT,GL_STDREL_CASES = new_inductive_definition
  `!w1 w2. GL_STANDARD_REL p w1 w2
           ==> GL_STDREL p (set_of_list w1) (set_of_list w2)`;;

let GL_STDREL_IMP_GL_STDWORLDS = prove
 (`!p w1 w2. GL_STDREL p w1 w2 ==>
             w1 IN GL_STDWORLDS p /\
             w2 IN GL_STDWORLDS p`,
  GEN_TAC THEN MATCH_MP_TAC GL_STDREL_INDUCT THEN
  REWRITE_TAC[GL_STANDARD_REL_CAR] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC GL_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;

let SET_OF_LIST_EQ_GL_STANDARD_REL = prove
 (`!p u1 u2 w1 w2.
     set_of_list u1 = set_of_list w1 /\ NOREPETITION w1 /\
     set_of_list u2 = set_of_list w2 /\ NOREPETITION w2 /\
     GL_STANDARD_REL p u1 u2
     ==> GL_STANDARD_REL p w1 w2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GL_STANDARD_REL_CAR] THEN
  STRIP_TAC THEN
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
         {M | MAXIMAL_CONSISTENT GL_AX p M /\
              (!q. MEM q M ==> q SUBSENTENCE p)},
         GL_STANDARD_REL p,
         (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
       )
       (GL_STDWORLDS p,
        GL_STDREL p,
        (\a w. Atom a SUBFORMULA p /\ Atom a IN w))
       (\w1 w2.
          MAXIMAL_CONSISTENT GL_AX p w1 /\
          (!q. MEM q w1 ==> q SUBSENTENCE p) /\
          w2 IN GL_STDWORLDS p /\
          set_of_list w1 = w2)`,
  GEN_TAC THEN REWRITE_TAC[BISIMIMULATION] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
  [GEN_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC[IN_SET_OF_LIST];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![u1]; w1u1" THEN EXISTS_TAC `set_of_list u1:form->bool` THEN
   HYP_TAC "w1u1 -> hp" (REWRITE_RULE[GL_STANDARD_REL_CAR]) THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GL_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC GL_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN MATCH_MP_TAC GL_STDREL_RULES THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "![u2]; w2u2" THEN EXISTS_TAC `list_of_set u2:form list` THEN
  REWRITE_TAC[CONJ_ACI] THEN
  HYP_TAC "w2u2 -> @x2 y2. x2 y2 x2y2" (REWRITE_RULE[GL_STDREL_CASES]) THEN
  REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  SIMP_TAC[SET_OF_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  SIMP_TAC[MEM_LIST_OF_SET; FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
  CONJ_TAC THENL
  [HYP_TAC "x2y2 -> hp" (REWRITE_RULE[GL_STANDARD_REL_CAR]) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_GL_STANDARD_REL THEN
   EXISTS_TAC `x2:form list` THEN EXISTS_TAC `y2:form list` THEN
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET;
            FINITE_SET_OF_LIST] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[GL_STDREL_IMP_GL_STDWORLDS]; ALL_TAC] THEN
  MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN
  EXISTS_TAC `y2:form list` THEN
  SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  ASM_MESON_TAC[GL_STANDARD_REL_CAR]);;

let GL_COUNTERMODEL_FINITE_SETS = prove
 (`!p. ~ [GL_AX . {} |~ p] ==> ~holds_in (GL_STDWORLDS p, GL_STDREL p) p`,
  INTRO_TAC "!p; p" THEN
  DESTRUCT_TAC "@M. max mem subf"
    (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ [GL_AX . {} |~ p]`)) THEN
  REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP] THEN
  ASSUM_LIST (LABEL_TAC "hp" o MATCH_MP GL_COUNTERMODEL o
                end_itlist CONJ o rev) THEN
  EXISTS_TAC `\a w. Atom a SUBFORMULA p /\ Atom a IN w` THEN
  EXISTS_TAC `set_of_list M:form->bool` THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "hp" MP_TAC THEN
  MATCH_MP_TAC (MESON[] `(p <=> q) ==> (~p ==> ~q)`) THEN
  MATCH_MP_TAC BISIMIMULATION_HOLDS THEN
  EXISTS_TAC
      `(\w1 w2.
          MAXIMAL_CONSISTENT GL_AX p w1 /\
          (!q. MEM q w1 ==> q SUBSENTENCE p) /\
          w2 IN GL_STDWORLDS p /\
          set_of_list w1 = w2)` THEN
  ASM_REWRITE_TAC[BISIMIMULATION_SET_OF_LIST] THEN
  MATCH_MP_TAC GL_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;
