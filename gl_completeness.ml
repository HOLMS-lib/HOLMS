(* ========================================================================= *)
(* Proof of the consistency and modal completeness of GL.                    *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* ========================================================================= *)

let GL_AX = new_definition
  `GL_AX = {Box (Box p --> p) --> Box p | p IN (:form)}`;;

let LOB_IN_GL_AX = prove
 (`!q. (Box (Box q --> q) --> Box q) IN GL_AX`,
  REWRITE_TAC[GL_AX; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]);;

let GL_axiom_lob = prove
 (`!q. [GL_AX. {} |~ (Box (Box q --> q) --> Box q)]`,
  MESON_TAC[MODPROVES_RULES; LOB_IN_GL_AX]);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. transitive noetherian frames.                   *)
(* ------------------------------------------------------------------------- *)

let LOB_IMP_TRANSNT = prove
 (`!W R. (!x y:W. R x y ==> x IN W /\ y IN W) /\
         (!p. holds_in (W,R) (Box (Box p --> p) --> Box p))
         ==> (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z
                      ==> R x z) /\
             WF (\x y. R y x)`,
  MODAL_SCHEMA_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
  [X_GEN_TAC `w:W` THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`\v:W. v IN W /\ R w v /\ !w''. w'' IN W /\ R v w'' ==> R w w''`;
      `w:W`]) THEN
   MESON_TAC[];
   REWRITE_TAC[WF_IND] THEN X_GEN_TAC `P:W->bool` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `\x:W. !w:W. x IN W /\ R w x ==> P x`) THEN
   MATCH_MP_TAC MONO_FORALL THEN ASM_MESON_TAC[]]);;

let TRANSNT_IMP_LOB = prove
 (`!W R. (!x y:W. R x y ==> x IN W /\ y IN W) /\
         (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z) /\
         WF (\x y. R y x)
         ==> (!p. holds_in (W,R) (Box(Box p --> p) --> Box p))`,
  MODAL_SCHEMA_TAC THEN REWRITE_TAC[WF_IND] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

let TRANSNT_EQ_LOB = prove
 (`!W R. (!x y:W. R x y ==> x IN W /\ y IN W)
         ==> ((!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z
                       ==> R x z) /\
              WF (\x y. R y x) <=>
              (!p. holds_in (W,R) (Box(Box p --> p) --> Box p)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [MATCH_MP_TAC TRANSNT_IMP_LOB THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC LOB_IMP_TRANSNT THEN ASM_REWRITE_TAC[]]);;

let KAXIOM_TRANSNT_VALID = prove
 (`!p. KAXIOM p ==> TRANSNT:(W->bool)#(W->W->bool)->bool |= p`,
  MATCH_MP_TAC KAXIOM_INDUCT THEN REWRITE_TAC[valid] THEN FIX_TAC "f" THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  SPEC_TAC (`f:(W->bool)#(W->W->bool)`,`f:(W->bool)#(W->W->bool)`) THEN
  MATCH_MP_TAC (MESON[PAIR_SURJECTIVE]
    `(!W:W->bool R:W->W->bool. P (W,R)) ==> (!f. P f)`) THEN
  REWRITE_TAC[TRANSNT] THEN REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  MODAL_TAC);;

let GL_AX_TRANSNT_VALID = prove
 (`!p. p IN GL_AX ==> TRANSNT:(W->bool)#(W->W->bool)->bool |= p`,
  REWRITE_TAC[GL_AX; FORALL_IN_GSPEC; valid; IN_UNIV] THEN FIX_TAC "f" THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  SPEC_TAC (`f:(W->bool)#(W->W->bool)`,`f:(W->bool)#(W->W->bool)`) THEN
  MATCH_MP_TAC (MESON[PAIR_SURJECTIVE]
    `(!W:W->bool R:W->W->bool. P (W,R)) ==> (!f. P f)`) THEN
  REWRITE_TAC[TRANSNT] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN MATCH_MP_TAC TRANSNT_IMP_LOB THEN ASM_REWRITE_TAC[]);;

let GL_TRANSNT_VALID = prove
 (`!H p. [GL_AX . H |~ p] /\
         (!q. q IN H ==> TRANSNT:(W->bool)#(W->W->bool)->bool |= q)
         ==> TRANSNT:(W->bool)#(W->W->bool)->bool |= p`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC MODPROVES_INDUCT THEN
  CONJ_TAC THENL [SIMP_TAC[KAXIOM_TRANSNT_VALID]; ALL_TAC] THEN
  CONJ_TAC THENL [SIMP_TAC[GL_AX_TRANSNT_VALID]; ALL_TAC] THEN
  CONJ_TAC THENL [MESON_TAC[KAXIOM_TRANSNT_VALID]; ALL_TAC] THEN
  CONJ_TAC THENL [MODAL_TAC; ALL_TAC] THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN MODAL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. ITF                                             *)
(* ------------------------------------------------------------------------- *)

let ITF = new_definition
  `ITF (W:W->bool,R:W->W->bool) <=>
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W /\
   (!x. x IN W ==> ~R x x) /\
   (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)`;;

let ITF_NT = prove
 (`!W R:W->W->bool. ITF(W,R) ==> TRANSNT(W,R)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ITF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[TRANSNT] THEN MATCH_MP_TAC WF_FINITE THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `W:W->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let GL_ITF_VALID = prove
 (`!p. [GL_AX . {} |~ p] ==> ITF:(W->bool)#(W->W->bool)->bool |= p`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `TRANSNT:(W->bool)#(W->W->bool)->bool |= p` MP_TAC THENL
  [MATCH_MP_TAC GL_TRANSNT_VALID THEN ASM_MESON_TAC[NOT_IN_EMPTY];
   REWRITE_TAC[valid; FORALL_PAIR_THM] THEN MESON_TAC[ITF_NT]]);;

let GL_consistent = prove
 (`~ [GL_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] GL_ITF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM;
              ITF; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Proposition for GL.                                                       *)
(* ------------------------------------------------------------------------- *)

let GL_schema_4 = prove
 (`!p. [GL_AX . {} |~ (Box p --> Box (Box p))]`,
  MESON_TAC[GL_axiom_lob; MLK_imp_box; MLK_and_pair_th; MLK_and_intro;
    MLK_shunt; MLK_imp_trans;MLK_and_right_th;MLK_and_left_th;MLK_box_and_th]);;

let GL_dot_box = prove
 (`!p. [GL_AX . {} |~ (Box p --> Box p && Box (Box p))]`,
  MESON_TAC[MLK_imp_refl_th; GL_schema_4; MLK_and_intro]);;

(* ------------------------------------------------------------------------- *)
(* GL standard frames and models.                                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Standard Frame.                                                           *)
(* ------------------------------------------------------------------------- *)

let GL_STANDARD_FRAME = new_definition
  `GL_STANDARD_FRAME p (W,R) <=>
   GEN_STANDARD_FRAME ITF GL_AX p (W,R)`;;

let GL_STANDARD_FRAME_CAR = prove
 (`!p W R. GL_STANDARD_FRAME p (W,R) <=>
           W = {w | MAXIMAL_CONSISTENT GL_AX p w /\
                    (!q. MEM q w ==> q SUBSENTENCE p)} /\
           ITF (W,R) /\
           (!q w. Box q SUBFORMULA p /\ w IN W
                  ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GL_STANDARD_FRAME; GEN_STANDARD_FRAME; ITF; FRAME] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Standard model.                                                           *)
(* ------------------------------------------------------------------------- *)

let GL_STANDARD_MODEL = new_definition
   `GL_STANDARD_MODEL p (W,R) V <=>
    GEN_STANDARD_MODEL ITF GL_AX p (W,R) V`;;

let GL_STANDARD_MODEL_CAR = prove
 (`!W R p V. GL_STANDARD_MODEL p (W,R) V <=>
   GL_STANDARD_FRAME p (W,R) /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p)) `,
  REWRITE_TAC[GL_STANDARD_MODEL; GEN_STANDARD_MODEL;
              GEN_STANDARD_FRAME; GL_STANDARD_FRAME]);;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let GL_truth_lemma = prove
 (`!W R p V q.
     ~ [GL_AX . {} |~ p] /\
     GL_STANDARD_MODEL p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REWRITE_TAC[GL_STANDARD_MODEL] THEN MESON_TAC[GEN_TRUTH_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Accessibility lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let GL_STANDARD_REL = new_definition
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
  REPEAT GEN_TAC THEN REWRITE_TAC[GL_STANDARD_REL; GEN_STANDARD_REL] THEN
  EQ_TAC THEN REPEAT (ASM_MESON_TAC[]) THEN REPEAT (ASM_MESON_TAC[]));;

let ITF_MAXIMAL_CONSISTENT = prove
 (`!S p. ~ [GL_AX . {} |~ p ]
         ==> ITF ({M | MAXIMAL_CONSISTENT GL_AX p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
                  GL_STANDARD_REL p)`,
  INTRO_TAC "!S p; p" THEN REWRITE_TAC[ITF] THEN
  (* Nonempty *)
  CONJ_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   ASM_MESON_TAC[NONEMPTY_MAXIMAL_CONSISTENT];
   ALL_TAC] THEN
  (* Well-defined *)
  CONJ_TAC THENL
  [REWRITE_TAC[GL_STANDARD_REL_CAR; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  (* Finite *)
  CONJ_TAC THENL
  [MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC
     `{l | NOREPETITION l /\
           !q. MEM q l ==> q IN {q | q SUBSENTENCE p}}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_NOREPETITION THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    SUBGOAL_THEN
      `{q | q SUBSENTENCE p} =
       {q | q SUBFORMULA p} UNION IMAGE (Not) {q | q SUBFORMULA p}`
      SUBST1_TAC THENL
    [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_UNION;
                 FORALL_IN_GSPEC; FORALL_IN_IMAGE] THEN
     REWRITE_TAC[IN_UNION; IN_ELIM_THM; SUBSENTENCE_RULES] THEN
     GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [SUBSENTENCE_CASES] THEN
     DISCH_THEN STRUCT_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
     ASM SET_TAC [];
     ALL_TAC] THEN
    REWRITE_TAC[FINITE_UNION; FINITE_SUBFORMULA] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_SUBFORMULA];
    ALL_TAC] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM; MAXIMAL_CONSISTENT] THEN
   GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
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
  INTRO_TAC "!x y z; (x1 x2) (y1 y2) (z1 z2) +" THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let ACCESSIBILITY_LEMMA =
  let MEM_FLATMAP_LEMMA = prove
   (`!p l. MEM p (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) l) <=>
           (?q. p = Box q /\ MEM p l)`,
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; FLATMAP] THEN
    REWRITE_TAC[MEM_APPEND] THEN ASM_CASES_TAC `?c. h = Box c` THENL
    [POP_ASSUM (CHOOSE_THEN SUBST_VAR_TAC) THEN ASM_REWRITE_TAC[MEM] THEN
     MESON_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `~ MEM p (match h with Box c -> [Box c] | _ -> [])`
      (fun th -> ASM_REWRITE_TAC[th]) THENL
    [POP_ASSUM MP_TAC THEN STRUCT_CASES_TAC (SPEC `h:form` (cases "form")) THEN
     REWRITE_TAC[MEM; distinctness "form"; injectivity "form"] THEN
     MESON_TAC[];
     ALL_TAC] THEN
    POP_ASSUM (fun th -> MESON_TAC[th]))
  and CONJLIST_FLATMAP_DOT_BOX_LEMMA = prove
   (`!w. [GL_AX . {} |~
            CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
            -->
            CONJLIST (MAP (Box)
              (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))]`,
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC[FLATMAP; MAP; MLK_imp_refl_th]; ALL_TAC] THEN
    REWRITE_TAC[FLATMAP; MAP_APPEND] THEN MATCH_MP_TAC MLK_imp_trans THEN
    EXISTS_TAC
      `CONJLIST (match h with Box c -> [Box c] | _ -> []) &&
       CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) t)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC MLK_iff_imp1 THEN MATCH_ACCEPT_TAC CONJLIST_APPEND;
     ALL_TAC] THEN
    MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC
      `CONJLIST (MAP (Box) (match h with Box c -> [c; Box c] | _ -> [])) &&
       CONJLIST (MAP (Box)
         (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) t))` THEN
    CONJ_TAC THENL
    [ALL_TAC;
     MATCH_MP_TAC MLK_iff_imp2 THEN MATCH_ACCEPT_TAC CONJLIST_APPEND] THEN
    MATCH_MP_TAC MLK_and_intro THEN CONJ_TAC THENL
    [ALL_TAC; ASM_MESON_TAC[MLK_imp_trans; MLK_and_right_th]] THEN
    MATCH_MP_TAC MLK_imp_trans THEN
    EXISTS_TAC `CONJLIST (match h with Box c -> [Box c] | _ -> [])` THEN
    CONJ_TAC THENL [MATCH_ACCEPT_TAC MLK_and_left_th; ALL_TAC] THEN
    POP_ASSUM (K ALL_TAC) THEN
    STRUCT_CASES_TAC (SPEC `h:form` (cases "form")) THEN
    REWRITE_TAC[distinctness "form"; MAP; MLK_imp_refl_th] THEN
    REWRITE_TAC[CONJLIST; NOT_CONS_NIL] THEN MATCH_ACCEPT_TAC GL_dot_box) in
 prove
 (`!p M w q.
     ~ [GL_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT GL_AX p M /\
     (!q. MEM q M ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT GL_AX p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     MEM (Not p) M /\
     Box q SUBFORMULA p /\
     (!x. GL_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`,
  REPEAT GEN_TAC THEN INTRO_TAC "p maxM subM maxw subw notp boxq rrr" THEN
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
   [GEN_TAC THEN REWRITE_TAC[MEM_FLATMAP_LEMMA] THEN MESON_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `Box(Box q --> q)` THEN
   REWRITE_TAC[GL_axiom_lob] THEN MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC
     `CONJLIST (MAP (Box)
        (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[CONJLIST_FLATMAP_DOT_BOX_LEMMA]; ALL_TAC] THEN
   CLAIM_TAC "XIMP"
     `!x y l.
       [GL_AX . {} |~ Not (Not y && CONJLIST (CONS x l))]
        ==> [GL_AX . {} |~ (CONJLIST (MAP (Box) l)) --> Box(x --> y)]` THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MLK_imp_trans THEN
    EXISTS_TAC `Box (CONJLIST l)` THEN CONJ_TAC THENL
    [MESON_TAC[CONJLIST_MAP_BOX;MLK_iff_imp1]; ALL_TAC] THEN
    MATCH_MP_TAC MLK_imp_box THEN MATCH_MP_TAC MLK_shunt THEN
    ONCE_REWRITE_TAC[GSYM MLK_contrapos_eq] THEN MATCH_MP_TAC MLK_imp_trans THEN
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
  ASM_REWRITE_TAC[GL_STANDARD_REL_CAR; NOT_IMP] THEN CONJ_TAC THENL
  [CONJ_TAC THENL
   [INTRO_TAC "!B; B" THEN HYP_TAC "subl" (REWRITE_RULE[SUBLIST]) THEN
    CONJ_TAC THEN REMOVE_THEN "subl" MATCH_MP_TAC THEN
    REWRITE_TAC[MEM; distinctness "form"; injectivity "form"] THENL
    [DISJ2_TAC THEN REWRITE_TAC[MEM_FLATMAP] THEN EXISTS_TAC `Box B` THEN
     ASM_REWRITE_TAC[MEM];
     DISJ2_TAC THEN DISJ2_TAC THEN REWRITE_TAC[MEM_FLATMAP] THEN
     EXISTS_TAC `Box B` THEN ASM_REWRITE_TAC[MEM]];
    ALL_TAC] THEN
   EXISTS_TAC `q:form` THEN HYP_TAC "subl" (REWRITE_RULE[SUBLIST]) THEN
   CONJ_TAC THENL
   [REMOVE_THEN "subl" MATCH_MP_TAC THEN REWRITE_TAC[MEM]; ALL_TAC] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT];
   ALL_TAC] THEN
  HYP_TAC "subl: +" (SPEC `Not q` o REWRITE_RULE[SUBLIST]) THEN
  REWRITE_TAC[MEM] THEN
  IMP_REWRITE_TAC[GSYM MAXIMAL_CONSISTENT_MEM_NOT] THEN
  SIMP_TAC[] THEN INTRO_TAC "_" THEN MATCH_MP_TAC SUBFORMULA_TRANS THEN
  EXISTS_TAC `Box q` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]) ;;

(* ------------------------------------------------------------------------- *)
(* Modal completeness theorem for GL.                                        *)
(* ------------------------------------------------------------------------- *)

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
  MP_TAC (ISPECL
    [`{M | MAXIMAL_CONSISTENT GL_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)}`;
     `GL_STANDARD_REL p`;
     `p:form`;
     `\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w`;
     `p:form`] GL_truth_lemma) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[SUBFORMULA_REFL; GL_STANDARD_MODEL_CAR;
  GL_STANDARD_FRAME_CAR; GEN_STANDARD_MODEL] THEN
   ASM_SIMP_TAC[ITF_MAXIMAL_CONSISTENT] THEN REWRITE_TAC[IN_ELIM_THM] THEN
   CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
   INTRO_TAC "!q w; boxq w subf" THEN EQ_TAC THENL
   [ASM_REWRITE_TAC[GL_STANDARD_REL_CAR] THEN SIMP_TAC[]; ALL_TAC] THEN
    INTRO_TAC "hp" THEN MATCH_MP_TAC ACCESSIBILITY_LEMMA THEN
    MAP_EVERY EXISTS_TAC [`p:form`; `M:form list`] THEN
    ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPEC `M:form list`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  DISCH_THEN (SUBST1_TAC o GSYM) THEN
  ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT_NC]);;

let GL_COUNTERMODEL_ALT = prove
 (`!p. ~ [GL_AX . {} |~ p]
       ==>
       ~holds_in
          ({M | MAXIMAL_CONSISTENT GL_AX p M /\
                (!q. MEM q M ==> q SUBSENTENCE p)},
           GL_STANDARD_REL p)
          p`,
  INTRO_TAC "!p; p" THEN
  REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP; IN_ELIM_THM] THEN
  EXISTS_TAC `\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w` THEN
  DESTRUCT_TAC "@M. max mem subf"
    (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ [GL_AX . {} |~ p]`)) THEN
  EXISTS_TAC `M:form list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GL_COUNTERMODEL THEN ASM_REWRITE_TAC[]);;

let COMPLETENESS_THEOREM = prove
 (`!p. ITF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [GL_AX . {} |~ p]`,
  GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  INTRO_TAC "p" THEN REWRITE_TAC[valid; NOT_FORALL_THM] THEN
  EXISTS_TAC `({M | MAXIMAL_CONSISTENT GL_AX p M /\
                    (!q. MEM q M ==> q SUBSENTENCE p)},
               GL_STANDARD_REL p)` THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
  [MATCH_MP_TAC ITF_MAXIMAL_CONSISTENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC GL_COUNTERMODEL_ALT THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Modal completeness for GL for models on a generic (infinite) domain.      *)
(* ------------------------------------------------------------------------- *)

let COMPLETENESS_THEOREM_GEN = prove
 (`!p. INFINITE (:A) /\ ITF:(A->bool)#(A->A->bool)->bool |= p
       ==> [GL_AX . {} |~ p]`,
  SUBGOAL_THEN
    `INFINITE (:A)
     ==> !p. ITF:(A->bool)#(A->A->bool)->bool |= p
             ==> ITF:(form list->bool)#(form list->form list->bool)->bool |= p`
    (fun th -> MESON_TAC[th; COMPLETENESS_THEOREM]) THEN
  INTRO_TAC "A" THEN MATCH_MP_TAC BISIMILAR_VALID THEN
  REPEAT GEN_TAC THEN INTRO_TAC "itf1 w1" THEN
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
  [REWRITE_TAC[ITF] THEN
   CONJ_TAC THENL [HYP SET_TAC "w1" []; ALL_TAC] THEN
   CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_MESON_TAC[ITF; FINITE_IMAGE]; ALL_TAC] THEN
   CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN
    HYP_TAC "itf1: _ _ _ irrefl _" (REWRITE_RULE[ITF]) THEN
    HYP MESON_TAC " irrefl inj" [];
    ALL_TAC] THEN
   REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
   HYP_TAC "itf1: _ _ _ _ trans" (REWRITE_RULE[ITF]) THEN
   HYP MESON_TAC " trans inj" [];
   ALL_TAC] THEN
  REWRITE_TAC[BISIMILAR] THEN
  EXISTS_TAC `\w1:form list w2:A. w1 IN W1 /\ w2 = f w1` THEN
  ASM_REWRITE_TAC[BISIMIMULATION] THEN REMOVE_THEN "w1" (K ALL_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  CONJ_TAC THENL [HYP MESON_TAC "inj" []; ALL_TAC] THEN
  CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
   ASM_MESON_TAC[ITF];
   ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Simple decision procedure for MLK_.                                         *)
(* ------------------------------------------------------------------------- *)

let GL_TAC : tactic =
  MATCH_MP_TAC COMPLETENESS_THEOREM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in; holds;
              ITF; GSYM MEMBER_NOT_EMPTY] THEN
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
   SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
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
