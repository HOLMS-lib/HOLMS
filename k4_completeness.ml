(* ========================================================================= *)
(* Proof of the consistency and modal completeness of K4.                    *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

let K4_AX = new_definition
  `K4_AX = {Box p --> Box Box p | p IN (:form)}`;;

let FOUR_IN_K4_AX = prove
 (`!q. Box q --> Box Box q IN K4_AX`,
  REWRITE_TAC[K4_AX; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]);;

let K4_AX_FOUR = prove
 (`!q. [K4_AX. {} |~ (Box q --> Box Box q)]`,
  MESON_TAC[MODPROVES_RULES; FOUR_IN_K4_AX]);;

let K4_DOT_BOX = prove
 (`!p. [K4_AX . {} |~ (Box p --> Box p && Box (Box p))]`,
  MESON_TAC[MLK_imp_refl_th; K4_AX_FOUR; MLK_and_intro]);;

(* ------------------------------------------------------------------------- *)
(* Transitive frames.                                                        *)
(* ------------------------------------------------------------------------- *)

let MODAL_TRANS = prove
 (`!W R.
     (!w w' w'':W. w IN W /\ w' IN W /\ w'' IN W /\
                   R w w' /\ R w' w''
                   ==> R w w'') <=>
     (!p. holds_in (W,R) (Box p --> Box Box p))`,
  MODAL_SCHEMA_TAC THEN MESON_TAC[]);;

let TRANS_DEF = new_definition
  `TRANS =
   {(W:W->bool,R:W->W->bool) |
    ~(W = {}) /\
    (!x y:W. R x y ==> x IN W /\ y IN W) /\
    (!x y z:W. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)}`;;

let IN_TRANS = prove
 (`(W:W->bool,R:W->W->bool) IN TRANS <=>
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   (!x y z:W. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)`,
  REWRITE_TAC[TRANS_DEF; IN_ELIM_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory: Transitive Frames are characteristic for K4.       *)
(* ------------------------------------------------------------------------- *)

g `TRANS:(W->bool)#(W->W->bool)->bool = CHAR K4_AX`;;
e (REWRITE_TAC[EXTENSION; FORALL_PAIR_THM]);;
e (REWRITE_TAC [IN_CHAR; IN_TRANS; IN_FRAME]);;
e (REWRITE_TAC[K4_AX; FORALL_IN_GSPEC; IN_UNIV]);;
e (REPEAT GEN_TAC);;
e EQ_TAC;;
 e (INTRO_TAC "not_empty Rel TRANS");;
  e (ASM_MESON_TAC[MODAL_TRANS]);;
 e (INTRO_TAC "(not_empty Rel) char");;
 e (ASM_MESON_TAC[MODAL_TRANS]);;
 let TRANS_CHAR_K4 = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. Transitive Frames.                              *)
(* ------------------------------------------------------------------------- *)

g `!W:W->bool R:W->W->bool.
     ~(W= {}) /\
     (!x y. R x y ==> x IN W /\ y IN W) /\
     (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)
     ==> (!p. holds_in (W,R) (Box p --> Box Box p))`;;
e (INTRO_TAC "!W R; non_empty Rel Trans");;
e (MP_TAC (REWRITE_RULE [EXTENSION; FORALL_PAIR_THM] TRANS_CHAR_K4));;
e (INTRO_TAC "Eq_form_Trans_Char");;
e (CLAIM_TAC "In_trans" `(W,R) IN TRANS:(W->bool)#(W->W->bool)->bool`);;
 e (ASM_REWRITE_TAC [IN_TRANS]);;
e (SUBGOAL_THEN `(W,R) IN CHAR K4_AX:(W->bool)#(W->W->bool)->bool`
                MP_TAC);;
 e (ASM_MESON_TAC []);;
e (ASM_REWRITE_TAC [IN_CHAR; K4_AX; FORALL_IN_GSPEC; IN_UNIV]);;
e (ASM_MESON_TAC []);;
let TRANS_IMP_FOUR = top_thm();;

let K4_TRANSNT_VALID = prove
 (`!H p. [K4_AX . H |~ p] /\
         (!q. q IN H ==> TRANS:(W->bool)#(W->W->bool)->bool |= q)
         ==> TRANS:(W->bool)#(W->W->bool)->bool |= p`,
  ASM_MESON_TAC[GEN_CHAR_VALID; TRANS_CHAR_K4]);;

(* ------------------------------------------------------------------------- *)
(* Finite Transitive Frames are appropriate for K4.                          *)
(* ------------------------------------------------------------------------- *)

let TF_DEF = new_definition
 `TF =
  {(W:W->bool,R:W->W->bool) |
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W /\
   (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)}`;;

let IN_TF = prove
 (`(W:W->bool,R:W->W->bool) IN TF <=>
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W /\
   (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)`,
  REWRITE_TAC[TF_DEF; IN_ELIM_PAIR_THM]);;

let TF_SUBSET_TRANS = prove
 (`TF:(W->bool)#(W->W->bool)->bool SUBSET TRANS`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_TF; IN_TRANS] THEN MESON_TAC[]);;

g `TF: (W->bool)#(W->W->bool)->bool = APPR K4_AX`;;
e (REWRITE_TAC[EXTENSION; FORALL_PAIR_THM]);;
e (REPEAT GEN_TAC);;
e EQ_TAC;;
 e (INTRO_TAC "In_TF");;
  e (SUBGOAL_THEN `(p1:W->bool, p2:W->W->bool) IN CHAR K4_AX` MP_TAC);;
    e (ASM_MESON_TAC [TF_SUBSET_TRANS; SUBSET; TRANS_CHAR_K4]);;
  e (HYP_TAC "In_TF" (REWRITE_RULE[IN_TF]));;
  e (ASM_REWRITE_TAC [IN_APPR; IN_FINITE_FRAME; IN_FRAME]);;
  e (ASM_MESON_TAC[CHAR_CAR]);;
 e (INTRO_TAC "In_Appr");;
  e (SUBGOAL_THEN  `(p1:W->bool,p2:W->W->bool) IN TRANS` MP_TAC);;
   e (SUBGOAL_THEN  `(p1:W->bool,p2:W->W->bool) IN CHAR K4_AX` MP_TAC);;
     e (ASM_MESON_TAC[APPR_SUBSET_CHAR; SUBSET; FORALL_PAIR_THM]);;
   e (ASM_MESON_TAC[TRANS_CHAR_K4; EXTENSION; FORALL_PAIR_THM]);;
  e (HYP_TAC "In_Appr" (REWRITE_RULE[IN_APPR; IN_FINITE_FRAME]));;
  e (ASM_REWRITE_TAC[IN_TRANS; IN_TF]);;
let TF_APPR_K4 = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. TF.                                             *)
(* ------------------------------------------------------------------------- *)

let K4_TF_VALID = prove
 (`!p. [K4_AX . {} |~ p] ==> TF:(W->bool)#(W->W->bool)->bool |= p`,
  MESON_TAC[GEN_APPR_VALID; TF_APPR_K4]);;

(* ------------------------------------------------------------------------- *)
(* Proof of Consistency of K4.                                               *)
(* ------------------------------------------------------------------------- *)

let K4_CONSISTENT = prove
 (`~ [K4_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] K4_TF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM;
              IN_TF; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* K4 standard frames and models.                                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Standard Frame.                                                           *)
(* ------------------------------------------------------------------------- *)

let K4_STANDARD_FRAME_DEF = new_definition
  `K4_STANDARD_FRAME p = GEN_STANDARD_FRAME K4_AX p`;;

let IN_K4_STANDARD_FRAME = prove
 (`!p W R. (W,R) IN K4_STANDARD_FRAME p <=>
           W = {w | MAXIMAL_CONSISTENT K4_AX p w /\
                    (!q. MEM q w ==> q SUBSENTENCE p)} /\
           (W,R) IN TF /\
           (!q w. Box q SUBFORMULA p /\ w IN W
                  ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`,
 REPEAT GEN_TAC THEN
 REWRITE_TAC[K4_STANDARD_FRAME_DEF; IN_GEN_STANDARD_FRAME] THEN
 EQ_TAC THEN MESON_TAC[TF_APPR_K4]);;

(* ------------------------------------------------------------------------- *)
(* Standard model.                                                           *)
(* ------------------------------------------------------------------------- *)

let K4_STANDARD_MODEL_DEF = new_definition
  `K4_STANDARD_MODEL = GEN_STANDARD_MODEL K4_AX`;;

let TF_SUBSET_FRAME = prove
 (`TF:(W->bool)#(W->W->bool)->bool SUBSET FRAME`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM] THEN INTRO_TAC "![W] [R]" THEN
  REWRITE_TAC[IN_TF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_FRAME]);;

let K4_STANDARD_MODEL_CAR = prove
 (`!W R p V.
     K4_STANDARD_MODEL p (W,R) V <=>
     (W,R) IN K4_STANDARD_FRAME p /\
     (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[K4_STANDARD_MODEL_DEF; GEN_STANDARD_MODEL_DEF] THEN
  REWRITE_TAC[IN_K4_STANDARD_FRAME; IN_GEN_STANDARD_FRAME] THEN
  EQ_TAC THEN ASM_MESON_TAC[TF_APPR_K4]);;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let K4_TRUTH_LEMMA = prove
 (`!W R p V q.
     ~ [K4_AX . {} |~ p] /\
     K4_STANDARD_MODEL p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REWRITE_TAC[K4_STANDARD_MODEL_DEF] THEN MESON_TAC[GEN_TRUTH_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Accessibility lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let K4_STANDARD_REL_DEF = new_definition
  `K4_STANDARD_REL p w x <=>
   GEN_STANDARD_REL K4_AX p w x /\
   (!B. MEM (Box B) w ==> MEM (Box B) x)`;;

let K4_STANDARD_REL_CAR = prove
 (`!p w x.
     K4_STANDARD_REL p w x <=>
     MAXIMAL_CONSISTENT K4_AX p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT K4_AX p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
     (!B. MEM (Box B) w ==> MEM (Box B) x /\ MEM B x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[K4_STANDARD_REL_DEF; GEN_STANDARD_REL] THEN
  EQ_TAC THEN REPEAT (ASM_MESON_TAC[]) THEN REPEAT (ASM_MESON_TAC[]));;

let TF_MAXIMAL_CONSISTENT = prove
 (`!p. ~ [K4_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT K4_AX p M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)},
            K4_STANDARD_REL p)
           IN TF `,
  INTRO_TAC "!p; p" THEN
  MP_TAC (ISPECL [`K4_AX`; `p:form`] GEN_FINITE_FRAME_MAXIMAL_CONSISTENT) THEN
  REWRITE_TAC[IN_FINITE_FRAME] THEN INTRO_TAC "gen_max_cons" THEN
  ASM_REWRITE_TAC[IN_TF] THEN
  (* Nonempty *)
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Well-defined *)
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[K4_STANDARD_REL_DEF] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Finite *)
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   (* Transitive *)
  REWRITE_TAC[IN_ELIM_THM; K4_STANDARD_REL_CAR] THEN
  INTRO_TAC "!x y z; (x1 x2) (y1 y2) (z1 z2) +" THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let CONJLIST_FLATMAP_DOT_BOX_LEMMA_K4 = prove
 (`!w. [K4_AX . {} |~
          CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
          -->
          CONJLIST (MAP (Box)
            (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))]`,
  MATCH_MP_TAC CONJLIST_FLATMAP_DOT_BOX_LEMMA_2 THEN
  MATCH_ACCEPT_TAC K4_DOT_BOX);;

let XK_SUBLIST_XK4 = prove
 (`!q. CONS (Not q) (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)
       SUBLIST
       CONS (Not q)
            (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w)`,
  GEN_TAC THEN REWRITE_TAC[CONS_SUBLIST] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[MEM] ; ALL_TAC] THEN
  REWRITE_TAC[SUBLIST] THEN INTRO_TAC "!x; a" THEN
  SUBGOAL_THEN `MEM (Box x) w` MP_TAC THENL
  [MATCH_MP_TAC MEM_FLATMAP_LEMMA THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  INTRO_TAC "memw" THEN ASM_REWRITE_TAC[MEM] THEN DISJ2_TAC THEN
  ASM_REWRITE_TAC[MEM_FLATMAP] THEN  EXISTS_TAC `Box x:form` THEN
  ASM_REWRITE_TAC[MEM]);;

g `!p w q.
     ~ [K4_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT K4_AX p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     Box q SUBFORMULA p /\
     (!x. K4_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`;;
e (INTRO_TAC "!p w q; p  maxw subw boxq rrr");;
e (REFUTE_THEN (LABEL_TAC "contra") THEN
  REMOVE_THEN "rrr" MP_TAC THEN REWRITE_TAC[NOT_FORALL_THM]);;
e (CLAIM_TAC "consistent_X"
     `CONSISTENT K4_AX
        (CONS (Not q)
              (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))`);;
  e (REMOVE_THEN "contra" MP_TAC);;
  e (REWRITE_TAC[CONSISTENT; CONTRAPOS_THM]);;
  e (INTRO_TAC "incons" THEN MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA);;
  e (MAP_EVERY EXISTS_TAC
       [`K4_AX`;
        `p:form`;
        `FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w`]);;
  e (ASM_REWRITE_TAC[]);;
  e CONJ_TAC;;
   e GEN_TAC;;
   e (REWRITE_TAC[MEM_FLATMAP_LEMMA_2] THEN MESON_TAC[]);;
   e (MATCH_MP_TAC MLK_imp_trans);;
   e (EXISTS_TAC `CONJLIST (MAP (Box)
                  (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))`);;
   e CONJ_TAC;;
    e (MP_TAC (CONJLIST_FLATMAP_DOT_BOX_LEMMA_K4));;
    e (ASM_MESON_TAC[]);;
   e (CLAIM_TAC "XIMP" `!y l. [K4_AX . {} |~ Not (Not y && CONJLIST l)]
                                ==> [K4_AX . {} |~ (CONJLIST (MAP (Box) l)) --> Box(y)]`);;
    e (REPEAT STRIP_TAC);;
    e (MATCH_MP_TAC MLK_imp_trans);;
    e (EXISTS_TAC `Box (CONJLIST l)`THEN CONJ_TAC);;
    e (MESON_TAC[CONJLIST_MAP_BOX; MLK_iff_imp1]);;
   e (MATCH_MP_TAC MLK_imp_box);;
   e (ONCE_REWRITE_TAC[GSYM MLK_contrapos_eq]);;
   e (MATCH_MP_TAC MLK_imp_trans);;
   e (EXISTS_TAC `CONJLIST l --> False`);;
   e CONJ_TAC;;
    e (ASM_MESON_TAC[MLK_shunt; MLK_not_def];);;
   e (MATCH_MP_TAC MLK_imp_trans);;
   e (EXISTS_TAC `Not (CONJLIST l)`);;
   e CONJ_TAC;;
    e (MESON_TAC[MLK_axiom_not;MLK_iff_imp2]);;
   e (MESON_TAC[MLK_imp_refl_th]);;


  e (POP_ASSUM MATCH_MP_TAC);;
  e (HYP_TAC "incons" (REWRITE_RULE[CONSISTENT]));;
  e (HYP_TAC "incons" (ONCE_REWRITE_RULE[CONJLIST]));;
  e (POP_ASSUM MP_TAC);;
  e (COND_CASES_TAC);;
   e (ASM_REWRITE_TAC[MLK_DOUBLENEG]);;
   e (INTRO_TAC "notnotq");;
   e (CLAIM_TAC "or" `[K4_AX . {} |~ Not Not q || Not CONJLIST []]`);;
     e (ASM_MESON_TAC [MLK_or_introl]);;
   e (CLAIM_TAC "eq" `[K4_AX . {} |~ Not (Not q && CONJLIST []) <-> Not Not q || Not CONJLIST []]`);;
    e (ASM_MESON_TAC[MLK_de_morgan_and_th]);;
   e (ASM_MESON_TAC[MLK_iff_mp;MLK_iff_sym]);;
  e (DISCH_THEN MATCH_ACCEPT_TAC);;
e (MP_TAC (SPECL
    [`K4_AX`;
     `p:form`;
     `CONS (Not q)
           (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w)`]
    EXTEND_MAXIMAL_CONSISTENT));;
e ANTS_TAC;;
 e (ASM_REWRITE_TAC[MEM] THEN GEN_TAC THEN STRIP_TAC THEN
     REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC));;
  e (MATCH_MP_TAC SUBFORMULA_IMP_NEG_SUBSENTENCE);;
  e (HYP MESON_TAC "boxq"
       [SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
  e (POP_ASSUM (DESTRUCT_TAC "@y. +" o REWRITE_RULE[MEM_FLATMAP]) THEN
     STRUCT_CASES_TAC (SPEC `y:form` (cases "form")) THEN REWRITE_TAC[MEM] THEN
     STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC);;
  e (MATCH_MP_TAC SUBFORMULA_IMP_SUBSENTENCE);;
  e (CLAIM_TAC "rmk" `Box a SUBSENTENCE p`);;
    e (POP_ASSUM MP_TAC THEN HYP MESON_TAC "subw" []);;
  e (HYP_TAC "rmk" (REWRITE_RULE[SUBSENTENCE_CASES; distinctness "form"]) THEN
     TRANS_TAC SUBFORMULA_TRANS `Box a` THEN ASM_REWRITE_TAC[] THEN
     MESON_TAC[SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
  e (POP_ASSUM MP_TAC THEN HYP MESON_TAC "subw" []);;
  e (INTRO_TAC "@X. maxX subX subl");;
 e (EXISTS_TAC `X:form list`);;
 e (ASM_REWRITE_TAC[NOT_IMP]);;
 e (ASM_REWRITE_TAC[K4_STANDARD_REL_DEF]);;
 e (MP_TAC (ISPECL [`K4_AX`; `p:form`;`w: form list`; `q:form`]
                   GEN_ACCESSIBILITY_LEMMA));;
 e (ANTS_TAC);;
  e (ASM_REWRITE_TAC[]);;
 e (CLAIM_TAC "subl2"
      `CONS (Not q) (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)
       SUBLIST
       CONS (Not q)
            (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w)`);;
  e (ASM_MESON_TAC[XK_SUBLIST_XK4]);;
 e (ASM_MESON_TAC[SUBLIST_TRANS]);;
e (INTRO_TAC "gsr_wX notqX ");;
e (ASM_REWRITE_TAC[]);;
e (INTRO_TAC "!B; B" THEN HYP_TAC "subl" (REWRITE_RULE[SUBLIST]));;
e (REMOVE_THEN "subl" MATCH_MP_TAC);;
e (REWRITE_TAC[MEM; distinctness "form"; injectivity "form"]);;
e (REWRITE_TAC[MEM_FLATMAP]);;
e (EXISTS_TAC `Box B`);;
e (ASM_REWRITE_TAC[MEM]);;
let K4_ACCESSIBILITY_LEMMA = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Modal completeness theorem for K4.                                        *)
(* ------------------------------------------------------------------------- *)

g `!p. ~ [K4_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT K4_AX p M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)},
            K4_STANDARD_REL p)
           IN K4_STANDARD_FRAME p`;;
e (INTRO_TAC "!p; not_theor_p");;
e (REWRITE_TAC [IN_K4_STANDARD_FRAME]);;
e CONJ_TAC;;
 e (MATCH_MP_TAC TF_MAXIMAL_CONSISTENT);;
 e (ASM_REWRITE_TAC[]);;
 e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (INTRO_TAC "!q w; boxq maxw subw");;
e EQ_TAC;;
 e (ASM_MESON_TAC[K4_STANDARD_REL_CAR]);;
e (ASM_MESON_TAC[K4_ACCESSIBILITY_LEMMA]);;
let K4F_IN_K4_STANDARD_FRAME = top_thm();;

let K4_COUNTERMODEL = prove
 (`!M p.
     ~ [K4_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT K4_AX p M /\
     MEM (Not p) M /\
     (!q. MEM q M ==> q SUBSENTENCE p)
     ==>
     ~holds
        ({M | MAXIMAL_CONSISTENT K4_AX p M /\
              (!q. MEM q M ==> q SUBSENTENCE p)},
         K4_STANDARD_REL p)
        (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
        p M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC GEN_COUNTERMODEL THEN
  EXISTS_TAC `K4_AX` THEN ASM_REWRITE_TAC[GEN_STANDARD_MODEL_DEF] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[K4F_IN_K4_STANDARD_FRAME; K4_STANDARD_FRAME_DEF];
   ALL_TAC] THENL
  [ASM_MESON_TAC[IN_ELIM_THM]]);;

g `!p. TF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [K4_AX . {} |~ p]`;;
e (GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM]);;
e (INTRO_TAC "p_not_theor");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT K4_AX p M /\
                     (!q. MEM q M ==> q SUBSENTENCE p)},
                K4_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC);;
e (MATCH_MP_TAC TF_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `({M | MAXIMAL_CONSISTENT K4_AX p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
                  K4_STANDARD_REL p)
                 IN GEN_STANDARD_FRAME K4_AX p`
                MP_TAC);;
 e (ASM_MESON_TAC[K4F_IN_K4_STANDARD_FRAME; K4_STANDARD_FRAME_DEF]);;
e (ASM_MESON_TAC[GEN_COUNTERMODEL_ALT]);;
let K4_COMPLETENESS_THM = top_thm ();;


(* ------------------------------------------------------------------------- *)
(* Modal completeness for K4 for models on a generic (infinite) domain.      *)
(* ------------------------------------------------------------------------- *)

let K4_COMPLETENESS_THM_GEN = prove
 (`!p. INFINITE (:A) /\ TF:(A->bool)#(A->A->bool)->bool |= p
       ==> [K4_AX . {} |~ p]`,
  SUBGOAL_THEN
    `INFINITE (:A)
     ==> !p. TF:(A->bool)#(A->A->bool)->bool |= p
             ==> TF:(form list->bool)#(form list->form list->bool)->bool |= p`
    (fun th -> MESON_TAC[th; K4_COMPLETENESS_THM]) THEN
  ASM_MESON_TAC[TF_APPR_K4; GEN_LEMMA_FOR_GEN_COMPLETENESS]);;

(* ------------------------------------------------------------------------- *)
(* Simple decision procedure for K4.                                         *)
(* ------------------------------------------------------------------------- *)

let K4_TAC : tactic =
  MATCH_MP_TAC K4_COMPLETENESS_THM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in; holds;
              IN_TF; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[];;

let K4_RULE tm =
  prove(tm, REPEAT GEN_TAC THEN K4_TAC);;

K4_RULE `!p q r. [K4_AX . {} |~ p && q && r --> p && r]`;;
K4_RULE `!p. [K4_AX . {} |~ Box p --> Box (Box p)]`;;
K4_RULE `!p q. [K4_AX . {} |~  Box (p --> q) && Box p --> Box q]`;;
(* K4_RULE `!p. [K4_AX . {} |~ (Box (Box p --> p) --> Box p)]`;;*)
(* K4_RULE `!p. [GL_AX . {} |~ Box (Box p --> p) --> Box p]`;; *)
(* K4_RULE `[GL_AX . {} |~ Box (Box False --> False) --> Box False]`;; *)

(* K4_box_iff_th *)
K4_RULE `!p q. [K4_AX . {} |~ Box (p <-> q) --> (Box p <-> Box q)] `;;

(* ------------------------------------------------------------------------- *)
(* Countermodel using set of formulae (instead of lists of formulae).        *)
(* ------------------------------------------------------------------------- *)

let K4_STDWORLDS_RULES,K4_STDWORLDS_INDUCT,K4_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT K4_AX p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN K4_STDWORLDS p`;;

let K4_STDREL_RULES,K4_STDREL_INDUCT,K4_STDREL_CASES = new_inductive_definition
  `!w1 w2. K4_STANDARD_REL p w1 w2
           ==> K4_STDREL p (set_of_list w1) (set_of_list w2)`;;

let K4_STDREL_IMP_K4_STDWORLDS = prove
 (`!p w1 w2. K4_STDREL p w1 w2 ==>
             w1 IN K4_STDWORLDS p /\
             w2 IN K4_STDWORLDS p`,
  GEN_TAC THEN MATCH_MP_TAC K4_STDREL_INDUCT THEN
  REWRITE_TAC[K4_STANDARD_REL_CAR] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC K4_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;

let SET_OF_LIST_EQ_K4_STANDARD_REL = prove
 (`!p u1 u2 w1 w2.
     set_of_list u1 = set_of_list w1 /\ NOREPETITION w1 /\
     set_of_list u2 = set_of_list w2 /\ NOREPETITION w2 /\
     K4_STANDARD_REL p u1 u2
     ==> K4_STANDARD_REL p w1 w2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[K4_STANDARD_REL_CAR] THEN
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
        {M | MAXIMAL_CONSISTENT K4_AX p M /\
             (!q. MEM q M ==> q SUBSENTENCE p)},
        K4_STANDARD_REL p,
        (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
      )
      (K4_STDWORLDS p,
       K4_STDREL p,
       (\a w. Atom a SUBFORMULA p /\ Atom a IN w))
      (\w1 w2.
         MAXIMAL_CONSISTENT K4_AX p w1 /\
         (!q. MEM q w1 ==> q SUBSENTENCE p) /\
         w2 IN K4_STDWORLDS p /\
         set_of_list w1 = w2)`,
 GEN_TAC THEN REWRITE_TAC[BISIMIMULATION] THEN REPEAT GEN_TAC THEN
 STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
 [GEN_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC[IN_SET_OF_LIST];
  ALL_TAC] THEN
 CONJ_TAC THENL
 [INTRO_TAC "![u1]; w1u1" THEN EXISTS_TAC `set_of_list u1:form->bool` THEN
  HYP_TAC "w1u1 -> hp" (REWRITE_RULE[K4_STANDARD_REL_CAR]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC K4_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC K4_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN MATCH_MP_TAC K4_STDREL_RULES THEN
  ASM_REWRITE_TAC[];
  ALL_TAC] THEN
 INTRO_TAC "![u2]; w2u2" THEN EXISTS_TAC `list_of_set u2:form list` THEN
 REWRITE_TAC[CONJ_ACI] THEN
 HYP_TAC "w2u2 -> @x2 y2. x2 y2 x2y2" (REWRITE_RULE[K4_STDREL_CASES]) THEN
 REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
 SIMP_TAC[SET_OF_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
 SIMP_TAC[MEM_LIST_OF_SET; FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
 CONJ_TAC THENL
 [HYP_TAC "x2y2 -> hp" (REWRITE_RULE[K4_STANDARD_REL_CAR]) THEN
  ASM_REWRITE_TAC[];
  ALL_TAC] THEN
 CONJ_TAC THENL
 [ASM_MESON_TAC[K4_STDREL_IMP_K4_STDWORLDS]; ALL_TAC] THEN
 CONJ_TAC THENL
 [MATCH_MP_TAC SET_OF_LIST_EQ_K4_STANDARD_REL THEN
  EXISTS_TAC `x2:form list` THEN EXISTS_TAC `y2:form list` THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET;
           FINITE_SET_OF_LIST] THEN
  ASM_MESON_TAC[MAXIMAL_CONSISTENT];
  ALL_TAC] THEN
 MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN
 EXISTS_TAC `y2:form list` THEN
 SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
 SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
 ASM_MESON_TAC[K4_STANDARD_REL_CAR]);;

let K4_COUNTERMODEL_FINITE_SETS = prove
 (`!p. ~ [K4_AX . {} |~ p] ==> ~holds_in (K4_STDWORLDS p, K4_STDREL p) p`,
  INTRO_TAC "!p; p" THEN
  DESTRUCT_TAC "@M. max mem subf"
    (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ [K4_AX . {} |~ p]`)) THEN
  REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP] THEN
  ASSUM_LIST (LABEL_TAC "hp" o MATCH_MP K4_COUNTERMODEL o
                end_itlist CONJ o rev) THEN
  EXISTS_TAC `\a w. Atom a SUBFORMULA p /\ Atom a IN w` THEN
  EXISTS_TAC `set_of_list M:form->bool` THEN CONJ_TAC THENL
  [MATCH_MP_TAC K4_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "hp" MP_TAC THEN
  MATCH_MP_TAC (MESON[] `(p <=> q) ==> (~p ==> ~q)`) THEN
  MATCH_MP_TAC BISIMIMULATION_HOLDS THEN
  EXISTS_TAC`\w1 w2. MAXIMAL_CONSISTENT K4_AX p w1 /\
                     (!q. MEM q w1 ==> q SUBSENTENCE p) /\
                     w2 IN K4_STDWORLDS p /\
                     set_of_list w1 = w2` THEN
  ASM_REWRITE_TAC[BISIMIMULATION_SET_OF_LIST] THEN
  MATCH_MP_TAC K4_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;
