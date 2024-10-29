(* ========================================================================= *)
(* Proof of the consistency and modal completeness of K.                     *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* ========================================================================= *)

let K_FRAME_DEF = new_definition
  `K_FRAME = {(W:W->bool,R) | (W,R) IN FRAME /\ FINITE W}`;;

let IN_K_FRAME = prove
 (`(W,R) IN K_FRAME <=>
   ~(W = {}) /\ (!x y:W. R x y ==> x IN W /\ y IN W) /\ FINITE W`,
  REWRITE_TAC[K_FRAME_DEF; IN_ELIM_PAIR_THM; IN_FRAME] THEN MESON_TAC[]);;

let K_FRAME_SUBSET_FRAME = prove
 (`K_FRAME:(W->bool)#(W->W->bool)->bool SUBSET FRAME`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_K_FRAME; IN_FRAME] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Soundness.                                                                *)
(* ------------------------------------------------------------------------- *)

let KAXIOM_VALID = prove
 (`!p. KAXIOM p ==> WR:(W->bool)#(W->W->bool)->bool |= p`,
  MATCH_MP_TAC KAXIOM_INDUCT THEN MODAL_TAC);;

g `!S H p.
     [S . H |~ p]
     ==> (!q. q IN S ==> K_FRAME:(W->bool)#(W->W->bool)->bool |= q) /\
         (!q. q IN H ==> K_FRAME:(W->bool)#(W->W->bool)->bool |= q)
         ==> K_FRAME:(W->bool)#(W->W->bool)->bool |= p`;;
e GEN_TAC;;
e (MATCH_MP_TAC MODPROVES_INDUCT);;
e (CONJ_TAC THENL [SIMP_TAC[KAXIOM_VALID]; ALL_TAC]);;
e (CONJ_TAC THENL [MESON_TAC[]; ALL_TAC]);;
e (CONJ_TAC THENL [MESON_TAC[]; ALL_TAC]);;
e (CONJ_TAC THENL [MODAL_TAC; ALL_TAC]);;
e (REWRITE_TAC[NOT_IN_EMPTY]);;
e MODAL_TAC;;
let FRAME_VALID = top_thm ();;

let K_FRAME_VALID = prove
 (`!H p.
     [{} . H |~ p]
     ==> (!q. q IN H ==> K_FRAME:(W->bool)#(W->W->bool)->bool |= q)
         ==> K_FRAME:(W->bool)#(W->W->bool)->bool |= p`,
  MESON_TAC[FRAME_VALID; NOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness                                                        *)
(* ------------------------------------------------------------------------- *)

g `~ [{} . {} |~ False]`;;
e (REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] K_FRAME_VALID)));;
e (REWRITE_TAC[NOT_IN_EMPTY]);;
e (REWRITE_TAC[valid; holds; holds_in;
               FORALL_PAIR_THM; IN_K_FRAME; NOT_FORALL_THM]);;
e (MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`]);;
e (REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING]);;
e (MESON_TAC[]);;
let K_CONSISTENT = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* Standard Frames.                                                          *)
(* ------------------------------------------------------------------------- *)

let K_STANDARD_FRAME_DEF = new_definition
  `K_STANDARD_FRAME = GEN_STANDARD_FRAME K_FRAME {}`;;

let IN_K_STANDARD_FRAME = prove
 (`(W,R) IN K_STANDARD_FRAME p <=>
   W = {w | MAXIMAL_CONSISTENT {} p w /\
            (!q. MEM q w ==> q SUBSENTENCE p)} /\
   (W,R) IN K_FRAME /\
   (!q w. Box q SUBFORMULA p /\ w IN W
          ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`,
  REWRITE_TAC[K_STANDARD_FRAME_DEF; IN_GEN_STANDARD_FRAME] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (REWRITE_RULE [SUBSET] K_FRAME_SUBSET_FRAME) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Standard Models.                                                          *)
(* ------------------------------------------------------------------------- *)

let K_STANDARD_MODEL_DEF = new_definition
  `K_STANDARD_MODEL = GEN_STANDARD_MODEL K_FRAME {}`;;

let K_STANDARD_MODEL_CAR = prove
 (`K_STANDARD_MODEL p (W,R) V <=>
   (W,R) IN K_STANDARD_FRAME p /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`,
  REWRITE_TAC[K_STANDARD_MODEL_DEF; K_STANDARD_FRAME_DEF;
              GEN_STANDARD_MODEL_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let K_TRUTH_LEMMA = prove
(`!W R p V q.
    ~ [{} . {} |~ p] /\
    K_STANDARD_MODEL p (W,R) V /\
    q SUBFORMULA p
    ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REWRITE_TAC[K_STANDARD_MODEL_DEF] THEN MESON_TAC[GEN_TRUTH_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Accessibility lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let K_STANDARD_REL_DEF = new_definition
  `K_STANDARD_REL p = GEN_STANDARD_REL {} p`;;

let K_STANDARD_REL_CAR = prove
 (`K_STANDARD_REL p w x <=>
   MAXIMAL_CONSISTENT {} p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT {} p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)`,
  REWRITE_TAC[K_STANDARD_REL_DEF; GEN_STANDARD_REL]);;

g `!p. ~ [{} . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT {} p M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)},
                 K_STANDARD_REL p) IN K_FRAME `;;
e (INTRO_TAC "!p; p");;
e (REWRITE_TAC[IN_K_FRAME]);;
e CONJ_TAC;; (* non empty *)
 e (REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM]);;
 e (ASM_MESON_TAC[NONEMPTY_MAXIMAL_CONSISTENT]);;
e CONJ_TAC;; (* well define *)
 e (REWRITE_TAC[K_STANDARD_REL_CAR]);;
 e (SET_TAC[]);;
e (MATCH_MP_TAC FINITE_SUBSET);; (* finite *)
e (EXISTS_TAC `{l | NOREPETITION l /\
                    !q. MEM q l ==> q IN {q | q SUBSENTENCE p}}`);;
e (CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[MAXIMAL_CONSISTENT]]);;
e (MATCH_MP_TAC FINITE_NOREPETITION);;
e (POP_ASSUM_LIST (K ALL_TAC));;
e (SUBGOAL_THEN `{q | q SUBSENTENCE p} =
                 {q | q SUBFORMULA p} UNION IMAGE (Not) {q | q SUBFORMULA p}`
     SUBST1_TAC);;
 e (REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_UNION;
                FORALL_IN_GSPEC; FORALL_IN_IMAGE]);;
 e (REWRITE_TAC[IN_UNION; IN_ELIM_THM; SUBSENTENCE_RULES]);;
 e GEN_TAC;;
 e (GEN_REWRITE_TAC LAND_CONV [SUBSENTENCE_CASES]);;
 e (ASM SET_TAC[]);;
e (REWRITE_TAC[FINITE_UNION; FINITE_SUBFORMULA]);;
e (MATCH_MP_TAC FINITE_IMAGE);;
e (REWRITE_TAC[FINITE_SUBFORMULA]);;
let K_MAXIMAL_CONSISTENT = top_thm ();;

g `!p l. MEM p (FLATMAP (\x. match x with Box c -> [c] | _ -> []) l)
         ==> MEM (Box p) l`;;
e (GEN_TAC);;
e (LIST_INDUCT_TAC);;
  e (REWRITE_TAC[MEM; FLATMAP]);;
e (PURE_REWRITE_TAC[FLATMAP]);;
e (PURE_REWRITE_TAC[MEM_APPEND]);;
e (PURE_ONCE_REWRITE_TAC[MESON[]
     `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`]);;
e CONJ_TAC;;
  r 1;;
  e (ASM IMP_REWRITE_TAC[MEM]);;
e (REWRITE_TAC[MEM]);;
e (ASSUME_TAC (MATCH_CONV `match h with Box c -> [c] | _ -> []`));;
e (REMOVE_THEN "" MP_TAC THEN COND_CASES_TAC);;
  e (POP_ASSUM (CHOOSE_THEN SUBST_VAR_TAC));;
  e (ASM_REWRITE_TAC[MEM]);;
  e (MESON_TAC[]);;
e (STRIP_TAC);;
e (FIRST_X_ASSUM(SUBST1_TAC));;
e (REWRITE_TAC[MEM]);;
let MEM_FLATMAP_LEMMA = top_thm();;

g `!p l. MEM p (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) l)
         ==>  MEM p l`;;
e (GEN_TAC);;
e (LIST_INDUCT_TAC);;
  e (REWRITE_TAC[MEM; FLATMAP]);;
e (PURE_REWRITE_TAC[FLATMAP]);;
e (PURE_REWRITE_TAC[MEM_APPEND]);;
e (PURE_ONCE_REWRITE_TAC[MESON[]
     `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`]);;
e CONJ_TAC;;
  r 1;;
  e (ASM IMP_REWRITE_TAC[MEM]);;
e (REWRITE_TAC[MEM]);;
e (ASSUME_TAC (MATCH_CONV `match h with Box c -> [Box c] | _ -> []`));;
e (FIRST_X_ASSUM MP_TAC THEN COND_CASES_TAC);;
  e (POP_ASSUM (CHOOSE_THEN SUBST_VAR_TAC));;
  e (ASM_REWRITE_TAC[MEM]);;
  e (MESON_TAC[]);;
e (STRIP_TAC);;
e (FIRST_X_ASSUM(SUBST1_TAC));;
e (REWRITE_TAC[MEM]);;
let MEM_FLATMAP_LEMMA_1 = top_thm();;

g `!w. [{} . {}
        |~ CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
           --> CONJLIST (MAP (Box)
                             (FLATMAP (\x. match x with Box c -> [c] | _ -> [])
                                      w))]`;;
e (LIST_INDUCT_TAC);;
  e (REWRITE_TAC[MEM; FLATMAP; MAP; MLK_imp_refl_th]);;
e (REWRITE_TAC[FLATMAP; MAP_APPEND]);;
e (MATCH_MP_TAC MLK_imp_trans);;
e (EXISTS_TAC
     `CONJLIST (match h with Box c -> [Box c] | _ -> []) &&
      CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) t)`);;
e (CONJ_TAC);;
  e (MATCH_MP_TAC MLK_iff_imp1);;
  e (MATCH_ACCEPT_TAC CONJLIST_APPEND);;
e (MATCH_MP_TAC MLK_imp_trans);;
e (EXISTS_TAC
     `CONJLIST (MAP (Box) (match h with Box c -> [c] | _ -> [])) &&
      CONJLIST (MAP (Box)
       (FLATMAP (\x. match x with Box c -> [c] | _ -> []) t))`);;
e (CONJ_TAC);;
  r (1);;
  e (MATCH_MP_TAC MLK_iff_imp2);;
  e (MATCH_ACCEPT_TAC CONJLIST_APPEND);;
e (MATCH_MP_TAC MLK_and_intro);;
e (CONJ_TAC);;
  r (1);;
  e (ASM_MESON_TAC[MLK_imp_trans; MLK_and_right_th; MAP]);;
e (MATCH_MP_TAC MLK_imp_trans);;
e (EXISTS_TAC `CONJLIST (match h with Box c -> [Box c] | _ -> [])`);;
e (CONJ_TAC);;
  e (MATCH_ACCEPT_TAC MLK_and_left_th);;
e (POP_ASSUM (K ALL_TAC));;
e (STRUCT_CASES_TAC (SPEC `h:form` (cases "form")));;
e (REWRITE_TAC[distinctness "form"; MAP; MLK_imp_refl_th]);;
e (REWRITE_TAC[distinctness "form"; MAP; MLK_imp_refl_th]);;
e (REWRITE_TAC[distinctness "form"; MAP; MLK_imp_refl_th]);;
e (REWRITE_TAC[distinctness "form"; MAP; MLK_imp_refl_th]);;
e (REWRITE_TAC[distinctness "form"; MAP; MLK_imp_refl_th]);;
e (REWRITE_TAC[distinctness "form"; MAP; MLK_imp_refl_th]);;
e (REWRITE_TAC[distinctness "form"; MAP; MLK_imp_refl_th]);;
e (REWRITE_TAC[distinctness "form"; MAP; MLK_imp_refl_th]);;
e (REWRITE_TAC[distinctness "form"; MAP; MLK_imp_refl_th]);;
let CONJLIST_FLATMAP_DOT_BOX_LEMMA = top_thm();;

g `!p X. [{} . {} |~ (CONJLIST (CONS p X) --> False) <->
                     (p && CONJLIST X --> False)]`;;
e (REPEAT GEN_TAC);;
e (MATCH_MP_TAC MLK_imp_subst);;
e (ASM_REWRITE_TAC[MLK_iff_refl_th; CONJLIST_CONS]);;
let CONJLIST_CONS_NOT = top_thm();;

g `!p X. [{} . {} |~ CONJLIST (CONS p X) --> False] <=>
         [{} . {} |~ p && CONJLIST X --> False]`;;
e (REPEAT GEN_TAC);;
e (ASM_MESON_TAC[CONJLIST_CONS_NOT; MLK_iff]);;
let CONJLIST_CONS_NOT_TH = top_thm();;

g `!p q r. [{} . {} |~ p && q --> r] <=> [{} . {} |~ p --> q --> r]`;;
e (MESON_TAC[MLK_shunt;MLK_ante_conj]);;
let K_AND_IMP = top_thm();;

g `!p q. [{} . {} |~ Not p --> q <-> (p --> False) --> q]`;;
e (REPEAT GEN_TAC);;
e (MATCH_MP_TAC MLK_imp_subst);;
e (REWRITE_TAC[MLK_axiom_not; MLK_iff_refl_th]);;
let K_NOT_IMP_ID = top_thm();;

g `!p q r.
        [{} . {} |~ (Not p --> q --> r) <-> ((p --> False) --> q --> r)]`;;
e (REPEAT GEN_TAC);;
e (MATCH_MP_TAC MLK_imp_subst);;
e (REWRITE_TAC[MLK_axiom_not; MLK_iff_refl_th]);;
let K_NOT_IMP_ID_1 = top_thm();;

g `!p q r. [{} . {} |~ Not p --> q --> r] <=>
           [{} . {} |~ (p --> False) --> q --> r]`;;
e (REPEAT GEN_TAC);;
e (MESON_TAC[K_NOT_IMP_ID_1; MLK_iff]);;
let K_NOT_IMP_ID_2 = top_thm();;

g `!q p. [{} . {} |~ Not q && p --> False] <=>
         [{} . {} |~ (q --> False) --> p --> False]`;;
e (REPEAT GEN_TAC);;
e (REWRITE_TAC[K_AND_IMP]);;
e (REWRITE_TAC[K_NOT_IMP_ID_2]);;
let K_NOT_IMP_False = top_thm();;

g `!p q. [{} . {} |~ p <-> q]
         ==> ([{} . {} |~ Not p] <=> [{} . {} |~ Not q])`;;
e (MESON_TAC[MLK_iff; MLK_not_subst]);;
let K_NOT_SUBST_1 = top_thm();;

g `!p. [{} . {} |~ Not p --> False] <=> [{} . {} |~ Not (p --> False)]`;;
e (GEN_TAC);;
e (MATCH_MP_TAC (MESON[]
     `!p q r. ([{} . {} |~ p] <=> [{} . {} |~ q]) /\
              ([{} . {} |~ q] <=> [{} . {} |~ r])
              ==> ([{} . {} |~ p] <=> [{} . {} |~ r])`));;
e (EXISTS_TAC `Not Not p`);;
e (CONJ_TAC);;
  e (ASM_MESON_TAC[MLK_DOUBLENEG_CL; MLK_not_def]);;
e (SUBGOAL_THEN
     `[{} . {} |~ Not p <-> (p --> False)]
      ==> ([{} . {} |~ Not Not p] <=> [{} . {} |~ Not (p --> False)])`
     (fun th -> MATCH_MP_TAC th));;
  e (MESON_TAC[K_NOT_SUBST_1]);;
e (REWRITE_TAC[MLK_axiom_not]);;
let K_NOT_IMP_ID_4 = top_thm();;

g `!q p. [{} . {} |~ Not q && p --> False]
         ==> [{} . {} |~ p --> q]`;;
e (REPEAT GEN_TAC);;
e (REWRITE_TAC[K_NOT_IMP_False]);;
e (MATCH_MP_TAC (MESON[]
     `!p q r. ([{} . {} |~ p] ==> [{} . {} |~ q]) /\
              ([{} . {} |~ q] ==> [{} . {} |~ r])
              ==> ([{} . {} |~ p] ==> [{} . {} |~ r])`));;
e (EXISTS_TAC `((p --> q) --> False) --> False`);;
e (REWRITE_TAC[MLK_imp_false_rule]);;
e (REWRITE_TAC[GSYM MLK_not_def]);;
e (STRIP_TAC);;
e (MATCH_MP_TAC MLK_DOUBLENEG_CL);;
e (SIMP_TAC[MLK_not_def]);;
e (ASM_MESON_TAC[K_NOT_IMP_ID_4]);;
let K_NOT_IMP_ID_5 = top_thm();;

g `!p w q.
     ~ [{} . {} |~ p] /\
     MAXIMAL_CONSISTENT {} p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     Box q SUBFORMULA p
     ==> ((!x. K_STANDARD_REL p w x ==> MEM q x) <=> MEM (Box q) w)`;;
e (REPEAT GEN_TAC);;
e (REPEAT GEN_TAC THEN INTRO_TAC "p maxM maxw boxq");;
e (EQ_TAC);;
  r (1);;
  e (ASM_MESON_TAC[K_STANDARD_REL_CAR]);;
e (ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM]);;
e (INTRO_TAC "asd");;
e (REWRITE_TAC[NOT_FORALL_THM]);;
e (REWRITE_TAC[MESON[]`~(p ==> q) <=> (p /\ ~q)`]);;
e (REWRITE_TAC[K_STANDARD_REL_CAR]);;
e (CLAIM_TAC "consistent_X"
     `CONSISTENT {} (CONS (Not q)
                          (FLATMAP (\x. match x with Box c -> [c] | _ -> [])
                                   w))`);;
  e (REFUTE_THEN MP_TAC);;
  e (INTRO_TAC "PA");;
  e (SUBGOAL_THEN `MEM (Box q) w ==> F` (fun(th) -> (MATCH_MP_TAC th)));;
    e (ASM_MESON_TAC[]);;
  e (REMOVE_THEN "PA" MP_TAC THEN REWRITE_TAC[CONSISTENT]);;
  e (INTRO_TAC "PA");;
  e (SUBGOAL_THEN
      `[{} . {}
        |~ CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
           --> Box q] /\
       (!c. MEM c (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)
            ==> MEM (Box c) w ) /\
       Box q SUBSENTENCE p
       ==> MEM (Box q) w`
      (fun th -> MATCH_MP_TAC th));;
    e (REPEAT STRIP_TAC);;
    e (MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA);;
    e (EXISTS_TAC `{}:form->bool`);;
    e (MAP_EVERY EXISTS_TAC[`p:form`;
         `FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w`]);;
    e (ASM_REWRITE_TAC[MEM_FLATMAP_LEMMA_1]);;
  e (ASM IMP_REWRITE_TAC[MEM_FLATMAP_LEMMA; SUBFORMULA_IMP_SUBSENTENCE]);;
  e (MATCH_MP_TAC MLK_imp_trans);;
  e (EXISTS_TAC
      `CONJLIST (MAP (Box)
                     (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w))`);;
  e (REWRITE_TAC[CONJLIST_FLATMAP_DOT_BOX_LEMMA]);;
  e (MATCH_MP_TAC MKL_CONJLIST_BOX_IMP_BOX);;
  e (REMOVE_THEN "PA" MP_TAC);;
  e (REWRITE_TAC[MLK_not_def]);;
  e (REWRITE_TAC[CONJLIST_CONS_NOT_TH]);;
  e (MESON_TAC[K_NOT_IMP_ID_5]);;
e (MP_TAC (SPECL
              [`{}:form->bool`; `p:form`;
               `CONS (Not q)
                     (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)`]
              EXTEND_MAXIMAL_CONSISTENT));;
e (ANTS_TAC);;
  e (ASM_REWRITE_TAC[MEM]);;
  e (GEN_TAC THEN STRIP_TAC);;
  e (FIRST_X_ASSUM SUBST_VAR_TAC);;
  e (MATCH_MP_TAC SUBFORMULA_IMP_NEG_SUBSENTENCE);;
  e (HYP MESON_TAC "boxq"
        [SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
e (CLAIM_TAC "boxq'" `MEM (Box q') (w:(form)list)`);;
  e (MATCH_MP_TAC MEM_FLATMAP_LEMMA);;
  e (ASM_REWRITE_TAC[]);;
e (CLAIM_TAC "boxq'sub" `Box (q':form) SUBSENTENCE p`);;
  e (ASM_MESON_TAC[]);;
e (HYP_TAC "boxq'sub" (REWRITE_RULE[SUBSENTENCE_CASES; distinctness "form"]));;
e (MATCH_MP_TAC SUBFORMULA_IMP_SUBSENTENCE);;
e (HYP MESON_TAC "boxq'sub"
    [SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
e (INTRO_TAC "@X. maxX subX subl" THEN EXISTS_TAC `X:form list`);;
e (ASM_REWRITE_TAC[K_STANDARD_REL_CAR; NOT_IMP]);;
e (CONJ_TAC);;
  e (INTRO_TAC "!B; B");;
  e (HYP_TAC "subl" (REWRITE_RULE[SUBLIST]));;
  e (REMOVE_THEN "subl" MATCH_MP_TAC);;
  e (REWRITE_TAC[MEM; distinctness "form"; injectivity "form"]);;
  e (DISJ2_TAC THEN REWRITE_TAC[MEM_FLATMAP]);;
  e (EXISTS_TAC `Box B`);;
  e (ASM_REWRITE_TAC[MEM]);;
e (HYP_TAC "subl" (REWRITE_RULE[SUBLIST]));;
e (HYP_TAC "subl: +" (SPEC `Not q` o REWRITE_RULE[SUBLIST]));;
e (IMP_REWRITE_TAC[GSYM MAXIMAL_CONSISTENT_MEM_NOT]);;
e (STRIP_TAC);;
e (CONJ_TAC);;
  r 1;;
  e (MATCH_MP_TAC SUBFORMULA_TRANS);;
  e (EXISTS_TAC `Box (q:form)`);;
  e (ASM_REWRITE_TAC[]);;
  e (ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
r 1;;
e (REMOVE_THEN "" MATCH_MP_TAC THEN REWRITE_TAC[MEM]);;
let K_ACCESSIBILITY_LEMMA = top_thm();;

g `!p w q.
    ~ [{} . {} |~ p] /\
    MAXIMAL_CONSISTENT {} p w /\
    (!q. MEM q w ==> q SUBSENTENCE p) /\
    Box q SUBFORMULA p /\
    (!x. K_STANDARD_REL p w x ==> MEM q x)
    ==> MEM (Box q) w`;;
e (REPEAT STRIP_TAC);;
e (REMOVE_THEN "" MP_TAC);;
e (MATCH_MP_TAC EQ_IMP);;
e (MATCH_MP_TAC K_ACCESSIBILITY_LEMMA);;
e (ASM_REWRITE_TAC[]);;
let K_ACCESSIBILITY_LEMMA_1 = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Modal completeness theorem for K.                                         *)
(* ------------------------------------------------------------------------- *)

g `!M p.
     ~ [{} . {} |~ p] /\
     MAXIMAL_CONSISTENT {} p M /\
     MEM (Not p) M /\
     (!q. MEM q M ==> q SUBSENTENCE p)
     ==> ~holds ({M | MAXIMAL_CONSISTENT {} p M /\
                      (!q. MEM q M ==> q SUBSENTENCE p)},
                 K_STANDARD_REL p)
                (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
                p M`;;
e (REPEAT GEN_TAC THEN STRIP_TAC);;
e (MP_TAC (ISPECL
    [`{M | MAXIMAL_CONSISTENT {} p M /\ (!q. MEM q M ==> q SUBSENTENCE p)}`;
     `K_STANDARD_REL p`;
     `p:form`;
     `\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w`;
     `p:form`] K_TRUTH_LEMMA));;
  e ANTS_TAC;;
  e (ASM_REWRITE_TAC[SUBFORMULA_REFL; K_STANDARD_MODEL_CAR;
                     IN_K_STANDARD_FRAME]);;
  e (ASM_SIMP_TAC[K_MAXIMAL_CONSISTENT]);;
  e (REWRITE_TAC[IN_ELIM_THM]);;
  e CONJ_TAC;;
    e (INTRO_TAC "!q w; boxq w subf");;
    e EQ_TAC;;
      e (ASM_MESON_TAC[K_ACCESSIBILITY_LEMMA]);;
    e (INTRO_TAC "hp");;
    e (MATCH_MP_TAC K_ACCESSIBILITY_LEMMA_1);;
    e (EXISTS_TAC `p:form`);;
    e (ASM_REWRITE_TAC[]);;
  e (ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT_NC]);;
e (DISCH_THEN (MP_TAC o SPEC `M:form list`));;
e ANTS_TAC;;
e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (DISCH_THEN (SUBST1_TAC o GSYM));;
e (ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT_NC]);;
let K_COUNTERMODEL = top_thm();;

g `!p. ~ [{} . {} |~ p]
       ==> ~holds_in ({M | MAXIMAL_CONSISTENT {} p M /\
                           (!q. MEM q M ==> q SUBSENTENCE p)},
                       K_STANDARD_REL p)
                     p`;;
e (INTRO_TAC "!p; Np");;
e (REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP; IN_ELIM_THM]);;
e (EXISTS_TAC `\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w`);;
e (DESTRUCT_TAC "@M. max mem subf"
      (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~([{} . {} |~ p])`)));;
e (EXISTS_TAC `M:form list`);;
e (ASM_REWRITE_TAC[]);;
e (MATCH_MP_TAC K_COUNTERMODEL);;
e (ASM_REWRITE_TAC[]);;
let LEMMA_K_COUNTER = top_thm();;

g `!p. K_FRAME:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [{} . {} |~ p]`;;
e GEN_TAC;;
e (GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM]);;
e (INTRO_TAC "p");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT {} p M /\
                     (!q. MEM q M ==> q SUBSENTENCE p)},
                K_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP]);;
e CONJ_TAC;;
  e (MATCH_MP_TAC K_MAXIMAL_CONSISTENT);;
  e (ASM_REWRITE_TAC[]);;
e (MATCH_MP_TAC LEMMA_K_COUNTER);;
e (ASM_REWRITE_TAC[]);;
let K_COMPLETENESS_THM = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Modal completeness for K for models on a generic (infinite) domain.      *)
(* ------------------------------------------------------------------------- *)

g `!p. INFINITE (:A) /\ K_FRAME:(A->bool)#(A->A->bool)->bool |= p
       ==> [{} . {} |~ p]`;;
e (SUBGOAL_THEN
    `INFINITE (:A)
     ==> !p. K_FRAME:(A->bool)#(A->A->bool)->bool |= p
             ==> K_FRAME:(form list->bool)#(form list->form list->bool)->bool
                 |= p`
    (fun th -> MESON_TAC[th; K_COMPLETENESS_THM]) THEN
  INTRO_TAC "A" THEN MATCH_MP_TAC BISIMILAR_VALID THEN
  REPEAT GEN_TAC THEN INTRO_TAC "K_FRAME w1" THEN
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
   `f (w1:form list):A`]);;
e (REWRITE_TAC[IN_K_FRAME]);;
e CONJ_TAC;;
  e CONJ_TAC;;
    e (HYP SET_TAC "w1" []);;
  e CONJ_TAC;;
    e (SET_TAC[]);;
  e (ASM_MESON_TAC[IN_K_FRAME; FINITE_IMAGE]);;
e (REWRITE_TAC[BISIMILAR] THEN
   EXISTS_TAC `\w1:form list w2:A. w1 IN W1 /\ w2 = f w1` THEN
   ASM_REWRITE_TAC[BISIMIMULATION] THEN REMOVE_THEN "w1" (K ALL_TAC) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
   ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
   CONJ_TAC THENL [HYP MESON_TAC "inj" []; ALL_TAC] THEN
   CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[IN_K_FRAME];
    ALL_TAC] THEN
   ASM_MESON_TAC[]);;
let K_COMPLETENESS_THM_GEN = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Simple decision procedure for K.                                          *)
(* ------------------------------------------------------------------------- *)

let K_TAC : tactic =
  MATCH_MP_TAC K_COMPLETENESS_THM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in; holds;
              IN_K_FRAME; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[];;

let K_RULE tm =
  prove(tm, REPEAT GEN_TAC THEN K_TAC);;

K_RULE `!p q r. [{} . {} |~ (Not p --> q --> r) <->
                            ((p --> False) --> q --> r)]`;;

K_RULE `!p. [{} . {} |~ (p --> False) --> False <-> p]`;;

K_RULE `!p q. [{} . {} |~ Not (p && q) <-> Not p || Not q]`;;

(* ------------------------------------------------------------------------- *)
(* Countermodel using set of formulae (instead of lists of formulae).        *)
(* ------------------------------------------------------------------------- *)

let K_STDWORLDS_RULES,K_STDWORLDS_INDUCT,K_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT {} p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN K_STDWORLDS p`;;

let K_STDREL_RULES,K_STDREL_INDUCT,K_STDREL_CASES = new_inductive_definition
  `!w1 w2. K_STANDARD_REL p w1 w2
           ==> K_STDREL p (set_of_list w1) (set_of_list w2)`;;

let K_STDREL_IMP_K_STDWORLDS = prove
 (`!p w1 w2. K_STDREL p w1 w2 ==>
             w1 IN K_STDWORLDS p /\
             w2 IN K_STDWORLDS p`,
  GEN_TAC THEN MATCH_MP_TAC K_STDREL_INDUCT THEN
  REWRITE_TAC[K_STANDARD_REL_CAR] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC K_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;

g `!p. BISIMIMULATION
       ({M | MAXIMAL_CONSISTENT {} p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
         K_STANDARD_REL p,
         (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w))
       (K_STDWORLDS p,
        K_STDREL p,
        (\a w. Atom a SUBFORMULA p /\ Atom a IN w))
       (\w1 w2.
          MAXIMAL_CONSISTENT {} p w1 /\
          (!q. MEM q w1 ==> q SUBSENTENCE p) /\
          w2 IN K_STDWORLDS p /\
          set_of_list w1 = w2)`;;
e (GEN_TAC THEN REWRITE_TAC[BISIMIMULATION] THEN REPEAT GEN_TAC THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC[IN_SET_OF_LIST];
    ALL_TAC] THEN
   CONJ_TAC);;
e (INTRO_TAC "![u1]; w1u1" THEN EXISTS_TAC `set_of_list u1:form->bool` THEN
   HYP_TAC "w1u1 -> hp" (REWRITE_RULE[K_STANDARD_REL_CAR]) THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC K_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC K_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN MATCH_MP_TAC K_STDREL_RULES THEN
   ASM_REWRITE_TAC[]);;
e (INTRO_TAC "![u2]; w2u2" THEN EXISTS_TAC `list_of_set u2:form list` THEN
   REWRITE_TAC[CONJ_ACI] THEN
   HYP_TAC "w2u2 -> @x2 y2. x2 y2 x2y2" (REWRITE_RULE[K_STDREL_CASES]) THEN
   REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   SIMP_TAC[SET_OF_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   SIMP_TAC[MEM_LIST_OF_SET; FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
   CONJ_TAC THENL
   [HYP_TAC "x2y2 -> hp" (REWRITE_RULE[K_STANDARD_REL_CAR]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC);;
e (ASM_MESON_TAC[K_STDREL_IMP_K_STDWORLDS]);;
e CONJ_TAC;;
e (ASM_REWRITE_TAC[K_STANDARD_REL_DEF]);;
e (MATCH_MP_TAC SET_OF_LIST_EQ_STANDARD_REL THEN
   EXISTS_TAC `x2:form list` THEN EXISTS_TAC `y2:form list` THEN
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT; K_STANDARD_REL_DEF]);;
e (MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT  THEN
  EXISTS_TAC `y2:form list` THEN
   SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   ASM_MESON_TAC[K_STANDARD_REL_CAR]);;
let K_BISIMIMULATION_SET_OF_LIST = top_thm();;

let K_COUNTERMODEL_FINITE_SETS = prove
  (`!p. ~[{} . {} |~ p] ==> ~holds_in (K_STDWORLDS p, K_STDREL p) p`,
   INTRO_TAC "!p; p" THEN
   DESTRUCT_TAC "@M. max mem subf"
     (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ [{} . {} |~ p]`)) THEN
   REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP] THEN
   ASSUM_LIST (LABEL_TAC "hp" o MATCH_MP K_COUNTERMODEL o
                 end_itlist CONJ o rev) THEN
   EXISTS_TAC `\a w. Atom a SUBFORMULA p /\ Atom a IN w` THEN
   EXISTS_TAC `set_of_list M:form->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC K_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REMOVE_THEN "hp" MP_TAC THEN
   MATCH_MP_TAC (MESON[] `(p <=> q) ==> (~p ==> ~q)`) THEN
   MATCH_MP_TAC BISIMIMULATION_HOLDS THEN
   EXISTS_TAC
       `\w1 w2.
          MAXIMAL_CONSISTENT {} p w1 /\
          (!q. MEM q w1 ==> q SUBSENTENCE p) /\
          w2 IN K_STDWORLDS p /\
          set_of_list w1 = w2` THEN
   ASM_REWRITE_TAC[K_BISIMIMULATION_SET_OF_LIST] THEN
   MATCH_MP_TAC K_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;
