(* ========================================================================= *)
(* Proof of the consistency and modal completeness of B.                     *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

needs "HOLMS/gen_completeness.ml";;

let B_AX = new_definition
  `B_AX = {B_SCHEMA p | p IN (:form)} UNION {T_SCHEMA p |p IN (:form)}`;;

let B_IN_B_AX = prove
 (`!q. p -->  Box Diam p IN B_AX`,
  REWRITE_TAC[B_AX; B_SCHEMA_DEF; T_SCHEMA_DEF; IN_ELIM_THM;
              IN_UNIV; IN_UNION] THEN
  MESON_TAC[]);;

let T_IN_B_AX = prove
 (`!q. Box q -->  q IN B_AX`,
  REWRITE_TAC[B_AX; B_SCHEMA_DEF; T_SCHEMA_DEF; IN_ELIM_THM;
              IN_UNIV; UNION] THEN
  MESON_TAC[]);;

let B_AX_B= prove
 (`!q. [B_AX. {} |~ (q --> Box Diam q)]`,
  MESON_TAC[MODPROVES_RULES; B_IN_B_AX]);;

let B_AX_T = prove
 (`!q. [B_AX. {} |~ (Box q --> q)]`,
  MESON_TAC[MODPROVES_RULES; T_IN_B_AX]);;

(* ------------------------------------------------------------------------- *)
(* Reflexive-Symmetric frames.                                               *)
(* ------------------------------------------------------------------------- *)

let RSYM_DEF = new_definition
  `RSYM =
   {(W:W->bool,R:W->W->bool) |
    (W,R) IN FRAME /\
    REFLEXIVE W R /\
    SYMMETRIC W R}`;;
    
let IN_RSYM = prove
 (`(W:W->bool,R:W->W->bool) IN RSYM <=>
   (W,R) IN FRAME /\
    REFLEXIVE W R /\
    SYMMETRIC W R`,
  REWRITE_TAC[RSYM_DEF; IN_ELIM_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory: Refl-Symmetric Frames are characteristic for B.    *)
(* ------------------------------------------------------------------------- *)

g `RSYM:(W->bool)#(W->W->bool)->bool = CHAR B_AX`;;
e (REWRITE_TAC[EXTENSION; FORALL_PAIR_THM]);;
e (REWRITE_TAC[IN_CHAR; IN_RSYM]);;
e (REWRITE_TAC[B_AX; FORALL_IN_UNION; FORALL_IN_GSPEC; MODAL_REFL; MODAL_SYM; IN_UNIV]);;
e (MESON_TAC[]);;
let RSYM_CHAR_B = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. Reflexive-Symmetric Frames                      *)
(* ------------------------------------------------------------------------- *)

let B_RSYM_VALID = prove
 (`!H p. [B_AX . H |~ p] /\
         (!q. q IN H ==> RSYM:(W->bool)#(W->W->bool)->bool |= q)
         ==> RSYM:(W->bool)#(W->W->bool)->bool |= p`,
  ASM_MESON_TAC[GEN_CHAR_VALID; RSYM_CHAR_B]);;

(* ------------------------------------------------------------------------- *)
(* Finite Reflexive-Symmetric Frames are appropriate for B.                  *)
(* ------------------------------------------------------------------------- *)

let RSF_DEF = new_definition
 `RSF =
  {(W:W->bool,R:W->W->bool) |
   (W,R) IN FINITE_FRAME /\
    REFLEXIVE W R /\
    SYMMETRIC W R}`;;

let IN_RSF = prove
 (`(W:W->bool,R:W->W->bool) IN RSF <=>
   (W,R) IN FINITE_FRAME /\
    REFLEXIVE W R /\
    SYMMETRIC W R`,
  REWRITE_TAC[RSF_DEF; IN_ELIM_PAIR_THM]);;

let RSF_SUBSET_RSYM = prove
 (`RSF:(W->bool)#(W->W->bool)->bool SUBSET RSYM`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_RSF; IN_FINITE_FRAME; REFLEXIVE;
              TRANSITIVE; IN_RSYM; IN_FRAME] THEN MESON_TAC[]);;

let RSF_FIN_RSYM = prove
 (`RSF:(W->bool)#(W->W->bool)->bool = (RSYM INTER FINITE_FRAME)`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN 
  REWRITE_TAC[IN_INTER; IN_RSF; IN_FINITE_FRAME; TRANSITIVE; REFLEXIVE;
              IN_RSYM; IN_FRAME] THEN
  MESON_TAC[FINITE_FRAME_SUBSET_FRAME; SUBSET]);;

g `RSF: (W->bool)#(W->W->bool)->bool = APPR B_AX`;;
e (REWRITE_TAC[EXTENSION; FORALL_PAIR_THM]);;
e (REWRITE_TAC[APPR_CAR; RSF_FIN_RSYM]);;
e (REWRITE_TAC[RSYM_CHAR_B; IN_INTER; IN_CHAR; IN_FINITE_FRAME_INTER]);;
e (MESON_TAC[]);;
let RSF_APPR_B = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. RSF.                                            *)
(* ------------------------------------------------------------------------- *)

let B_RSF_VALID = prove
 (`!p. [B_AX . {} |~ p] ==> RSF:(W->bool)#(W->W->bool)->bool |= p`,
  MESON_TAC[GEN_APPR_VALID; RSF_APPR_B]);;

(* ------------------------------------------------------------------------- *)
(* Proof of Consistency of B.                                                *)
(* ------------------------------------------------------------------------- *)

let B_CONSISTENT = prove
 (`~ [B_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] B_RSF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM; IN_RSF;
              IN_FINITE_FRAME; REFLEXIVE; SYMMETRIC; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. x = 0 /\ x = y`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* B standard frames and models.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Standard Frame.                                                           *)
(* ------------------------------------------------------------------------- *)

let B_STANDARD_FRAME_DEF = new_definition
  `B_STANDARD_FRAME p = GEN_STANDARD_FRAME B_AX p`;;

let IN_B_STANDARD_FRAME = prove
  (`!p W R. (W,R) IN B_STANDARD_FRAME p <=>
            W = {w | MAXIMAL_CONSISTENT B_AX p w /\
                     (!q. MEM q w ==> q SUBSENTENCE p)} /\
            (W,R) IN RSF /\
            (!q w. Box q SUBFORMULA p /\ w IN W
                   ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`,
 REPEAT GEN_TAC THEN
 REWRITE_TAC[B_STANDARD_FRAME_DEF; IN_GEN_STANDARD_FRAME] THEN
 EQ_TAC THEN MESON_TAC[RSF_APPR_B]);;

(* ------------------------------------------------------------------------- *)
(* Standard model.                                                           *)
(* ------------------------------------------------------------------------- *)

let B_STANDARD_MODEL_DEF = new_definition
  `B_STANDARD_MODEL = GEN_STANDARD_MODEL B_AX`;;

let B_STANDARD_MODEL_CAR = prove
 (`!W R p V.
     B_STANDARD_MODEL p (W,R) V <=>
     (W,R) IN B_STANDARD_FRAME p /\
     (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[B_STANDARD_MODEL_DEF; GEN_STANDARD_MODEL_DEF] THEN
  REWRITE_TAC[IN_B_STANDARD_FRAME; IN_GEN_STANDARD_FRAME] THEN
  EQ_TAC THEN ASM_MESON_TAC[RSF_APPR_B]);;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let B_TRUTH_LEMMA = prove
 (`!W R p V q.
     ~ [B_AX . {} |~ p] /\
     B_STANDARD_MODEL p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REWRITE_TAC[B_STANDARD_MODEL_DEF] THEN MESON_TAC[GEN_TRUTH_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Accessibility lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let B_STANDARD_REL_DEF = new_definition
  `B_STANDARD_REL p w x <=>
   GEN_STANDARD_REL B_AX p w x /\
   (!B. MEM (Box B) x ==> MEM B w)`;;

let B_STANDARD_REL_CAR = prove
 (`!p w x.
     B_STANDARD_REL p w x <=>
     MAXIMAL_CONSISTENT B_AX p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT B_AX p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
     (!B. MEM (Box B) w ==> MEM B x) /\
     (!B. MEM (Box B) x ==> MEM B w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[B_STANDARD_REL_DEF; GEN_STANDARD_REL] THEN
  EQ_TAC THEN REPEAT (ASM_MESON_TAC[]) THEN REPEAT (ASM_MESON_TAC[]));;

let RSF_MAXIMAL_CONSISTENT = prove
 (`!p. ~ [B_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT B_AX p M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)},
            B_STANDARD_REL p)
           IN RSF `,
  INTRO_TAC "!p; p" THEN
  MP_TAC (ISPECL [`B_AX`; `p:form`] GEN_FINITE_FRAME_MAXIMAL_CONSISTENT) THEN
  REWRITE_TAC[IN_FINITE_FRAME] THEN INTRO_TAC "gen_max_cons" THEN
  ASM_REWRITE_TAC[IN_RSF; IN_FINITE_FRAME; REFLEXIVE; SYMMETRIC] THEN
  CONJ_TAC THENL
  (* Nonempty *)
  [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Well-defined *)
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[B_STANDARD_REL_DEF] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Finite *)
  ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Reflexive *)
  CONJ_TAC THENL [REWRITE_TAC[IN_ELIM_THM; B_STANDARD_REL_CAR] THEN
  INTRO_TAC "!w; (max_cons) (imp)" THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN INTRO_TAC "box_mem" THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA THEN
  EXISTS_TAC `B_AX` THEN EXISTS_TAC `p:form` THEN EXISTS_TAC `[Box B]` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [ASM_REWRITE_TAC[MEM] THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC]  THEN
  CLAIM_TAC "d" `B SUBFORMULA Box B` THENL
  [ASM_REWRITE_TAC[SUBFORMULA_INVERSION; SUBFORMULA_REFL]; ALL_TAC] THEN
  CONJ_TAC THENL
  [CLAIM_TAC "c" `Box B SUBSENTENCE p` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   HYP_TAC "c" (REWRITE_RULE[SUBSENTENCE_CASES]) THEN
   DISJ_CASES_TAC (ASSUME `Box B SUBFORMULA p \/
                           (?p'. Box B = Not p' /\ p' SUBFORMULA p)`) THENL
   [ASM_MESON_TAC[SUBFORMULA_TRANS]; ALL_TAC] THEN
   CLAIM_TAC "@y. e" `?p'. Box B = Not p' /\ p' SUBFORMULA p` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `~(Box B = Not y)` MP_TAC THENL
   [ASM_MESON_TAC[form_DISTINCT]; ALL_TAC] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[CONJLIST] THEN ASM_MESON_TAC[B_AX_T]; ALL_TAC] THEN
  (* Symmetric *)
  REWRITE_TAC[IN_ELIM_THM; B_STANDARD_REL_CAR] THEN
  INTRO_TAC "!w w'; (x1 x2) (y1 y2) +"  THEN
  ASM_REWRITE_TAC[B_STANDARD_REL_CAR] THEN
  MESON_TAC[] );;

g `!p w q.
     ~ [B_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT B_AX p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     Box q SUBFORMULA p /\
     (!x. B_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`;;
e (INTRO_TAC "!p w q; p  maxw subw boxq rrr");;
e (REFUTE_THEN (LABEL_TAC "contra") THEN
  REMOVE_THEN "rrr" MP_TAC THEN REWRITE_TAC[NOT_FORALL_THM]);;
e (CLAIM_TAC "consistent_X"
    `CONSISTENT B_AX
       (CONS (Not q)
          (APPEND (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)
                  (FLATMAP (\x. match x with
                                | Not e ->
                                    if Box e SUBSENTENCE p
                                    then [Not Box e]
                                    else []
                                | _ -> []) w)))`);;
  e (REMOVE_THEN "contra" MP_TAC);;
  e (REWRITE_TAC[CONSISTENT; CONTRAPOS_THM]);;
  e (INTRO_TAC "incons" THEN MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA);;
  e (MAP_EVERY EXISTS_TAC
       [`B_AX`;
        `p:form`;
        `APPEND (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
                (FLATMAP (\x. match x with
                              | Not e ->
                                  if Box e SUBSENTENCE p
                                  then [Not e]
                                  else []
                              | _ -> []) w) `]);;
  e (ASM_REWRITE_TAC[]);;
  e CONJ_TAC;;
   e GEN_TAC;;
    e (ASM_REWRITE_TAC[MEM_APPEND]);;
    e (ASM_REWRITE_TAC[MEM_FLATMAP_LEMMA_2; MEM_FLATMAP_LEMMA_4] THEN
       ASM_MESON_TAC[]);;
   e (MATCH_MP_TAC MLK_imp_trans);;
    e (EXISTS_TAC
        `CONJLIST
           (APPEND (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
                   (FLATMAP (\x. match x with
                                 | Not e ->
                                     if Box e SUBSENTENCE p
                                     then [Box Not Box e]
                                     else []
                                 | _ -> []) w))`);;
    e CONJ_TAC;;
     e (MATCH_MP_TAC (CONJLIST_IMP_CONJLIST));;
      e GEN_TAC;;
      e (ASM_REWRITE_TAC[MAP_APPEND; MEM_APPEND; MEM_MAP;
          MEM_FLATMAP_LEMMA_4; MEM_FLATMAP_LEMMA_5]);;
       e STRIP_TAC;;
        e (EXISTS_TAC `p':form`);;
         e (ASM_REWRITE_TAC[MLK_imp_refl_th]);;
        e (EXISTS_TAC `Not r:form`);;
         e CONJ_TAC;;
          e DISJ2_TAC;;
           e (EXISTS_TAC `r:form`);;
           e (ASM_REWRITE_TAC[]);;
          e (ASM_REWRITE_TAC[]);;
          e (MP_TAC (ISPECL [`Not r`] B_AX_B));;
          e (MESON_TAC[diam_DEF; MLK_not_subst; MLK_box_subst; MLK_not_not_th;
                       MLK_imp_mp_subst; MLK_iff_refl_th]);;
     e (MATCH_MP_TAC MLK_iff_mp);;
     e (EXISTS_TAC
         `CONJLIST
            (MAP (Box)
                 (APPEND (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)
                         (FLATMAP (\x. match x with
                                       | Not e ->
                                           if Box e SUBSENTENCE p
                                           then [Not Box e]
                                           else []
                                       | _ -> []) w)))
            --> Box q`);;
     e CONJ_TAC;;
      e (MATCH_MP_TAC MLK_imp_subst);;
       e (ASM_REWRITE_TAC[MLK_iff_refl_th]);;
       e (MATCH_MP_TAC MLK_iff_mp_subst);;
       e (EXISTS_TAC
           `CONJLIST
              (APPEND (MAP (Box)
                        (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w))
                      (MAP (Box) (FLATMAP (\x. match x with
                                               | Not e ->
                                                   if Box e SUBSENTENCE p
                                                   then [Not Box e]
                                                   else []
                                               | _ -> []) w)))`);;
       e (EXISTS_TAC
           `CONJLIST
              (APPEND (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
                      (FLATMAP (\x. match x with
                                    | Not e ->
                                        if Box e SUBSENTENCE p
                                        then [Box Not Box e]
                                        else []
                                    | _ -> []) w))`);;
       e (ASM_REWRITE_TAC[ MLK_iff_refl_th]);;
       e CONJ_TAC;;
        e (ASM_MESON_TAC[MLK_iff_sym; APPEND_MAP_BOX]);;
         e (ASM_REWRITE_TAC[MLK_iff_def]);;
         e CONJ_TAC;;
          e (MATCH_MP_TAC CONJLIST_IMP_CONJLIST);;
           e (ASM_REWRITE_TAC[MEM_APPEND; MEM_FLATMAP_LEMMA_6;
                MEM_FLATMAP_LEMMA_5; MEM_FLATMAP_LEMMA_2; MEM_MAP; FLATMAP]);;
           e (REPEAT STRIP_TAC);;
            e (EXISTS_TAC `Box q'`);;
             e CONJ_TAC;;
              e DISJ1_TAC;;
               e (EXISTS_TAC `q': form`);;
               e (ASM_MESON_TAC[MEM_FLATMAP_LEMMA_1]);;
              e (ASM_REWRITE_TAC[MLK_imp_refl_th]);;
            e (EXISTS_TAC `Box Not Box r`);;
             e CONJ_TAC;;
              e DISJ2_TAC;;
               e (EXISTS_TAC `Not Box r`);;
               e (ASM_REWRITE_TAC[]);;
               e (EXISTS_TAC `r: form`);;
               e (ASM_REWRITE_TAC[]);;
              e (ASM_REWRITE_TAC[MLK_imp_refl_th]);;
          e (MATCH_MP_TAC CONJLIST_IMP_CONJLIST);;
           e (ASM_REWRITE_TAC[MEM_APPEND; MEM_FLATMAP_LEMMA_6;
                MEM_FLATMAP_LEMMA_5; MEM_FLATMAP_LEMMA_2; MEM_MAP; FLATMAP]);;
           e (REPEAT STRIP_TAC);;
            e (EXISTS_TAC `Box x`);;
             e CONJ_TAC;;
              e DISJ1_TAC;;
               e (EXISTS_TAC `x: form`);;
               e (ASM_MESON_TAC[MEM_FLATMAP_LEMMA]);;
              e (ASM_REWRITE_TAC[MLK_imp_refl_th]);;
            e (EXISTS_TAC `Box Not Box r:form`);;
             e CONJ_TAC;;
              e DISJ2_TAC;;
               e (EXISTS_TAC `r:form`);;
               e (ASM_REWRITE_TAC[]);;
              e (ASM_REWRITE_TAC[MLK_imp_refl_th]);;
         e (CLAIM_TAC "XIMP"
              `!y l. [B_AX . {} |~ Not (Not y && CONJLIST l)]
                     ==> [B_AX . {} |~ (CONJLIST (MAP (Box) l)) --> Box(y)]`);;
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
              e (MESON_TAC[MLK_axiom_not; MLK_iff_imp2]);;
              e (MESON_TAC[MLK_imp_refl_th]);;
        e (POP_ASSUM MATCH_MP_TAC);;
        e (HYP_TAC "incons" (ONCE_REWRITE_RULE[CONJLIST]));;
        e (POP_ASSUM MP_TAC);;
        e (COND_CASES_TAC);;
        e (ASM_REWRITE_TAC[MLK_DOUBLENEG]);;
        e (INTRO_TAC "notnotq");;
        e (ASM_REWRITE_TAC[CONJLIST]);;
        e (ASM_MESON_TAC[MLK_iff_mp; MLK_not_subst; MLK_and_left_true_th;
             MLK_iff_refl_th; MLK_iff_mp_subst; MLK_and_comm_th;
             MLK_iff_sym; MLK_and_left_true_th]);;
      e (ASM_REWRITE_TAC[]);;
e (MP_TAC (SPECL
    [`B_AX`;
     `p:form`;
     `CONS (Not q)
           (APPEND (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)
                   (FLATMAP (\x. match x with
                                 | Not e ->
                                     if Box e SUBSENTENCE p
                                     then [Not Box e]
                                     else []
                                 | _ -> []) w))`]
    EXTEND_MAXIMAL_CONSISTENT));;
e ANTS_TAC;;
 e (ASM_REWRITE_TAC[MEM] THEN GEN_TAC THEN STRIP_TAC THEN
     REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC));;
  e (MATCH_MP_TAC SUBFORMULA_IMP_NEG_SUBSENTENCE);;
  e (HYP MESON_TAC "boxq"
       [SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
  e (UNDISCH_TAC `MEM q'
      (APPEND (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)
              (FLATMAP (\x. match x with
                            | Not e ->
                                if Box e SUBSENTENCE p
                                then [Not Box e]
                                else []
                             | _ -> []) w))`);;
  e (REWRITE_TAC[MEM_APPEND; MEM_FLATMAP_LEMMA_6]);;
  e (STRIP_TAC);;
  e (CLAIM_TAC "mem_flatmap" `MEM (Box q') w`);;
    e (ASM_MESON_TAC[MEM_FLATMAP_LEMMA]);;
  e (SUBGOAL_THEN `(Box q') SUBSENTENCE p:form` MP_TAC);;
    e (POP_ASSUM MP_TAC);;
    e (ASM_REWRITE_TAC[]);;
  e (REWRITE_TAC[SUBSENTENCE_CASES]);;
  e STRIP_TAC;;
   e DISJ1_TAC;;
    e (MATCH_MP_TAC SUBFORMULA_TRANS);;
    e (EXISTS_TAC `Box q'`);;
    e (ASM_REWRITE_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION;
                       SUBFORMULA_REFL]);;
   e (REFUTE_THEN MP_TAC);;
    e (ASM_MESON_TAC[form_DISTINCT]);;
  e (UNDISCH_TAC `Box r SUBSENTENCE p`);;
   e (ASM_REWRITE_TAC[SUBSENTENCE_CASES]);;
   e STRIP_TAC;;
    e DISJ2_TAC;;
     e (EXISTS_TAC `Box r`);;
     e (ASM_REWRITE_TAC[]);;
    e (REFUTE_THEN MP_TAC);;
    e (ASM_MESON_TAC[form_DISTINCT]);;
e (INTRO_TAC "@X. maxX subX subl");;
 e (EXISTS_TAC `X:form list`);;
 e (ASM_REWRITE_TAC[NOT_IMP]);;
 e (ASM_REWRITE_TAC[B_STANDARD_REL_CAR]);;
 e CONJ_TAC;;
  e (HYP_TAC "subl" (REWRITE_RULE[SUBLIST; MEM; MEM_APPEND;
                      MEM_FLATMAP_LEMMA_6; MEM_FLATMAP_LEMMA_A]));;
   e CONJ_TAC;;
    e (REPEAT STRIP_TAC);;
     e (ASM_MESON_TAC[]);;
    e (REPEAT STRIP_TAC);;
     e (REFUTE_THEN (LABEL_TAC "contra"));;
     e (CLAIM_TAC "contra_mem" `MEM (Not B) w`);;
       e (CLAIM_TAC "contra_sub" `B SUBFORMULA p`);;
         e (SUBGOAL_THEN `Box B SUBSENTENCE p` MP_TAC);;
           e (ASM_MESON_TAC[]);;
         e (REWRITE_TAC[SUBSENTENCE_CASES]);;
         e STRIP_TAC;;
          e (MATCH_MP_TAC SUBFORMULA_TRANS);;
           e (EXISTS_TAC `Box B`);;
           e (ASM_REWRITE_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION;
                              SUBFORMULA_REFL]);;
          e (REFUTE_THEN MP_TAC);;
           e (ASM_MESON_TAC[form_DISTINCT]);;
       e (ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT]);;
  e (ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT; CONSISTENT_LEMMA]);;
  e (HYP_TAC "subl" (REWRITE_RULE[SUBLIST]));;
  e (HYP_TAC "subl: +" (SPEC `Not q:form` o REWRITE_RULE[SUBLIST]));;
  e (IMP_REWRITE_TAC[GSYM MAXIMAL_CONSISTENT_MEM_NOT]);;
   e STRIP_TAC;;
   e CONJ_TAC;;
    r 1;;
     e (MATCH_MP_TAC SUBFORMULA_TRANS);;
     e (EXISTS_TAC `Box (q:form)`);;
     e (ASM_REWRITE_TAC[]);;
     e (ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION;
                      SUBFORMULA_REFL]);;
    r 1;;
     e (REMOVE_THEN "" MATCH_MP_TAC THEN REWRITE_TAC[MEM]);;
let B_ACCESSIBILITY_LEMMA = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Modal completeness theorem for B.                                         *)
(* ------------------------------------------------------------------------- *)

g `!p. ~ [B_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT B_AX p M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)},
            B_STANDARD_REL p)
           IN B_STANDARD_FRAME p`;;
e (INTRO_TAC "!p; not_theor_p");;
e (REWRITE_TAC [IN_B_STANDARD_FRAME]);;
e CONJ_TAC;;
 e (MATCH_MP_TAC RSF_MAXIMAL_CONSISTENT);;
 e (ASM_REWRITE_TAC[]);;
 e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (INTRO_TAC "!q w; boxq maxw subw");;
e EQ_TAC;;
 e (ASM_MESON_TAC[B_STANDARD_REL_CAR]);;
e (ASM_MESON_TAC[B_ACCESSIBILITY_LEMMA]);;
let BF_IN_B_STANDARD_FRAME = top_thm();;

let B_COUNTERMODEL = prove
 (`!M p.
     ~ [B_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT B_AX p M /\
     MEM (Not p) M /\
     (!q. MEM q M ==> q SUBSENTENCE p)
     ==>
     ~holds
        ({M | MAXIMAL_CONSISTENT B_AX p M /\
              (!q. MEM q M ==> q SUBSENTENCE p)},
         B_STANDARD_REL p)
        (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
        p M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC GEN_COUNTERMODEL THEN
  EXISTS_TAC `B_AX` THEN ASM_REWRITE_TAC[GEN_STANDARD_MODEL_DEF] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[BF_IN_B_STANDARD_FRAME; B_STANDARD_FRAME_DEF];
   ALL_TAC] THENL
  [ASM_MESON_TAC[IN_ELIM_THM]]);;

g `!p. RSF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [B_AX . {} |~ p]`;;
e (GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM]);;
e (INTRO_TAC "p_not_theor");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT B_AX p M /\
                     (!q. MEM q M ==> q SUBSENTENCE p)},
                B_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC);;
e (MATCH_MP_TAC RSF_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `({M | MAXIMAL_CONSISTENT B_AX p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
                  B_STANDARD_REL p)
                 IN GEN_STANDARD_FRAME B_AX p`
                MP_TAC);;
 e (ASM_MESON_TAC[BF_IN_B_STANDARD_FRAME; B_STANDARD_FRAME_DEF]);;
e (ASM_MESON_TAC[GEN_COUNTERMODEL_ALT]);;
let B_COMPLETENESS_THM = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* Modal completeness for B for models on a generic (infinite) domain.       *)
(* ------------------------------------------------------------------------- *)

let B_COMPLETENESS_THM_GEN = prove
 (`!p. INFINITE (:A) /\ RSF:(A->bool)#(A->A->bool)->bool |= p
       ==> [B_AX . {} |~ p]`,
  SUBGOAL_THEN
    `INFINITE (:A)
     ==> !p. RSF:(A->bool)#(A->A->bool)->bool |= p
             ==> RSF:(form list->bool)#(form list->form list->bool)->bool |= p`
    (fun th -> MESON_TAC[th; B_COMPLETENESS_THM]) THEN
  ASM_MESON_TAC[RSF_APPR_B; GEN_LEMMA_FOR_GEN_COMPLETENESS]);;

(* ------------------------------------------------------------------------- *)
(* Simple decision procedure for B.                                          *)
(* ------------------------------------------------------------------------- *)

let B_TAC : tactic =
  MATCH_MP_TAC B_COMPLETENESS_THM THEN
  REWRITE_TAC[diam_DEF; valid; FORALL_PAIR_THM; holds_in; holds; IN_RSF;
    IN_FINITE_FRAME; REFLEXIVE; SYMMETRIC; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[];;

let B_RULE tm =
  prove(tm, REPEAT GEN_TAC THEN B_TAC);;

B_RULE `!p q r. [B_AX . {} |~ p && q && r --> p && r]`;;
B_RULE `!p q. [B_AX . {} |~  Box (p --> q) && Box p --> Box q]`;;
B_RULE `!p q. [B_AX . {} |~  Box p --> p]`;;
B_RULE `!p. [B_AX . {} |~  p -->  Box Diam p]`;;
(* B_RULE `!p. [B_AX . {} |~ Box p --> Box (Box p)]`;; *)
(* B_RULE `!p. [B_AX . {} |~ (Box (Box p --> p) --> Box p)]`;; *)
(* B_RULE `!p. [B_AX . {} |~ Box (Box p --> p) --> Box p]`;; *)
(* B_RULE `[B_AX . {} |~ Box (Box False --> False) --> Box False]`;; *)

(* ------------------------------------------------------------------------- *)
(* Countermodel using set of formulae (instead of lists of formulae).        *)
(* ------------------------------------------------------------------------- *)

let B_STDWORLDS_RULES,B_STDWORLDS_INDUCT,B_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT B_AX p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN B_STDWORLDS p`;;

let B_STDREL_RULES,B_STDREL_INDUCT,B_STDREL_CASES = new_inductive_definition
  `!w1 w2. B_STANDARD_REL p w1 w2
           ==> B_STDREL p (set_of_list w1) (set_of_list w2)`;;

let B_STDREL_IMP_B_STDWORLDS = prove
 (`!p w1 w2. B_STDREL p w1 w2 ==>
             w1 IN B_STDWORLDS p /\
             w2 IN B_STDWORLDS p`,
  GEN_TAC THEN MATCH_MP_TAC B_STDREL_INDUCT THEN
  REWRITE_TAC[B_STANDARD_REL_CAR] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC B_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;

let SET_OF_LIST_EQ_B_STANDARD_REL = prove
 (`!p u1 u2 w1 w2.
     set_of_list u1 = set_of_list w1 /\ NOREPETITION w1 /\
     set_of_list u2 = set_of_list w2 /\ NOREPETITION w2 /\
     B_STANDARD_REL p u1 u2
     ==> B_STANDARD_REL p w1 w2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[B_STANDARD_REL_CAR] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]; ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]);;

let B_BISIMIMULATION_SET_OF_LIST = prove
(`!p. BISIMIMULATION
      (
        {M | MAXIMAL_CONSISTENT B_AX p M /\
             (!q. MEM q M ==> q SUBSENTENCE p)},
        B_STANDARD_REL p,
        (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
      )
      (B_STDWORLDS p,
       B_STDREL p,
       (\a w. Atom a SUBFORMULA p /\ Atom a IN w))
      (\w1 w2.
         MAXIMAL_CONSISTENT B_AX p w1 /\
         (!q. MEM q w1 ==> q SUBSENTENCE p) /\
         w2 IN B_STDWORLDS p /\
         set_of_list w1 = w2)`,
 GEN_TAC THEN REWRITE_TAC[BISIMIMULATION] THEN REPEAT GEN_TAC THEN
 STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
 [GEN_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC[IN_SET_OF_LIST];
  ALL_TAC] THEN
 CONJ_TAC THENL
 [INTRO_TAC "![u1]; w1u1" THEN EXISTS_TAC `set_of_list u1:form->bool` THEN
  HYP_TAC "w1u1 -> hp" (REWRITE_RULE[B_STANDARD_REL_CAR]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC B_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC B_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN MATCH_MP_TAC B_STDREL_RULES THEN
  ASM_REWRITE_TAC[];
  ALL_TAC] THEN
 INTRO_TAC "![u2]; w2u2" THEN EXISTS_TAC `list_of_set u2:form list` THEN
 REWRITE_TAC[CONJ_ACI] THEN
 HYP_TAC "w2u2 -> @x2 y2. x2 y2 x2y2" (REWRITE_RULE[B_STDREL_CASES]) THEN
 REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
 SIMP_TAC[SET_OF_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
 SIMP_TAC[MEM_LIST_OF_SET; FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
 CONJ_TAC THENL
 [HYP_TAC "x2y2 -> hp" (REWRITE_RULE[B_STANDARD_REL_CAR]) THEN
  ASM_REWRITE_TAC[];
  ALL_TAC] THEN
 CONJ_TAC THENL
 [MATCH_MP_TAC SET_OF_LIST_EQ_B_STANDARD_REL THEN
  EXISTS_TAC `x2:form list` THEN EXISTS_TAC `y2:form list` THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET;
           FINITE_SET_OF_LIST] THEN
  ASM_MESON_TAC[MAXIMAL_CONSISTENT];
  ALL_TAC] THEN
 CONJ_TAC THENL
 [ASM_MESON_TAC[B_STDREL_IMP_B_STDWORLDS]; ALL_TAC] THEN
 MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN
 EXISTS_TAC `y2:form list` THEN
 SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
 SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
 ASM_MESON_TAC[B_STANDARD_REL_CAR]);;

let B_COUNTERMODEL_FINITE_SETS = prove
 (`!p. ~ [B_AX . {} |~ p] ==> ~holds_in (B_STDWORLDS p, B_STDREL p) p`,
  INTRO_TAC "!p; p" THEN
  DESTRUCT_TAC "@M. max mem subf"
    (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ [B_AX . {} |~ p]`)) THEN
  REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP] THEN
  ASSUM_LIST (LABEL_TAC "hp" o MATCH_MP B_COUNTERMODEL o
                end_itlist CONJ o rev) THEN
  EXISTS_TAC `\a w. Atom a SUBFORMULA p /\ Atom a IN w` THEN
  EXISTS_TAC `set_of_list M:form->bool` THEN CONJ_TAC THENL
  [MATCH_MP_TAC B_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "hp" MP_TAC THEN
  MATCH_MP_TAC (MESON[] `(p <=> q) ==> (~p ==> ~q)`) THEN
  MATCH_MP_TAC BISIMIMULATION_HOLDS THEN
  EXISTS_TAC`\w1 w2. MAXIMAL_CONSISTENT B_AX p w1 /\
                     (!q. MEM q w1 ==> q SUBSENTENCE p) /\
                     w2 IN B_STDWORLDS p /\
                     set_of_list w1 = w2` THEN
  ASM_REWRITE_TAC[B_BISIMIMULATION_SET_OF_LIST] THEN
  MATCH_MP_TAC B_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;
