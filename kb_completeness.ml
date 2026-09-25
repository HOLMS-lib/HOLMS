(* ========================================================================= *)
(* Proof of the consistency and modal completeness of B.                     *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

needs "HOLMS/gen_completeness.ml";;

let KB_AX = new_definition
  `KB_AX = {B_SCHEMA p | p IN (:form)}`;;

let B_IN_KB_AX = prove
 (`!q. p -->  Box Diam p IN KB_AX`,
  REWRITE_TAC[KB_AX; B_SCHEMA_DEF; IN_ELIM_THM;
              IN_UNIV] THEN
  MESON_TAC[]);;

let B_AX_KB= prove
 (`!q. [KB_AX. {} |~ (q --> Box Diam q)]`,
  MESON_TAC[MODPROVES_RULES; B_IN_KB_AX]);;

(* ------------------------------------------------------------------------- *)
(* Symmetric frames.                                                         *)
(* ------------------------------------------------------------------------- *)

let SYM_DEF = new_definition
  `SYM =
   {(W:W->bool,R:W->W->bool) |
    (W,R) IN FRAME /\
    SYMMETRIC W R}`;;
    
let IN_SYM = prove
 (`(W:W->bool,R:W->W->bool) IN SYM <=>
   (W,R) IN FRAME /\
    SYMMETRIC W R`,
  REWRITE_TAC[SYM_DEF; IN_ELIM_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory: Symmetric Frames are characteristic for KB.        *)
(* ------------------------------------------------------------------------- *)

let SYM_CHAR_KB = prove
  (`SYM:(W->bool)#(W->W->bool)->bool = CHAR KB_AX`,
   REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN
    REWRITE_TAC[IN_CHAR; IN_SYM] THEN
    REWRITE_TAC[KB_AX; FORALL_IN_GSPEC; MODAL_SYM; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. Symmetric Frames                                *)
(* ------------------------------------------------------------------------- *)

let KB_SYM_VALID = prove
 (`!H p. [KB_AX . H |~ p] /\
         (!q. q IN H ==> SYM:(W->bool)#(W->W->bool)->bool |= q)
         ==> SYM:(W->bool)#(W->W->bool)->bool |= p`,
  ASM_MESON_TAC[GEN_CHAR_VALID; SYM_CHAR_KB]);;

(* ------------------------------------------------------------------------- *)
(* Finite Symmetric Frames are appropriate for KB.                           *)
(* ------------------------------------------------------------------------- *)

let SYF_DEF = new_definition
 `SYF =
  {(W:W->bool,R:W->W->bool) |
   (W,R) IN FINITE_FRAME /\
    SYMMETRIC W R}`;;

let IN_SYF = prove
 (`(W:W->bool,R:W->W->bool) IN SYF <=>
   (W,R) IN FINITE_FRAME /\
    SYMMETRIC W R`,
  REWRITE_TAC[SYF_DEF; IN_ELIM_PAIR_THM]);;

let SYF_FIN_SYM = prove
 (`SYF:(W->bool)#(W->W->bool)->bool = (SYM INTER FINITE_FRAME)`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN 
  REWRITE_TAC[IN_INTER; IN_SYF; IN_FINITE_FRAME; TRANSITIVE;
              IN_SYM; IN_FRAME] THEN
  MESON_TAC[FINITE_FRAME_SUBSET_FRAME; SUBSET]);;

let SYF_APPR_KB = prove
  (`SYF: (W->bool)#(W->W->bool)->bool = APPR KB_AX`,
   REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN
    REWRITE_TAC[APPR_CAR; SYF_FIN_SYM] THEN
    REWRITE_TAC[SYM_CHAR_KB; IN_INTER; IN_CHAR; IN_FINITE_FRAME_INTER] THEN
    MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. SYF.                                            *)
(* ------------------------------------------------------------------------- *)

let KB_SYF_VALID = prove
 (`!p. [KB_AX . {} |~ p] ==> SYF:(W->bool)#(W->W->bool)->bool |= p`,
  MESON_TAC[GEN_APPR_VALID; SYF_APPR_KB]);;

(* ------------------------------------------------------------------------- *)
(* Proof of Consistency of KB.                                               *)
(* ------------------------------------------------------------------------- *)

let KB_CONSISTENT = prove
 (`~ [KB_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`]KB_SYF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM; IN_SYF;
              IN_FINITE_FRAME; SYMMETRIC; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. x = 0 /\ x = y`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* KB standard frames and models.                                            *)
(* ------------------------------------------------------------------------- *)

let KB_STANDARD_WORLD_DEF = new_definition
  `KB_STANDARD_WORLD p = GEN_STANDARD_WORLD KB_AX p`;;

let KB_STANDARD_FRAME_DEF = new_definition
  `KB_STANDARD_FRAME p = GEN_STANDARD_FRAME KB_AX p`;;

let IN_KB_STANDARD_FRAME = prove
  (`!p W R. (W,R) IN KB_STANDARD_FRAME p <=>
            W = KB_STANDARD_WORLD p /\
            (W,R) IN SYF /\
            (!q w. Box q SUBFORMULA p /\ w IN W
                   ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`,
 REPEAT GEN_TAC THEN
 REWRITE_TAC[KB_STANDARD_FRAME_DEF; IN_GEN_STANDARD_FRAME; 
             KB_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD] THEN
 EQ_TAC THEN MESON_TAC[SYF_APPR_KB]);;

let KB_STANDARD_MODEL_DEF = new_definition
  `KB_STANDARD_MODEL = GEN_STANDARD_MODEL KB_AX`;;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let KB_TRUTH_LEMMA = prove
 (`!W R p V q.
     ~ [KB_AX . {} |~ p] /\
     KB_STANDARD_MODEL p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REWRITE_TAC[KB_STANDARD_MODEL_DEF] THEN MESON_TAC[GEN_TRUTH_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Accessibility lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let KB_STANDARD_REL_DEF = new_definition
  `KB_STANDARD_REL p w x <=>
   GEN_STANDARD_REL KB_AX p w x /\
   (!B. MEM (Box B) x ==> MEM B w)`;;

let KB_STANDARD_REL_CAR = prove
 (`!p w x.
     KB_STANDARD_REL p w x <=>
     w IN KB_STANDARD_WORLD p /\
     x IN KB_STANDARD_WORLD p /\
     (!B. MEM (Box B) w ==> MEM B x) /\
     (!B. MEM (Box B) x ==> MEM B w)`,
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[KB_STANDARD_REL_DEF; GEN_STANDARD_REL; 
              IN_ELIM_THM; KB_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD] THEN
  MESON_TAC[]);;

let SYF_MAXIMAL_CONSISTENT = prove
 (`!p. ~ [KB_AX . {} |~ p]
       ==> (KB_STANDARD_WORLD p,
            KB_STANDARD_REL p)
           IN SYF `,
  INTRO_TAC "!p; p" THEN
  MP_TAC (ISPECL [`KB_AX`; `p:form`] GEN_FINITE_FRAME_MAXIMAL_CONSISTENT) THEN
  REWRITE_TAC[IN_FINITE_FRAME] THEN INTRO_TAC "gen_max_cons" THEN
  ASM_REWRITE_TAC[IN_SYF; IN_FINITE_FRAME; SYMMETRIC] THEN
  CONJ_TAC THENL
  (* Nonempty *)
  [CONJ_TAC THENL 
   [REWRITE_TAC[KB_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD] THEN
   ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Well-defined *)
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[KB_STANDARD_REL_CAR] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Finite *)
   REWRITE_TAC[KB_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD] THEN
   ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Symmetric *)
   REWRITE_TAC[IN_ELIM_THM; KB_STANDARD_REL_CAR] THEN
   INTRO_TAC "!w w'; w w' w w' mem_w mem_w'"  THEN
   ASM_REWRITE_TAC[KB_STANDARD_REL_CAR]);;

let KB_ACCESSIBILITY_LEMMA = prove
  (`!p w q.
     ~ [KB_AX . {} |~ p] /\
     w IN KB_STANDARD_WORLD p /\
     Box q SUBFORMULA p /\
     (!x. KB_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`,
   INTRO_TAC "!p w q; p  stdw boxq rel" THEN
   REFUTE_THEN (LABEL_TAC "contra") THEN
   REMOVE_THEN "rel" MP_TAC THEN REWRITE_TAC[NOT_FORALL_THM] THEN
   ABBREV_TAC `X = Not q INSERT ({C | Box C IN set_of_list w} UNION
                                 {Not Box E | Not E IN set_of_list w /\ 
                                                      Box E SUBSENTENCE p}) ` 
   THEN POP_ASSUM (LABEL_TAC "X") THEN
   THEN1
   (CLAIM_TAC "FinX1 FinX2 FinX3 FinX4"
    `FINITE {C | Box C IN set_of_list w} /\
     FINITE {Box C | Box C IN set_of_list w} /\
     FINITE {Not E | Not E IN set_of_list w /\
                     Box E SUBSENTENCE p} /\
     FINITE {Not Box E | Not E IN set_of_list w /\
                         Box E SUBSENTENCE p}`)
   (CLAIM_TAC "FinX1" `FINITE {C | Box C IN set_of_list w}` THENL 
    [MATCH_MP_TAC FINITE_SUBSET THEN       
     EXISTS_TAC `{y | ?x. x IN set_of_list w /\ y = dest_box_fun x}` THEN
     CONJ_TAC THENL 
     [MATCH_MP_TAC FINITE_IMAGE_EXPAND THEN 
      ASM_REWRITE_TAC[FINITE_SET_OF_LIST];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      GEN_TAC THEN DISCH_TAC THEN
      EXISTS_TAC `Box x` THEN ASM_REWRITE_TAC[dest_box_fun]]; ALL_TAC] THEN      
    HYP REWRITE_TAC "FinX1" [] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_SUBSET THEN 
     EXISTS_TAC `IMAGE (Box) {C | Box C IN set_of_list w}` THEN
     CONJ_TAC THENL [ASM_MESON_TAC[FINITE_IMAGE]; SET_TAC[]];
     MATCH_MP_TAC FINITE_SUBSET THEN       
     EXISTS_TAC `set_of_list (w:form list)` THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[FINITE_SET_OF_LIST]; SET_TAC[]];
     MATCH_MP_TAC FINITE_SUBSET THEN       
     EXISTS_TAC `{y | ?x. x:form IN set_of_list w /\ 
                      (Box dest_not_fun x) SUBSENTENCE p /\
                      y = Not Box dest_not_fun x}` THEN
     CONJ_TAC THENL 
     [MATCH_MP_TAC FINITE_IMAGE_EXPAND_GEN THEN 
      ASM_REWRITE_TAC[FINITE_SET_OF_LIST];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      INTRO_TAC "!x; (@E. E)" THEN
      EXISTS_TAC `Not E` THEN ASM_REWRITE_TAC[dest_not_fun]]]) THEN
   THEN1
   (CLAIM_TAC "@M. Mmax Mfin M Msuper"
    `?M. MAXIMAL_SETCONSISTENT KB_AX p M /\
         FINITE M /\
         (!q. q IN M ==> q SUBSENTENCE p) /\
         X SUBSET M`)
   (MATCH_MP_TAC EXTEND_MAXIMAL_SETCONSISTENT THEN
    SHOW_TAC `SETCONSISTENT KB_AX X` THENL
    [EXPAND_TAC "X" THEN
     REMOVE_THEN "X" (K ALL_TAC) THEN
     REFUTE_THEN (LABEL_TAC "contra_cons") THEN
     REMOVE_THEN "contra" MP_TAC THEN
     REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN
     MATCH_MP_TAC MAXIMAL_SETCONSISTENT_LEMMA THEN
     MAP_EVERY EXISTS_TAC [`KB_AX`; `p:form`; 
                           `{Box C | Box C IN set_of_list w} UNION 
                            {Not E | Not E IN set_of_list w /\ 
                                     Box E SUBSENTENCE p}`] THEN
     HYP_TAC "stdw: maxconsw w" 
             (REWRITE_RULE [IN_ELIM_THM; KB_STANDARD_WORLD_DEF; 
                            GEN_STANDARD_WORLD;
                            MAXIMAL_CONSISTENT_IFF_MAXIMAL_SETCONSISTENT])THEN
     HYP REWRITE_TAC "maxconsw boxq" [] THEN
     CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
     HYP_TAC "contra_cons" (REWRITE_RULE[SETCONSISTENT]) THEN
     HYP_SUFFICE_TAC `[KB_AX. {} |~ CONJLIST 
                                    (list_of_set (
                                     {Box C | Box C IN set_of_list w} UNION
                                     {Not E | Not E IN set_of_list w /\ 
                                              Box E SUBSENTENCE p})) 
                                    --> Box q]` 
                     "FinX2 FinX3" 
                     [GSYM MODPROVES_DEDUCTION_LEMMA_CONJLIST_EMPTY_ALT; FINITE_UNION] THEN
      CLAIM_TAC "contra_prove" 
                `[KB_AX .{} |~ CONJLIST 
                               (list_of_set 
                               ({C | Box C IN set_of_list w} UNION
                                {Not Box E | Not E IN set_of_list w /\ 
                                                     Box E SUBSENTENCE p})) 
                              --> q]` THENL
      [HYP SIMP_TAC "FinX1 FinX4"[MODPROVES_DEDUCTION_LEMMA_CONJLIST_EMPTY_ALT; 
                                  FINITE_UNION] THEN
       ONCE_REWRITE_TAC[GSYM MLK_DOUBLENEG_IFF; MLK_not_def] THEN
       ONCE_REWRITE_TAC[MLK_not_def] THEN
       REWRITE_TAC[MODPROVES_DEDUCTION_LEMMA] THEN
       HYP REWRITE_TAC "contra_cons" [];
       ALL_TAC] THEN
      REMOVE_THEN "contra_cons" (K ALL_TAC) THEN   
      SHOW_TAC `[KB_AX . {} |~
                 CONJLIST (list_of_set
                                     ({Box C | Box C IN set_of_list w} UNION
                                      {Not E | Not E IN set_of_list w /\ 
                                               Box E SUBSENTENCE p})) 
                 --> Box q]` THENL
      [MATCH_MP_TAC MLK_imp_trans THEN
       EXISTS_TAC `CONJLIST (list_of_set
                            ({Box C | Box C IN set_of_list w} UNION
                             {Box Not Box E | 
                               Not E IN set_of_list w /\ 
                               Box E SUBSENTENCE p}))` THEN
       SHOW_TAC ` [KB_AX . {} |~ 
                   CONJLIST
                    (list_of_set
                     ({Box C | Box C IN set_of_list w} UNION
                      {Box Not Box E | Not E IN set_of_list w /\ 
                                       Box E SUBSENTENCE p}))
                   --> Box q]` THENL
       [MATCH_MP_TAC MLK_imp_trans THEN
        EXISTS_TAC `Box CONJLIST (list_of_set
                                  ({C | Box C IN set_of_list w} UNION
                                   {Not Box E | 
                                     Not E IN set_of_list w /\
                                     Box E SUBSENTENCE p}))` THEN
        CONJ_TAC THENL
        [ALL_TAC; MATCH_MP_TAC MLK_boximp THEN
         ASM_MESON_TAC[MLK_necessitation]] THEN
        MATCH_MP_TAC MLK_iff_imp1 THEN
        MATCH_MP_TAC MLK_iff_trans THEN
        EXISTS_TAC `CONJLIST (MAP (Box) (list_of_set 
                              ({C | Box C IN set_of_list w} UNION
                               {Not Box E | 
                                 Not E IN set_of_list w /\ 
                                 Box E SUBSENTENCE p})))` THEN
        CONJ_TAC THENL
        [ALL_TAC; REWRITE_TAC [GSYM CONJLIST_MAP_BOX]] THEN
        MATCH_MP_TAC SET_OF_LIST_EQ_CONJLIST_EQ THEN 
        ASM_REWRITE_TAC[SET_OF_LIST_MAP] THEN
        SUFFICE_TAC `FINITE ({Box C | Box C IN set_of_list w} UNION
                             {Box Not Box E | Not E IN set_of_list w /\ 
                                              Box E SUBSENTENCE p}) /\
                     FINITE ({C | Box C IN set_of_list w} UNION
                             {Not Box E | Not E IN set_of_list w /\ 
                                          Box E SUBSENTENCE p}) /\
                     {Box C | Box C IN set_of_list w} UNION 
                     {Box Not Box E | Not E IN set_of_list w /\ 
                                      Box E SUBSENTENCE p} = 
                     IMAGE(Box) ({C | Box C IN set_of_list w} UNION 
                                 {Not Box E | Not E IN set_of_list w /\ 
                                              Box E SUBSENTENCE p})`
                   [SET_OF_LIST_OF_SET] THEN
        REPEAT CONJ_TAC THENL
        [HYP REWRITE_TAC "FinX2" [FINITE_UNION] THEN
         MATCH_MP_TAC FINITE_SUBSET THEN
         EXISTS_TAC `IMAGE(Box) {Not Box E | Not E IN set_of_list w /\ 
                                             Box E SUBSENTENCE p}` THEN
         CONJ_TAC THENL
         [ASM_MESON_TAC[FINITE_IMAGE]; SET_TAC[]];
         HYP REWRITE_TAC "FinX1 FinX4" [FINITE_UNION];
         SET_TAC[]]; ALL_TAC]] THEN
       SHOW_TAC `[KB_AX . {} |~ 
                  CONJLIST
                  (list_of_set
                  ({Box C | Box C IN set_of_list w} UNION
                   {Not E | Not E IN set_of_list w /\ Box E SUBSENTENCE p}))
                  -->
                  CONJLIST
                  (list_of_set
                  ({Box C | Box C IN set_of_list w} UNION
                   {Box Not Box E | Not E IN set_of_list w /\ 
                                            Box E SUBSENTENCE p}))]` THENL
        [MATCH_MP_TAC MLK_imp_mp_subst THEN
         EXISTS_TAC `CONJLIST (list_of_set({Box C | Box C IN set_of_list w})) &&
                     CONJLIST (list_of_set({Not E | Not E IN set_of_list w /\ 
                                                    Box E SUBSENTENCE p}))` THEN
         SHOW_TAC `[KB_AX . {} |~ 
                    CONJLIST (list_of_set {Box C | Box C IN set_of_list w}) &&
                    CONJLIST (list_of_set {Not E | Not E IN set_of_list w /\ 
                                                   Box E SUBSENTENCE p}) <->
                    CONJLIST (list_of_set ({Box C | Box C IN set_of_list w} 
                                           UNION
                                           {Not E | Not E IN set_of_list w /\
                                                    Box E SUBSENTENCE p}))]` 
          THENL [ONCE_REWRITE_TAC[MLK_iff_sym] THEN
          MATCH_MP_TAC MODPROVES_UNION_CONJLIST_THM THEN
          HYP REWRITE_TAC "FinX2 FinX3" []; ALL_TAC] THEN
          EXISTS_TAC `CONJLIST(list_of_set({Box C | Box C IN set_of_list w}))&&
                      CONJLIST (list_of_set({Box Not Box E | 
                                              Not E IN set_of_list w /\ 
                                              Box E SUBSENTENCE p}))` THEN
          SHOW_TAC `[KB_AX . {} |~ 
                     CONJLIST (list_of_set {Box C | Box C IN set_of_list w}) &&
                     CONJLIST (list_of_set {Box Not Box E | 
                                             Not E IN set_of_list w /\ 
                                             Box E SUBSENTENCE p}) <->
                     CONJLIST (list_of_set ({Box C | Box C IN set_of_list w} 
                                            UNION
                                            {Box Not Box E | 
                                               Not E IN set_of_list w /\
                                               Box E SUBSENTENCE p}))]` THENL
          [ONCE_REWRITE_TAC[MLK_iff_sym] THEN
           MATCH_MP_TAC MODPROVES_UNION_CONJLIST_THM THEN
           HYP REWRITE_TAC "FinX2" [] THEN
           MATCH_MP_TAC FINITE_SUBSET THEN
           EXISTS_TAC ` IMAGE (Box) {Not Box E | 
                                      Not E IN set_of_list w /\ 
                                      Box E SUBSENTENCE p}` THEN
           CONJ_TAC THENL
           [ASM_MESON_TAC[FINITE_IMAGE]; SET_TAC[]]; ALL_TAC] THEN
          SHOW_TAC `[KB_AX . {} |~ 
                     CONJLIST (list_of_set {Box C | Box C IN set_of_list w}) &&
                     CONJLIST (list_of_set {Not E | Not E IN set_of_list w /\ 
                                                    Box E SUBSENTENCE p}) -->
                     CONJLIST (list_of_set {Box C | Box C IN set_of_list w}) &&
                     CONJLIST (list_of_set {Box Not Box E | 
                                             Not E IN set_of_list w /\ 
                                             Box E SUBSENTENCE p})]` THENL
          [MATCH_MP_TAC MLK_and_imp THEN
           REWRITE_TAC [MLK_imp_refl_th] THEN
           MATCH_MP_TAC MLK_imp_trans THEN
           EXISTS_TAC `Box Diam (CONJLIST (list_of_set
                                  {Not E | Not E IN set_of_list w /\ 
                                           Box E SUBSENTENCE p}))` THEN
           CONJ_TAC THENL
           [MESON_TAC[B_AX_KB]; ALL_TAC] THEN
           MATCH_MP_TAC MLK_imp_trans THEN
           EXISTS_TAC `CONJLIST (MAP (Box) (MAP (Diam) 
                         (list_of_set {Not E | Not E IN set_of_list w /\ 
                                               Box E SUBSENTENCE p})))` THEN
           CONJ_TAC THENL
           [MESON_TAC[CONJLIST_MAP_BOX_DIAM]; ALL_TAC] THEN
           MATCH_MP_TAC MEM_EQ_CONJLIST_IMP THEN
           GEN_TAC THEN REWRITE_TAC[MEM_MAP] THEN
           INTRO_TAC "y_mem" THEN
           CLAIM_TAC "y_in" `y IN {Box Not Box E | Not E IN set_of_list w /\ 
                                            Box E SUBSENTENCE p}` THENL
           [HYP_SUFFICE_TAC `FINITE {Box Not Box E | Not E IN set_of_list w /\ 
                                                Box E SUBSENTENCE p}`
                            "y_mem" [MEM_LIST_OF_SET] THEN
            MATCH_MP_TAC FINITE_SUBSET THEN
            EXISTS_TAC ` IMAGE (Box) {Not Box E | 
                                      Not E IN set_of_list w /\ 
                                      Box E SUBSENTENCE p}` THEN
            CONJ_TAC THENL
            [ASM_MESON_TAC[FINITE_IMAGE]; SET_TAC[]]; ALL_TAC] THEN
            HYP_TAC "y_in: @E. y" (REWRITE_RULE[IN_ELIM_THM]) THEN
            EXISTS_TAC `Box Diam Not E` THEN
            CONJ_TAC THENL
            [EXISTS_TAC `Diam Not E` THEN REWRITE_TAC[] THEN
             EXISTS_TAC ` Not E` THEN REWRITE_TAC[] THEN
             HYP_SUFFICE_TAC `Not E IN {Not E | Not E IN set_of_list w /\ 
                                                Box E SUBSENTENCE p}`
                             "FinX3" [MEM_LIST_OF_SET] THEN
             REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `E:form` THEN
             HYP REWRITE_TAC "y" [];
             HYP REWRITE_TAC "y" [diam_DEF] THEN MATCH_MP_TAC MLK_iff_imp1 THEN
             ASM_REWRITE_TAC[diam_DEF] THEN MATCH_MP_TAC MLK_box_subst THEN
             MATCH_MP_TAC MLK_not_subst THEN MATCH_MP_TAC MLK_box_subst THEN
             MESON_TAC[MLK_not_not_th]]]]; ALL_TAC] THEN
    THEN1
      (SHOW_TAC `FINITE (X:form->bool)`)
      (EXPAND_TAC "X" THEN REWRITE_TAC[FINITE_INSERT; FINITE_UNION] THEN
       HYP REWRITE_TAC "FinX1 FinX4" []) THEN
    SHOW_TAC `!q. q IN X ==> q SUBSENTENCE p` THENL
    [EXPAND_TAC "X" THEN
     REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_UNION; FORALL_IN_GSPEC; IN_SET_OF_LIST] THEN
     THEN1
      (SHOW_TAC `Not q SUBSENTENCE p`)
      (SUFFICE_TAC `q SUBFORMULA p` [SUBSENTENCE_RULES] THEN
       HYP MESON_TAC "boxq" [MINOR_SUBFORMULA]) THEN
     THEN1
      (SHOW_TAC `!C. MEM (Box C) w ==> C SUBSENTENCE p`)
      (INTRO_TAC "!C; boxC_mem_w" THEN
       MATCH_MP_TAC SUBFORMULA_IMP_SUBSENTENCE THEN
       MATCH_MP_TAC SUBFORMULA_TRANS THEN
       EXISTS_TAC `Box C` THEN
       REWRITE_TAC[SUBFORMULA_INVERSION; SUBFORMULA_REFL] THEN
       SUFFICE_TAC `Box C SUBSENTENCE p` [SUBSENTENCE_CASES; form_DISTINCT] THEN
       HYP_TAC "stdw" (REWRITE_RULE[IN_ELIM_THM; KB_STANDARD_WORLD_DEF; 
                       GEN_STANDARD_WORLD]) THEN
       HYP MESON_TAC "stdw boxC_mem_w" [] THEN
       REWRITE_TAC[SUBSENTENCE_CASES; form_DISTINCT]) THEN
      SHOW_TAC `!E. MEM (Not E) w /\ Box E SUBSENTENCE p ==> Not Box E SUBSENTENCE p` THENL
      [INTRO_TAC "!E; notE_mem_w boxE_subs" THEN
       SUFFICE_TAC `Box E SUBFORMULA p` [SUBFORMULA_IMP_NEG_SUBSENTENCE] THEN
       HYP MESON_TAC "boxE_subs" [form_DISTINCT; SUBSENTENCE_CASES]]]) THEN
   SUFFICE_TAC `KB_STANDARD_REL p w (list_of_set M) /\ ~MEM q (list_of_set M)` [] THEN
   SHOW_TAC `~MEM (q:form) (list_of_set M)` THENL
   [HYP_SUFFICE_TAC `~(q:form IN M)` "Mfin" [MEM_LIST_OF_SET] THEN
    HYP_SUFFICE_TAC `Not q IN M` "Mmax" [IN_SETCONSISTENT_NC; MAXIMAL_SETCONSISTENT_IMP_SETCONSISTENT] THEN
    HYP_SUFFICE_TAC `Not q IN X` "Msuper" [SUBSET] THEN
    EXPAND_TAC "X" THEN REWRITE_TAC[IN_INSERT; IN_UNION];
    ALL_TAC] THEN
   SHOW_TAC `KB_STANDARD_REL p w (list_of_set M)` THEN
   ASM_REWRITE_TAC[KB_STANDARD_REL_CAR] THEN
   SHOW_TAC `(list_of_set (M:form->bool)) IN KB_STANDARD_WORLD p` THENL
   [REWRITE_TAC[KB_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD; IN_ELIM_THM] THEN
    REWRITE_TAC[MAXIMAL_CONSISTENT_IFF_MAXIMAL_SETCONSISTENT] THEN
    HYP SIMP_TAC "Mfin" [SET_OF_LIST_OF_SET; NOREPETITION_LIST_OF_SET; MEM_LIST_OF_SET] THEN
    FROM_TAC ["Mmax"; "M"] THEN BY ASM_CLEAR_TAC; ALL_TAC] THEN
   SHOW_TAC `!B. MEM (Box B) w ==> MEM B (list_of_set M)` THENL
   [INTRO_TAC "!B; BoxB_mem_w" THEN
    HYP_SUFFICE_TAC `B:form IN M` "Mfin" [MEM_LIST_OF_SET] THEN
    HYP_SUFFICE_TAC `B:form IN X` "Msuper" [SUBSET] THEN
    EXPAND_TAC "X" THEN 
    SUFFICE_TAC `B IN {C | Box C IN set_of_list w}` [IN_INSERT; IN_UNION] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN 
    ASM_REWRITE_TAC[IN_SET_OF_LIST]; ALL_TAC] THEN
   SHOW_TAC `!B. MEM (Box B) (list_of_set M) ==> MEM B w` THENL
   [SUFFICE_TAC `(?E:form. MEM (Box E) (list_of_set M) /\ ~ MEM E w) 
                 ==> F` [] THEN
    HYP_SUFFICE_TAC `(?E:form. Box E IN M /\ ~ (E IN (set_of_list w))) ==> F`
                    "Mfin" [GSYM IN_SET_OF_LIST; SET_OF_LIST_OF_SET] THEN
    INTRO_TAC "@E. BoxE_in_M E_not_mem_w" THEN
    HYP_SUFFICE_TAC `Not Box E IN M` "Mmax BoxE_in_M" 
                    [IN_SETCONSISTENT_NC; MAXIMAL_SETCONSISTENT] THEN     
    HYP_SUFFICE_TAC `Not Box E IN X` "Msuper" [SUBSET]  THEN
    EXPAND_TAC "X" THEN REWRITE_TAC[IN_UNION; IN_INSERT; IN_ELIM_THM] THEN
    SUFFICE_TAC `Not E IN set_of_list w /\ Box E SUBSENTENCE p` [] THEN
    SHOW_TAC `Not E IN set_of_list w` THENL
    [CLAIM_TAC "wmax" `MAXIMAL_SETCONSISTENT KB_AX p (set_of_list w)` THENL
     [HYP_TAC "stdw" (REWRITE_RULE[IN_ELIM_THM; KB_STANDARD_WORLD_DEF; 
                                   GEN_STANDARD_WORLD]) THEN
      ASM_MESON_TAC[MAXIMAL_CONSISTENT_IFF_MAXIMAL_SETCONSISTENT]; ALL_TAC] THEN
     HYP_SUFFICE_TAC `E SUBFORMULA p` "wmax E_not_mem_w" [MAXIMAL_SETCONSISTENT] THEN
     MATCH_MP_TAC SUBFORMULA_TRANS THEN
     SUBGOAL_THEN `Box E SUBSENTENCE p` MP_TAC THENL
     [HYP MESON_TAC "BoxE_in_M M" []; ALL_TAC] THEN
     REWRITE_TAC[SUBSENTENCE_CASES] THEN
     ASM_MESON_TAC[form_DISTINCT; SUBFORMULA_TRANS; SUBFORMULA_INVERSION;
                      SUBFORMULA_REFL];
    HYP MESON_TAC "BoxE_in_M M" []]]);;

(* ------------------------------------------------------------------------- *)
(* Modal completeness theorem for KB.                                        *)
(* ------------------------------------------------------------------------- *)

let KB_STD_IN_KB_STANDARD_FRAME = prove
  (`!p. ~ [KB_AX . {} |~ p]
       ==> (KB_STANDARD_WORLD p,
            KB_STANDARD_REL p)
           IN KB_STANDARD_FRAME p`,
   INTRO_TAC "!p; not_theor_p" THEN
   ASM_REWRITE_TAC [IN_KB_STANDARD_FRAME] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC [SYF_MAXIMAL_CONSISTENT];
    INTRO_TAC "!q w; boxq stdw" THEN
    EQ_TAC THENL
    [ASM_MESON_TAC[KB_STANDARD_REL_CAR];
    ASM_MESON_TAC[KB_ACCESSIBILITY_LEMMA]]]);;

let KB_COUNTERMODEL = prove
 (`!M p.
     ~ [KB_AX . {} |~ p] /\
     M IN KB_STANDARD_WORLD p /\
     MEM (Not p) M ==>
     ~holds
        (KB_STANDARD_WORLD p,
         KB_STANDARD_REL p)
        (STANDARD_EVAL p)
        p M`,
  INTRO_TAC "!M p; pr stdM mem" THEN
  MATCH_MP_TAC GEN_COUNTERMODEL THEN EXISTS_TAC `KB_AX` THEN 
  HYP_TAC "stdM -> maxconsM M" (REWRITE_RULE[IN_KB_STANDARD_FRAME; KB_STANDARD_WORLD_DEF;
                               GEN_STANDARD_WORLD; IN_ELIM_THM]) THEN
  ASM_REWRITE_TAC[GEN_STANDARD_MODEL_DEF] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[KB_STD_IN_KB_STANDARD_FRAME; KB_STANDARD_FRAME_DEF];
   ALL_TAC] THENL
  [ASM_MESON_TAC[IN_ELIM_THM; STANDARD_EVAL;
                 KB_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD]]);;

let KB_COMPLETENESS_THM = prove
  (`!p. SYF:(form list->bool)#(form list->form list->bool)->bool |= p
        ==> [KB_AX . {} |~ p]`,
    GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
    INTRO_TAC "p_not_theor" THEN
    REWRITE_TAC[valid; NOT_FORALL_THM] THEN
    EXISTS_TAC `(KB_STANDARD_WORLD p, KB_STANDARD_REL p)` THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
    [ASM_MESON_TAC [SYF_MAXIMAL_CONSISTENT];
     SUBGOAL_THEN `(KB_STANDARD_WORLD p,
                    KB_STANDARD_REL p)
                   IN GEN_STANDARD_FRAME KB_AX p`
                  MP_TAC THENL
     [ASM_MESON_TAC[KB_STD_IN_KB_STANDARD_FRAME; KB_STANDARD_FRAME_DEF];
     ASM_MESON_TAC[GEN_COUNTERMODEL_ALT]]]);;

(* ------------------------------------------------------------------------- *)
(* Modal completeness for KB for models on a generic (infinite) domain.      *)
(* ------------------------------------------------------------------------- *)

let KB_COMPLETENESS_THM_GEN = prove
 (`!p. INFINITE (:A) /\ SYF:(A->bool)#(A->A->bool)->bool |= p
       ==> [KB_AX . {} |~ p]`,
  SUBGOAL_THEN
    `INFINITE (:A)
     ==> !p. SYF:(A->bool)#(A->A->bool)->bool |= p
             ==> SYF:(form list->bool)#(form list->form list->bool)->bool |= p`
    (fun th -> MESON_TAC[th; KB_COMPLETENESS_THM]) THEN
  ASM_MESON_TAC[SYF_APPR_KB; GEN_LEMMA_FOR_GEN_COMPLETENESS]);;

(* ------------------------------------------------------------------------- *)
(* Simple decision procedure for B.                                          *)
(* ------------------------------------------------------------------------- *)

let KB_TAC : tactic =
  MATCH_MP_TAC KB_COMPLETENESS_THM THEN
  REWRITE_TAC[diam_DEF; valid; FORALL_PAIR_THM; holds_in; holds; IN_SYF;
    IN_FINITE_FRAME; SYMMETRIC; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[];;

let KB_RULE tm =
  prove(tm, REPEAT GEN_TAC THEN KB_TAC);;

KB_RULE `!p q r. [KB_AX . {} |~ p && q && r --> p && r]`;;
KB_RULE `!p q. [KB_AX . {} |~  Box (p --> q) && Box p --> Box q]`;;
(*KB_RULE `!p q. [KB_AX . {} |~  Box p --> p]`;;*)
KB_RULE `!p. [KB_AX . {} |~  p -->  Box Diam p]`;;
(* KB_RULE `!p. [KB_AX . {} |~ Box p --> Box (Box p)]`;; *)
(* KB_RULE `!p. [KB_AX . {} |~ (Box (Box p --> p) --> Box p)]`;; *)
(* KB_RULE `!p. [KB_AX . {} |~ Box (Box p --> p) --> Box p]`;; *)
(* KB_RULE `[KB_AX . {} |~ Box (Box False --> False) --> Box False]`;; *)

(* ------------------------------------------------------------------------- *)
(* Countermodel using set of formulae (instead of lists of formulae).        *)
(* ------------------------------------------------------------------------- *)

let KB_STDWORLDS_RULES,KB_STDWORLDS_INDUCT,KB_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT KB_AX p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN KB_STDWORLDS p`;;

let KB_STDREL_RULES,KB_STDREL_INDUCT,KB_STDREL_CASES = new_inductive_definition
  `!w1 w2. KB_STANDARD_REL p w1 w2
           ==> KB_STDREL p (set_of_list w1) (set_of_list w2)`;;

let KB_STDREL_IMP_KB_STDWORLDS = prove
 (`!p w1 w2. KB_STDREL p w1 w2 ==>
             w1 IN KB_STDWORLDS p /\
             w2 IN KB_STDWORLDS p`,
  GEN_TAC THEN MATCH_MP_TAC KB_STDREL_INDUCT THEN
  REWRITE_TAC[KB_STANDARD_REL_CAR] THEN 
  INTRO_TAC "!w1 w2; stdw1 stdw2 w2 w1" THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC KB_STDWORLDS_RULES THEN 
   HYP_TAC "stdw1" (REWRITE_RULE[IN_ELIM_THM; KB_STANDARD_WORLD_DEF; 
                                 GEN_STANDARD_WORLD]) THEN
   ASM_REWRITE_TAC[]; 
   MATCH_MP_TAC KB_STDWORLDS_RULES THEN 
   HYP_TAC "stdw2" (REWRITE_RULE[IN_ELIM_THM; KB_STANDARD_WORLD_DEF; 
                                 GEN_STANDARD_WORLD]) THEN
   ASM_REWRITE_TAC[]]);;

let SET_OF_LIST_EQ_KB_STANDARD_REL = prove
 (`!p u1 u2 w1 w2.
     set_of_list u1 = set_of_list w1 /\ NOREPETITION w1 /\
     set_of_list u2 = set_of_list w2 /\ NOREPETITION w2 /\
     KB_STANDARD_REL p u1 u2
     ==> KB_STANDARD_REL p w1 w2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[KB_STANDARD_REL_CAR] THEN
  REWRITE_TAC[IN_ELIM_THM; KB_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD] THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM];
   MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM];
   ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM];
   ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]]);;

let KB_STANDARD_BISIM = new_definition
 `KB_STANDARD_BISIM (p:form) (w1:form list) (w2:form->bool)  <=>
         w1 IN KB_STANDARD_WORLD p /\
         w2 IN KB_STDWORLDS p /\
         set_of_list w1 = w2`;;

let KB_BISIMIMULATION_SET_OF_LIST = prove
(`!p:form. BISIMIMULATION
      (KB_STANDARD_WORLD p,
        KB_STANDARD_REL p,
        STANDARD_EVAL p)
      (KB_STDWORLDS p,
       KB_STDREL p,
       SET_STANDARD_EVAL p)
      (KB_STANDARD_BISIM p)`,
 GEN_TAC THEN 
 REWRITE_TAC[STANDARD_EVAL; SET_STANDARD_EVAL; KB_STANDARD_BISIM; BISIMIMULATION] THEN REPEAT GEN_TAC THEN
 REWRITE_TAC[IN_ELIM_THM; KB_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD] THEN
 STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
 [GEN_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC[IN_SET_OF_LIST];
  ALL_TAC] THEN
 CONJ_TAC THENL
 [INTRO_TAC "![u1]; w1u1" THEN EXISTS_TAC `set_of_list u1:form->bool` THEN
  HYP_TAC "w1u1 -> hp" 
          (REWRITE_RULE[KB_STANDARD_REL_CAR; IN_ELIM_THM; 
                        KB_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC KB_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC KB_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN MATCH_MP_TAC KB_STDREL_RULES THEN
  ASM_REWRITE_TAC[];
  ALL_TAC] THEN
 INTRO_TAC "![u2]; w2u2" THEN EXISTS_TAC `list_of_set u2:form list` THEN
 REWRITE_TAC[CONJ_ACI] THEN
 HYP_TAC "w2u2 -> @x2 y2. x2 y2 x2y2" (REWRITE_RULE[KB_STDREL_CASES]) THEN
 REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
 SIMP_TAC[SET_OF_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
 SIMP_TAC[MEM_LIST_OF_SET; FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
 CONJ_TAC THENL
 [HYP_TAC "x2y2 -> hp" (REWRITE_RULE[KB_STANDARD_REL_CAR; IN_ELIM_THM; 
                        KB_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD]) THEN
  ASM_REWRITE_TAC[];
  ALL_TAC] THEN
 CONJ_TAC THENL
 [ASM_MESON_TAC[KB_STDREL_IMP_KB_STDWORLDS]; ALL_TAC] THEN
 CONJ_TAC THENL
 [MATCH_MP_TAC SET_OF_LIST_EQ_KB_STANDARD_REL THEN
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
 HYP_TAC "x2y2 -> hp" (REWRITE_RULE[KB_STANDARD_REL_CAR; IN_ELIM_THM; 
                        KB_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD]) THEN
 ASM_MESON_TAC[]);;

let KB_COUNTERMODEL_FINITE_SETS = prove
 (`!p. ~ [KB_AX . {} |~ p] ==> ~holds_in (KB_STDWORLDS p, KB_STDREL p) p`,
  INTRO_TAC "!p; p" THEN
  DESTRUCT_TAC "@M. maxM memM M"
    (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ [KB_AX . {} |~ p]`)) THEN
  CLAIM_TAC "stdwM" `M IN KB_STANDARD_WORLD p` THENL 
  [ASM_REWRITE_TAC[IN_ELIM_THM; KB_STANDARD_WORLD_DEF; GEN_STANDARD_WORLD]; ALL_TAC] THEN
  REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP] THEN
  EXISTS_TAC `SET_STANDARD_EVAL p` THEN
  EXISTS_TAC `set_of_list M:form->bool` THEN CONJ_TAC THENL
  [MATCH_MP_TAC KB_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUFFICE_TAC `BISIMIMULATION (KB_STANDARD_WORLD p , KB_STANDARD_REL p, STANDARD_EVAL p)
                              (KB_STDWORLDS p, KB_STDREL p, SET_STANDARD_EVAL p)
                              (KB_STANDARD_BISIM (p:form)) /\
               KB_STANDARD_BISIM p M (set_of_list M) /\
               ~holds (KB_STANDARD_WORLD p,KB_STANDARD_REL p) (STANDARD_EVAL p) p M`
                  [BISIMIMULATION_HOLDS] THENL
  [REPEAT CONJ_TAC THENL 
   [ASM_REWRITE_TAC[KB_BISIMIMULATION_SET_OF_LIST]; 
    ASM_REWRITE_TAC[KB_STANDARD_BISIM] THEN
    MATCH_MP_TAC KB_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]; 
    ASM_MESON_TAC[KB_COUNTERMODEL]]]);;