(* Proof of the consistency and modal completeness of S5.                     *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)


let S5_AX = new_definition
  `S5_AX = {Diam p --> Box Diam  p | p IN (:form)} UNION {Box p --> p |p IN (:form)}`;;

let S5_UNION = prove
 (`S5_AX = T_AX UNION {Diam p --> Box Diam  p | p IN (:form)}`,
  REWRITE_TAC[S5_AX;T_AX; EXTENSION] THEN
  REWRITE_TAC[UNION;IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]);; 

let FIVE_IN_S5_AX = prove
 (`!q. Diam q --> Box Diam q IN S5_AX`,
  REWRITE_TAC[S5_AX; IN_ELIM_THM; IN_UNIV; UNION] THEN MESON_TAC[]);;

let T_IN_S5_AX = prove
 (`!q. Box q -->  q IN S5_AX`,
  REWRITE_TAC[S5_AX; IN_ELIM_THM; IN_UNIV; UNION] THEN MESON_TAC[]);;

let S5_AX_FIVE = prove
 (`!q. [S5_AX. {} |~ (Diam q --> Box Diam q)]`,
  MESON_TAC[MODPROVES_RULES; FIVE_IN_S5_AX]);;

let S5_AX_T = prove
 (`!q. [S5_AX. {} |~ (Box q --> q)]`,
  MESON_TAC[MODPROVES_RULES; T_IN_S5_AX]);;

(* ------------------------------------------------------------------------- *)
(* Reflexive-Euclidean frames.                                               *)
(* ------------------------------------------------------------------------- *)

let MODAL_EUCL = prove
 (`!W R.
     (!w w' w'':W. w IN W /\ w' IN W /\ w'' IN W /\
                   R w w' /\ R w w''
                   ==> R w'' w') <=>
     (!p. holds_in (W,R) (Diam p --> Box Diam p))`,
  REWRITE_TAC[diam_DEF] THEN MODAL_SCHEMA_TAC THEN EQ_TAC THENL [ASM_MESON_TAC[]; REPEAT STRIP_TAC] THEN 
  FIRST_X_ASSUM (MP_TAC o SPECL [`\v:W. v = w'`; `w:W`]) THEN ASM_MESON_TAC[]);;

let REUCL_DEF = new_definition
  `REUCL =
   {(W:W->bool,R:W->W->bool) |
    ~(W = {}) /\
    (!x y:W. R x y ==> x IN W /\ y IN W) /\
    (!x:W. x IN W ==> R x x) /\
    (!x y z:W. x IN W /\ y IN W /\ z IN W /\ R x y /\ R x z ==> R z y)}`;;

let IN_REUCL = prove
 (`(W:W->bool,R:W->W->bool) IN REUCL <=>
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   (!x:W. x IN W ==> R x x) /\
   (!x y z:W. x IN W /\ y IN W /\ z IN W /\ R x y /\ R x z ==> R z y)`,
  REWRITE_TAC[REUCL_DEF; IN_ELIM_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory: Refl-Euclidean Frames are characteristic for S5.   *)
(* ------------------------------------------------------------------------- *)

g `REUCL:(W->bool)#(W->W->bool)->bool = CHAR S5_AX`;;
e (REWRITE_TAC[EXTENSION; FORALL_PAIR_THM]);;
e (REWRITE_TAC[IN_CHAR; IN_REUCL; IN_FRAME]);;
e (REPEAT GEN_TAC);;
e EQ_TAC;;
 e (INTRO_TAC "not_empty Rel Refl Eucl");;
 e (ASM_REWRITE_TAC[S5_UNION]);;
  e (GEN_TAC THEN INTRO_TAC "DISJ" THEN  FIRST_ASSUM (fun th -> DISJ_CASES_TAC (REWRITE_RULE[IN_UNION;T_AX; IN_ELIM_THM] th)));;
    e (CLAIM_TAC "@q. form T" `? p'. p' IN (:form) /\ p = Box p' --> p'`);;
      e (ASM_REWRITE_TAC[]);;
    e (ASM_MESON_TAC[MODAL_REFL]);;
    e (CLAIM_TAC "@q. form 5" `? p'. p' IN (:form) /\ p = Diam p' --> Box Diam p'`);;
      e (ASM_REWRITE_TAC[]);;
    e (ASM_MESON_TAC[MODAL_EUCL]);;
 e (INTRO_TAC "(not_empty Rel) char");;
  e (ASM_MESON_TAC[MODAL_REFL; MODAL_EUCL; T_IN_S5_AX; FIVE_IN_S5_AX]);;
let REUCL_CHAR_S5 = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. Reflexive-Euclidean Frames                      *)
(* ------------------------------------------------------------------------- *)

let S5_REUCL_VALID = prove
 (`!H p. [S5_AX . H |~ p] /\
         (!q. q IN H ==> REUCL:(W->bool)#(W->W->bool)->bool |= q)
         ==> REUCL:(W->bool)#(W->W->bool)->bool |= p`,
  ASM_MESON_TAC[GEN_CHAR_VALID; REUCL_CHAR_S5]);;

(* ------------------------------------------------------------------------- *)
(* Finite Reflexive-Euclidean Frames are appropriate for S5.                 *)
(* ------------------------------------------------------------------------- *)

let REF_DEF = new_definition
 `REF =
  {(W:W->bool,R:W->W->bool) |
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W /\
   (!x. x IN W ==> R x x) /\
   (!x y z:W. x IN W /\ y IN W /\ z IN W /\ R x y /\ R x z ==> R z y)}`;;

let IN_REF = prove
 (`(W:W->bool,R:W->W->bool) IN REF <=>
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W /\
   (!x. x IN W ==> R x x) /\
   (!x y z:W. x IN W /\ y IN W /\ z IN W /\ R x y /\ R x z ==> R z y)`,
  REWRITE_TAC[REF_DEF; IN_ELIM_PAIR_THM]);;

let REF_SUBSET_REUCL = prove
 (`REF:(W->bool)#(W->W->bool)->bool SUBSET REUCL`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_REF; IN_REUCL] THEN MESON_TAC[]);;

g `REF: (W->bool)#(W->W->bool)->bool = APPR S5_AX`;;
e (REWRITE_TAC[EXTENSION; FORALL_PAIR_THM]);;
e (REPEAT GEN_TAC);;
e (REWRITE_TAC[APPR_CAR]);;
e EQ_TAC;;
 e (INTRO_TAC "In_REF");;
 e CONJ_TAC;;
  e (ASM_MESON_TAC [REF_SUBSET_REUCL; SUBSET; REUCL_CHAR_S5]);;
  e (HYP_TAC "In_REF" (REWRITE_RULE[IN_REF]));;
   e (ASM_REWRITE_TAC[]);;
 e (INTRO_TAC "In_Char Fin");;
  e (SUBGOAL_THEN  `(p1:W->bool,p2:W->W->bool) IN REUCL` MP_TAC);;
   e (ASM_MESON_TAC[REUCL_CHAR_S5; EXTENSION; FORALL_PAIR_THM]);;
  e (ASM_REWRITE_TAC[IN_REUCL; IN_REF]);;
let REF_APPR_S5 = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. REF.                                            *)
(* ------------------------------------------------------------------------- *)

let S5_REF_VALID = prove
 (`!p. [S5_AX . {} |~ p] ==> REF:(W->bool)#(W->W->bool)->bool |= p`,
  MESON_TAC[GEN_APPR_VALID; REF_APPR_S5]);;

(* ------------------------------------------------------------------------- *)
(* Proof of Consistency of S5.                                               *)
(* ------------------------------------------------------------------------- *)

let S5_CONSISTENT = prove
 (`~ [S5_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] S5_REF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM;
              IN_REF; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. x = 0 /\ x = y`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Theorems of S5.                                                           *)
(* ------------------------------------------------------------------------- *)
let S5_imp_Diam = prove
 (`!q. [S5_AX. {} |~ (q --> Diam q)]`,
  ASM_REWRITE_TAC[diam_DEF] THEN
  ASM_MESON_TAC [S5_AX_T; MLK_not_not_th; MLK_imp_mp_subst; MLK_iff_refl_th; MLK_iff_sym; MLK_contrapos_eq]);;

g `[S5_AX . {} |~ Box q --> Box Box q]`;;
e (MATCH_MP_TAC MLK_imp_trans);;
e (EXISTS_TAC `Box Diam Box q`);;
e CONJ_TAC;;
 e (MATCH_MP_TAC MLK_imp_trans);;
  e (EXISTS_TAC `Diam Box q`);;
  e CONJ_TAC;;
   e (MATCH_ACCEPT_TAC S5_imp_Diam);;
   e (MATCH_ACCEPT_TAC S5_AX_FIVE);;
 e (MATCH_MP_TAC MLK_imp_box);;
  e (CLAIM_TAC "contra_five_instance" `[S5_AX . {} |~ Not Box Diam Not q --> Not Diam Not q]`);;
    e (ASM_MESON_TAC[MLK_contrapos_eq; S5_AX_FIVE]);;
  e (HYP_TAC "contra_five_instance" (REWRITE_RULE[diam_DEF]));;
  e (ASM_REWRITE_TAC[diam_DEF]);;
  e (ASM_MESON_TAC [MLK_not_not_th; MLK_imp_mp_subst; MLK_iff_refl_th; MLK_iff_sym; MLK_not_subst; MLK_box_subst]);;
let S5_AX_FOUR = top_thm();;  

(* ------------------------------------------------------------------------- *)
(* S5 standard frames and models.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Standard Frame.                                                           *)
(* ------------------------------------------------------------------------- *)

let S5_STANDARD_FRAME_DEF = new_definition
  `S5_STANDARD_FRAME p = GEN_STANDARD_FRAME S5_AX p`;;

let IN_S5_STANDARD_FRAME = prove
  (`!p W R. (W,R) IN S5_STANDARD_FRAME p <=>
            W = {w | MAXIMAL_CONSISTENT S5_AX p w /\
                     (!q. MEM q w ==> q SUBSENTENCE p)} /\
            (W,R) IN REF /\
            (!q w. Box q SUBFORMULA p /\ w IN W
                   ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`,
 REPEAT GEN_TAC THEN
 REWRITE_TAC[S5_STANDARD_FRAME_DEF; IN_GEN_STANDARD_FRAME] THEN
 EQ_TAC THEN MESON_TAC[REF_APPR_S5]);;

(* ------------------------------------------------------------------------- *)
(* Standard model.                                                           *)
(* ------------------------------------------------------------------------- *)

let S5_STANDARD_MODEL_DEF = new_definition
  `S5_STANDARD_MODEL = GEN_STANDARD_MODEL S5_AX`;;

let REF_SUBSET_FRAME = prove
 (`REF:(W->bool)#(W->W->bool)->bool SUBSET FRAME`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM] THEN INTRO_TAC "![W] [R]" THEN
  REWRITE_TAC[IN_REF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_FRAME]);;

let S5_STANDARD_MODEL_CAR = prove
 (`!W R p V.
     S5_STANDARD_MODEL p (W,R) V <=>
     (W,R) IN S5_STANDARD_FRAME p /\
     (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[S5_STANDARD_MODEL_DEF; GEN_STANDARD_MODEL_DEF] THEN
  REWRITE_TAC[IN_S5_STANDARD_FRAME; IN_GEN_STANDARD_FRAME] THEN
  EQ_TAC THEN ASM_MESON_TAC[REF_APPR_S5]);;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let S5_TRUTH_LEMMA = prove
 (`!W R p V q.
     ~ [S5_AX . {} |~ p] /\
     S5_STANDARD_MODEL p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REWRITE_TAC[S5_STANDARD_MODEL_DEF] THEN MESON_TAC[GEN_TRUTH_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Accessibility lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let S5_STANDARD_REL_DEF = new_definition
  `S5_STANDARD_REL p w x <=>
   GEN_STANDARD_REL S5_AX p w x /\
   (!B. MEM (Box B) w <=> MEM (Box B) x)`;;

let S5_STANDARD_REL_CAR = prove
 (`!p w x.
     S5_STANDARD_REL p w x <=>
     MAXIMAL_CONSISTENT S5_AX p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT S5_AX p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
     (!B. MEM (Box B) w <=> MEM (Box B) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S5_STANDARD_REL_DEF; GEN_STANDARD_REL] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA THEN
  EXISTS_TAC `S5_AX` THEN EXISTS_TAC `p:form` THEN EXISTS_TAC `[Box B]` THEN
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
  ASM_REWRITE_TAC[CONJLIST] THEN ASM_MESON_TAC[S5_AX_T]);;

 let REF_MAXIMAL_CONSISTENT = prove
 (`!p. ~ [S5_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT S5_AX p M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)},
            S5_STANDARD_REL p)
           IN REF `,
  INTRO_TAC "!p; p" THEN
  MP_TAC (ISPECL [`S5_AX`; `p:form`] GEN_FINITE_FRAME_MAXIMAL_CONSISTENT) THEN
  REWRITE_TAC[IN_FINITE_FRAME] THEN INTRO_TAC "gen_max_cons" THEN
  ASM_REWRITE_TAC[IN_REF] THEN
  (* Nonempty *)
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Well-defined *)
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[S5_STANDARD_REL_DEF] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Finite *)
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Reflexive *)
  CONJ_TAC THENL [REWRITE_TAC[IN_ELIM_THM; S5_STANDARD_REL_CAR] THEN
  INTRO_TAC "!x; (max_cons) (imp)" THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN INTRO_TAC "box_mem" THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA THEN
  EXISTS_TAC `S5_AX` THEN EXISTS_TAC `p:form` THEN EXISTS_TAC `[Box B]` THEN
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
  ASM_REWRITE_TAC[CONJLIST] THEN ASM_MESON_TAC[S5_AX_T]; ALL_TAC]
  THEN
  (* Transitive *)
 REWRITE_TAC[IN_ELIM_THM; S5_STANDARD_REL_CAR] THEN
  INTRO_TAC "!x y z; (x1 x2) (y1 y2) (z1 z2) +" THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);; 

  
g `!p w q.
     ~ [S5_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT S5_AX p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     Box q SUBFORMULA p /\
     (!x. S5_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`;;
e (INTRO_TAC "!p w q; p  maxw subw boxq rrr");;
e (REFUTE_THEN (LABEL_TAC "contra") THEN
  REMOVE_THEN "rrr" MP_TAC THEN REWRITE_TAC[NOT_FORALL_THM]);;
e (CLAIM_TAC "consistent_X"
    `CONSISTENT S5_AX (CONS (Not q)
                           (APPEND (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
                                   (FLATMAP (\x. match x with Not Box e -> [Not Box e] | _ -> []) w)))`);;
  e (REMOVE_THEN "contra" MP_TAC);;
  e (REWRITE_TAC[CONSISTENT; CONTRAPOS_THM]);;
  e (INTRO_TAC "incons" THEN MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA);;
  e (MAP_EVERY EXISTS_TAC
       [`S5_AX`;
        `p:form`;
        `APPEND (FLATMAP (\x. match x with Not Box e -> [Not Box e] | _ -> []) w) (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)`]);;
  e (ASM_REWRITE_TAC[]);;
  e CONJ_TAC;;
   e GEN_TAC;;
    e (ASM_REWRITE_TAC[MEM_APPEND]);;
    e (ASM_REWRITE_TAC[MEM_FLATMAP_LEMMA_2; MEM_FLATMAP_LEMMA_3 ] THEN ASM_MESON_TAC[]);;
   e (MATCH_MP_TAC MLK_imp_trans);;
    e (EXISTS_TAC `CONJLIST (MAP (Box) (APPEND ( (FLATMAP  (\x. match x with Not Box e -> [Not Box e] | _ -> []) w))
                                         (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)))`);;
    e CONJ_TAC;;
     e (MATCH_MP_TAC (CONJLIST_IMP_CONJLIST));;  
      e GEN_TAC;;
      e (ASM_REWRITE_TAC[MAP_APPEND; MEM_APPEND; MEM_MAP; MEM_FLATMAP_LEMMA_3; MEM_FLATMAP_LEMMA_2]);;
      e STRIP_TAC;;
       e (EXISTS_TAC `x:form`);;
        e CONJ_TAC;;
        e DISJ1_TAC;;
        e (EXISTS_TAC `q':form`);;
        e (ASM_REWRITE_TAC[]);;
        e (ASM_REWRITE_TAC[]);;
        e (SUBGOAL_THEN `[S5_AX . {} |~ Diam Not q' --> Box Diam Not q']` MP_TAC);;
          e (ASM_MESON_TAC [S5_AX_FIVE]);;
        e (ASM_REWRITE_TAC[diam_DEF]);;
        e DISCH_TAC;;
        e (CLAIM_TAC "S5_first"  `[S5_AX . {} |~ Not Box Not Not q' <-> Not Box q']`);;
          e (ASM_MESON_TAC[MLK_not_subst; MLK_box_subst; MLK_not_not_th]);;
        e (CLAIM_TAC "S5_first"  `[S5_AX . {} |~ Box Not Box Not Not q' <-> Box Not Box q']`);;
          e (ASM_MESON_TAC[MLK_not_subst; MLK_box_subst; MLK_not_not_th]);;
        e (ASM_MESON_TAC[MLK_imp_mp_subst]);;
       e (EXISTS_TAC `x:form`);;
         e CONJ_TAC;;
         e DISJ2_TAC;;
         e (EXISTS_TAC `q':form`);;
         e (ASM_REWRITE_TAC[]);;
         e (ASM_REWRITE_TAC[]);;
       e (MATCH_ACCEPT_TAC S5_AX_FOUR);;
    e (CLAIM_TAC "XIMP" `!y l. [S5_AX . {} |~ Not (Not y && CONJLIST l)]
                                ==> [S5_AX . {} |~ (CONJLIST (MAP (Box) l)) --> Box(y)]`);;
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
       e (CLAIM_TAC "or" `[S5_AX . {} |~ Not Not q || 
                                         Not  (CONJLIST (FLATMAP (\x. match x with Not Box e -> [Not Box e] | _ -> []) w) &&
                                               CONJLIST  (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)) ]`);;
         e (ASM_MESON_TAC [MLK_or_introl]);;

       e (CLAIM_TAC "eq" `[S5_AX . {} |~ Not (Not q && (CONJLIST (FLATMAP (\x. match x with Not Box e -> [Not Box e] | _ -> []) w)) 
                                                && CONJLIST  (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)) 
                                     <-> Not Not q || Not (CONJLIST (FLATMAP (\x. match x with Not Box e -> [Not Box e] | _ -> []) w)
                                                           && (CONJLIST  (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)))]`);;
         e (ASM_MESON_TAC[MLK_de_morgan_and_th]);;
    
       e (CLAIM_TAC "elim_append" `[S5_AX . {} |~ Not (Not q && (CONJLIST (FLATMAP (\x. match x with Not Box e -> [Not Box e] | _ -> []) w) &&
                                                    CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)))]`);;
         e (ASM_MESON_TAC[MLK_iff_mp;MLK_iff_sym]);;
       e (MATCH_MP_TAC MLK_not_subst_th);;
       e (EXISTS_TAC `Not q &&
                      CONJLIST (FLATMAP (\x. match x with Not Box e -> [Not Box e] | _ -> []) w) &&
                      CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)`);;
       e (ASM_REWRITE_TAC[]);;
       e (MATCH_MP_TAC MLK_and_subst_th);;
       e (ASM_REWRITE_TAC[MLK_iff_refl_th]);;
       e (ASM_MESON_TAC [MLK_iff_trans; MLK_iff_sym; CONJLIST_APPEND; APPEND]);;
       e DISCH_TAC;;
       e (MATCH_MP_TAC MLK_iff_mp);;
       e (EXISTS_TAC `Not (Not q &&
                           CONJLIST (APPEND (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
                                            (FLATMAP (\x. match x with Not Box e -> [Not Box e] | _ -> []) w)))`);;
       e (ASM_REWRITE_TAC[]);;
       e (MATCH_MP_TAC MLK_not_subst);;
       e (MATCH_MP_TAC MLK_and_subst_th);;
       e (ASM_REWRITE_TAC[MLK_iff_refl_th; CONJLIST_APPEND_SYM]);;
e (MP_TAC (SPECL
    [`S5_AX`;
     `p:form`;
     `CONS (Not q)
           (APPEND (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
      (FLATMAP (\x. match x with Not Box e -> [Not Box e] | _ -> []) w))`]
    EXTEND_MAXIMAL_CONSISTENT));;
e ANTS_TAC;;
 e (ASM_REWRITE_TAC[MEM] THEN GEN_TAC THEN STRIP_TAC THEN
     REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC));;
  e (MATCH_MP_TAC SUBFORMULA_IMP_NEG_SUBSENTENCE);;
  e (HYP MESON_TAC "boxq"
       [SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
  e (UNDISCH_TAC `MEM q'
      (APPEND (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
      (FLATMAP (\x. match x with Not Box e -> [Not Box e] | _ -> []) w))`);;
  e (REWRITE_TAC[MEM_APPEND; MEM_FLATMAP_LEMMA_2; MEM_FLATMAP_LEMMA_3]);;
  e (DISCH_TAC);;
  e (FIRST_ASSUM (fun th -> DISJ_CASES_TAC (REWRITE_RULE[] th)));;
  e (UNDISCH_TAC `exists q. q' = Box q /\ MEM q' w`);;
  e (INTRO_TAC "@y. q' MEM");;
  e (POP_ASSUM MP_TAC);;
    e (ASM_REWRITE_TAC[]);;
  e (UNDISCH_TAC `exists q. q' = Not Box q /\ MEM (Not Box q) w`);;
  e (INTRO_TAC "@y. q' MEM");;
  e (POP_ASSUM MP_TAC);;
    e (ASM_REWRITE_TAC[]);;
e (INTRO_TAC "@X. maxX subX subl");;
 e (EXISTS_TAC `X:form list`);;
 e (ASM_REWRITE_TAC[NOT_IMP]);;
 e (ASM_REWRITE_TAC[S5_STANDARD_REL_CAR]);;
 e CONJ_TAC;; 
  e (HYP_TAC "subl" (REWRITE_RULE[SUBLIST; MEM; MEM_APPEND; MEM_FLATMAP_LEMMA_2; MEM_FLATMAP_LEMMA_3]));;
   e (GEN_TAC THEN EQ_TAC);;
   e (ASM_MESON_TAC[]);;
   r 1;;
  e (HYP_TAC "subl" (REWRITE_RULE[SUBLIST]));;
   e (HYP_TAC "subl: +" (SPEC `Not q` o REWRITE_RULE[SUBLIST]));;
   e (IMP_REWRITE_TAC[GSYM MAXIMAL_CONSISTENT_MEM_NOT]);;
   e STRIP_TAC;;
   e CONJ_TAC;;
   r 1;;
   e (MATCH_MP_TAC SUBFORMULA_TRANS);;
  e (EXISTS_TAC `Box (q:form)`);;
  e (ASM_REWRITE_TAC[]);;
  e (ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
  r 1;;
  e (REMOVE_THEN "" MATCH_MP_TAC THEN REWRITE_TAC[MEM]);;
  (**)
  e DISCH_TAC;;
  e (REFUTE_THEN (LABEL_TAC "contra"));;
  e (CLAIM_TAC "contra_mem" `MEM (Not Box B) w`);;
    e (CLAIM_TAC "contra_sub" ` Box B SUBFORMULA p`);;
      e (CLAIM_TAC "contra_sub" ` Box B SUBSENTENCE p`);;
        e (ASM_MESON_TAC[]);;
      e (HYP_TAC "contra_sub" (REWRITE_RULE[SUBSENTENCE_CASES]));;
      e (FIRST_ASSUM (fun th -> DISJ_CASES_TAC (REWRITE_RULE[] th)));;
      e (ASM_MESON_TAC[]);; 
      e (REFUTE_THEN (LABEL_TAC "contra_not"));;
      e (ASM_MESON_TAC[form_DISTINCT]);;
    e (ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT]);;
  e (ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT; CONSISTENT_LEMMA]);;
let S5_ACCESSIBILITY_LEMMA = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Modal completeness theorem for S5.                                        *)
(* ------------------------------------------------------------------------- *)

g `!p. ~ [S5_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT S5_AX p M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)},
            S5_STANDARD_REL p)
           IN S5_STANDARD_FRAME p`;;
e (INTRO_TAC "!p; not_theor_p");;
e (REWRITE_TAC [IN_S5_STANDARD_FRAME]);;
e CONJ_TAC;;
 e (MATCH_MP_TAC REF_MAXIMAL_CONSISTENT);;
 e (ASM_REWRITE_TAC[]);;
 e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (INTRO_TAC "!q w; boxq maxw subw");;
e EQ_TAC;;
 e (ASM_MESON_TAC[S5_STANDARD_REL_DEF; GEN_STANDARD_REL]);;
e (ASM_MESON_TAC[S5_ACCESSIBILITY_LEMMA]);;
let S5F_IN_S5_STANDARD_FRAME = top_thm();;

let S5_COUNTERMODEL = prove
 (`!M p.
     ~ [S5_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT S5_AX p M /\
     MEM (Not p) M /\
     (!q. MEM q M ==> q SUBSENTENCE p)
     ==>
     ~holds
        ({M | MAXIMAL_CONSISTENT S5_AX p M /\
              (!q. MEM q M ==> q SUBSENTENCE p)},
         S5_STANDARD_REL p)
        (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
        p M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC GEN_COUNTERMODEL THEN
  EXISTS_TAC `S5_AX` THEN ASM_REWRITE_TAC[GEN_STANDARD_MODEL_DEF] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[S5F_IN_S5_STANDARD_FRAME; S5_STANDARD_FRAME_DEF];
   ALL_TAC] THENL
  [ASM_MESON_TAC[IN_ELIM_THM]]);;

g `!p. REF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [S5_AX . {} |~ p]`;;
e (GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM]);;
e (INTRO_TAC "p_not_theor");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT S5_AX p M /\
                     (!q. MEM q M ==> q SUBSENTENCE p)},
                S5_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC);;
e (MATCH_MP_TAC REF_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `({M | MAXIMAL_CONSISTENT S5_AX p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
                  S5_STANDARD_REL p)
                 IN GEN_STANDARD_FRAME S5_AX p`
                MP_TAC);;
 e (ASM_MESON_TAC[S5F_IN_S5_STANDARD_FRAME; S5_STANDARD_FRAME_DEF]);;
e (ASM_MESON_TAC[GEN_COUNTERMODEL_ALT]);;
let S5_COMPLETENESS_THM = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* Modal completeness for S5 for models on a generic (infinite) domain.      *)
(* ------------------------------------------------------------------------- *)

let S5_COMPLETENESS_THM_GEN = prove
 (`!p. INFINITE (:A) /\ REF:(A->bool)#(A->A->bool)->bool |= p
       ==> [S5_AX . {} |~ p]`,
  SUBGOAL_THEN
    `INFINITE (:A)
     ==> !p. REF:(A->bool)#(A->A->bool)->bool |= p
             ==> REF:(form list->bool)#(form list->form list->bool)->bool |= p`
    (fun th -> MESON_TAC[th; S5_COMPLETENESS_THM]) THEN
  ASM_MESON_TAC[REF_APPR_S5; GEN_LEMMA_FOR_GEN_COMPLETENESS]);;

(* ------------------------------------------------------------------------- *)
(* Simple decision procedure for S5.                                         *)
(* ------------------------------------------------------------------------- *)

let S5_TAC : tactic =
  MATCH_MP_TAC S5_COMPLETENESS_THM THEN
  REWRITE_TAC[diam_DEF; valid; FORALL_PAIR_THM; holds_in; holds;
              IN_REF; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[];;

let S5_RULE tm =
  prove(tm, REPEAT GEN_TAC THEN S5_TAC);;

S5_RULE `!p q r. [S5_AX . {} |~ p && q && r --> p && r]`;;
S5_RULE `!p. [S5_AX . {} |~ Box p --> Box (Box p)]`;;
S5_RULE `!p q. [S5_AX . {} |~  Box (p --> q) && Box p --> Box q]`;;
S5_RULE `!p q. [S5_AX . {} |~  Box p --> p]`;;
S5_RULE `!p q. [S5_AX . {} |~ Box p --> Diam p]`;;
S5_RULE `!p q. [S5_AX . {} |~ p --> Box Diam p]`;;
(*S5_RULE `!p. [S5_AX . {} |~ Box (Box p --> p) --> Box p]`;; *)
(*S5_RULE `[S5_AX . {} |~ Box (Box False --> False) --> Box False]`;;*)

(* ------------------------------------------------------------------------- *)
(* Countermodel using set of formulae (instead of lists of formulae).        *)
(* ------------------------------------------------------------------------- *)


let S5_STDWORLDS_RULES,S5_STDWORLDS_INDUCT,S5_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT S5_AX p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN S5_STDWORLDS p`;;

let S5_STDREL_RULES,S5_STDREL_INDUCT,S5_STDREL_CASES = new_inductive_definition
  `!w1 w2. S5_STANDARD_REL p w1 w2
           ==> S5_STDREL p (set_of_list w1) (set_of_list w2)`;;

let S5_STDREL_IMP_S5_STDWORLDS = prove
 (`!p w1 w2. S5_STDREL p w1 w2 ==>
             w1 IN S5_STDWORLDS p /\
             w2 IN S5_STDWORLDS p`,
  GEN_TAC THEN MATCH_MP_TAC S5_STDREL_INDUCT THEN
  REWRITE_TAC[S5_STANDARD_REL_CAR] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC S5_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;

let SET_OF_LIST_EQ_S5_STANDARD_REL = prove
 (`!p u1 u2 w1 w2.
     set_of_list u1 = set_of_list w1 /\ NOREPETITION w1 /\
     set_of_list u2 = set_of_list w2 /\ NOREPETITION w2 /\
     S5_STANDARD_REL p u1 u2
     ==> S5_STANDARD_REL p w1 w2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S5_STANDARD_REL_CAR] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]; ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]);;

let S5_BISIMIMULATION_SET_OF_LIST = prove
(`!p. BISIMIMULATION
      (
        {M | MAXIMAL_CONSISTENT S5_AX p M /\
             (!q. MEM q M ==> q SUBSENTENCE p)},
        S5_STANDARD_REL p,
        (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
      )
      (S5_STDWORLDS p,
       S5_STDREL p,
       (\a w. Atom a SUBFORMULA p /\ Atom a IN w))
      (\w1 w2.
         MAXIMAL_CONSISTENT S5_AX p w1 /\
         (!q. MEM q w1 ==> q SUBSENTENCE p) /\
         w2 IN S5_STDWORLDS p /\
         set_of_list w1 = w2)`,
 GEN_TAC THEN REWRITE_TAC[BISIMIMULATION] THEN REPEAT GEN_TAC THEN
 STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
 [GEN_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC[IN_SET_OF_LIST];
  ALL_TAC] THEN
 CONJ_TAC THENL
 [INTRO_TAC "![u1]; w1u1" THEN EXISTS_TAC `set_of_list u1:form->bool` THEN
  HYP_TAC "w1u1 -> hp" (REWRITE_RULE[S5_STANDARD_REL_CAR]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC S5_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC S5_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN MATCH_MP_TAC S5_STDREL_RULES THEN
  ASM_REWRITE_TAC[];
  ALL_TAC] THEN
 INTRO_TAC "![u2]; w2u2" THEN EXISTS_TAC `list_of_set u2:form list` THEN
 REWRITE_TAC[CONJ_ACI] THEN
 HYP_TAC "w2u2 -> @x2 y2. x2 y2 x2y2" (REWRITE_RULE[S5_STDREL_CASES]) THEN
 REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
 SIMP_TAC[SET_OF_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
 SIMP_TAC[MEM_LIST_OF_SET; FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
 CONJ_TAC THENL
 [HYP_TAC "x2y2 -> hp" (REWRITE_RULE[S5_STANDARD_REL_CAR]) THEN
  ASM_REWRITE_TAC[];
  ALL_TAC] THEN
 CONJ_TAC THENL
 [ASM_MESON_TAC[S5_STDREL_IMP_S5_STDWORLDS]; ALL_TAC] THEN
 CONJ_TAC THENL
 [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN
 EXISTS_TAC `y2:form list` THEN
 SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
 SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
 ASM_MESON_TAC[S5_STANDARD_REL_CAR];
 ALL_TAC] THEN
 MATCH_MP_TAC SET_OF_LIST_EQ_S5_STANDARD_REL THEN
  EXISTS_TAC `x2:form list` THEN EXISTS_TAC `y2:form list` THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET;
           FINITE_SET_OF_LIST] THEN
  ASM_MESON_TAC[MAXIMAL_CONSISTENT]);;

let S5_COUNTERMODEL_FINITE_SETS = prove
 (`!p. ~ [S5_AX . {} |~ p] ==> ~holds_in (S5_STDWORLDS p, S5_STDREL p) p`,
  INTRO_TAC "!p; p" THEN
  DESTRUCT_TAC "@M. max mem subf"
    (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ [S5_AX . {} |~ p]`)) THEN
  REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP] THEN
  ASSUM_LIST (LABEL_TAC "hp" o MATCH_MP S5_COUNTERMODEL o
                end_itlist CONJ o rev) THEN
  EXISTS_TAC `\a w. Atom a SUBFORMULA p /\ Atom a IN w` THEN
  EXISTS_TAC `set_of_list M:form->bool` THEN CONJ_TAC THENL
  [MATCH_MP_TAC S5_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "hp" MP_TAC THEN
  MATCH_MP_TAC (MESON[] `(p <=> q) ==> (~p ==> ~q)`) THEN
  MATCH_MP_TAC BISIMIMULATION_HOLDS THEN
  EXISTS_TAC`\w1 w2. MAXIMAL_CONSISTENT S5_AX p w1 /\
                     (!q. MEM q w1 ==> q SUBSENTENCE p) /\
                     w2 IN S5_STDWORLDS p /\
                     set_of_list w1 = w2` THEN
  ASM_REWRITE_TAC[S5_BISIMIMULATION_SET_OF_LIST] THEN
  MATCH_MP_TAC S5_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;

