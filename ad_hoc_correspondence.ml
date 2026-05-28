(* ========================================================================= *)
(* Correspondence Theory: Ad Hoc Polimorphic Code.                           *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

needs "HOLMS/calculus.ml";;
needs "HOLMS/dep_choice.ml";;

(* ------------------------------------------------------------------------- *)
(* Axiom Schemata.                                                           *)
(* ------------------------------------------------------------------------- *)

let D_SCHEMA_DEF = new_definition
  `D_SCHEMA p = (Box p --> Diam p)`;;

let T_SCHEMA_DEF = new_definition
  `T_SCHEMA p = (Box p --> p)`;;

let FOUR_SCHEMA_DEF = new_definition
  `FOUR_SCHEMA p = (Box p --> Box Box p)`;;

let B_SCHEMA_DEF = new_definition
  `B_SCHEMA p = (p --> Box (Diam p))`;;

let FIVE_SCHEMA_DEF = new_definition
   `FIVE_SCHEMA p = (Diam p --> Box Diam p)`;;

let LOB_SCHEMA_DEF = new_definition
  `LOB_SCHEMA p = Box (Box p --> p) --> Box p`;;

let GRZ_SCHEMA_DEF = new_definition
  `GRZ_SCHEMA p = (Box (Box (p --> Box p) --> p) --> p)`;;

(* ------------------------------------------------------------------------- *)
(* Properties of Binary Relationship.                                        *)
(* ------------------------------------------------------------------------- *)

let SERIAL = new_definition
  `SERIAL W R <=> (!w:W. w IN W ==> ?y:W. y IN W /\ (R w y))`;;

let REFLEXIVE = new_definition
  `REFLEXIVE W R <=> (!w:W. w IN W ==> R w w)`;;

let IRREFLEXIVE = new_definition
  `IRREFLEXIVE W R <=> (!x:W. x IN W ==> ~R x x)`;;

let TRANSITIVE = new_definition
  `TRANSITIVE W R <=>
   (!w w' w'':W. w IN W /\ w' IN W /\ w'' IN W /\
                 R w w' /\ R w' w''
                 ==> R w w'')`;;

let SYMMETRIC = new_definition
  `SYMMETRIC W R <=>
   (!w w':W. w IN W /\ w' IN W /\ R w w' ==> R w' w)`;;

let ANTISYMMETRIC = new_definition
  `ANTISYMMETRIC W R <=>
   (!w w':W. w IN W /\ w' IN W /\ R w w' /\ R w' w ==> w = w')`;;

let EUCLIDEAN = new_definition
  `EUCLIDEAN W R <=>
   (!w w' w'':W. w IN W /\ w' IN W /\ w'' IN W /\
                 R w w' /\ R w w''
                 ==> R w'' w')`;;

let WWF = new_definition
  `WWF (<<) <=>
   (!P. (?x:W. P x) /\ (!x. P x ==> x IN fld (<<))
        ==> (?x. P x /\ (!y. ~(x = y) /\ y << x ==> ~P y)))`;;

let WWF_EQ = prove
 (`!(<<). WWF (<<) <=>
          !P. (!x. P x ==> x IN fld (<<))
              ==> ((?x:A. P(x)) <=>
                   (?x. P(x) /\ (!y. ~(x = y) /\ y << x ==> ~P(y))))`,
  GEN_TAC THEN REWRITE_TAC[WWF] THEN EQ_TAC THENL
  [MESON_TAC[];
   INTRO_TAC "hp; !P; ne sub" THEN
   HYP_TAC "hp: +" (SPEC `P:A->bool`) THEN
   ASM_MESON_TAC[]]);;

let WWF_IND = prove
 (`!(<<). WWF(<<) <=>
          !P. (!x:A. ~P x ==> x IN fld (<<))
              ==> (!x. (!y. y << x /\ ~(x = y) ==> P y) ==> P x) ==> !x. P x`,
  GEN_TAC THEN REWRITE_TAC[WWF] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\x:A. ~P(x)`) THEN BETA_TAC THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence Lemmata.                                                   *)
(* ------------------------------------------------------------------------- *)

let MODAL_SER = prove
 (`!W:W->bool R. SERIAL W R <=>
                 (!p. holds_in (W,R) (D_SCHEMA p))`,
  REWRITE_TAC[diam_DEF; D_SCHEMA_DEF] THEN MODAL_SCHEMA_TAC THEN
  MESON_TAC[SERIAL]);;

let MODAL_REFL = prove
 (`!W:W->bool R. REFLEXIVE W R <=> (!p. holds_in (W,R) (T_SCHEMA p))`,
  REWRITE_TAC[REFLEXIVE; T_SCHEMA_DEF] THEN MODAL_SCHEMA_TAC THEN
  MESON_TAC[]);;

let MODAL_TRANS = prove
 (`!W:W->bool R. TRANSITIVE W R <=> (!p. holds_in (W,R) (FOUR_SCHEMA p))`,
  REWRITE_TAC[TRANSITIVE; FOUR_SCHEMA_DEF] THEN
  MODAL_SCHEMA_TAC THEN MESON_TAC[]);;

let MODAL_SYM = prove
 (`!W:W->bool R. SYMMETRIC W R <=>
                 (!p. holds_in (W,R) (B_SCHEMA p))`,
  ASM_REWRITE_TAC[diam_DEF; SYMMETRIC; B_SCHEMA_DEF] THEN MODAL_SCHEMA_TAC THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; REPEAT STRIP_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`\v:W. v = w`; `w:W`]) THEN ASM_MESON_TAC[]);;

let MODAL_EUCL = prove
 (`!W:W->bool R. EUCLIDEAN W R <=>
                 (!p. holds_in (W,R) (FIVE_SCHEMA p))`,
  REWRITE_TAC[diam_DEF; EUCLIDEAN; FIVE_SCHEMA_DEF] THEN MODAL_SCHEMA_TAC THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; REPEAT STRIP_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`\v:W. v = w'`; `w:W`]) THEN
  ASM_MESON_TAC[]);;

let MODAL_TRANSNT = prove
 (`!W:W->bool R. (!x y. R x y ==> x IN W /\ y IN W)
                 ==> (TRANSITIVE W R /\ WF(\x y. R y x) <=>
                      !p. holds_in (W,R) (LOB_SCHEMA p))`,
  REWRITE_TAC[TRANSITIVE; LOB_SCHEMA_DEF] THEN MODAL_SCHEMA_TAC THEN
  DISCH_TAC THEN EQ_TAC THENL
  [INTRO_TAC "TRANS WF" THEN HYP_TAC "WF" (REWRITE_RULE[WF_IND]) THEN
   REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "U" THEN CONJ_TAC THENL
  [X_GEN_TAC `w:W` THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`\v:W. v IN W /\ R w v /\ !w''. w'' IN W /\ R v w'' ==> R w w''`;
    `w:W`]) THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[WF_IND] THEN X_GEN_TAC `P:W->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\x:W. !w:W. x IN W /\ R w x ==> P x`) THEN
  MATCH_MP_TAC MONO_FORALL THEN ASM_MESON_TAC[]);;

let MODAL_RTWN = prove
  (`!W:W->bool R.
     (!x y. R x y ==> x IN W /\ y IN W)
     ==> (REFLEXIVE W R /\ TRANSITIVE W R /\ WWF (\x y. R y x)
     <=> !p. holds_in (W,R) (GRZ_SCHEMA p))`,     
  REWRITE_TAC[REFLEXIVE; TRANSITIVE; GRZ_SCHEMA_DEF] THEN
  INTRO_TAC "!W R; wd" THEN EQ_TAC THENL
  [INTRO_TAC "REFL TRANS WWF" THEN 
   HYP_TAC "WWF" (REWRITE_RULE[WWF_IND]) THEN
   GEN_TAC THEN
   ASM_REWRITE_TAC[holds_in] THEN
   REPEAT GEN_TAC THEN
   ABBREV_TAC `X_0 = {w:W | w IN W /\
                            holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                            ~(holds (W,R) V p w)}` THEN
   ABBREV_TAC `X_1 = {w:W | w IN W /\
                            holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                            ~(holds (W,R) V (Box p) w) /\
                            holds (W,R) V p w}` THEN
   CLAIM_TAC "EMPTY_IN" `(X_0 INTER X_1) = {}:W->bool` THENL
   [REFUTE_THEN MP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `?x. x:W IN X_0 INTER X_1` MP_TAC THENL
    [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
    INTRO_TAC "@x. NON_EMPTY" THEN
    HYP_TAC "NON_EMPTY" (REWRITE_RULE[IN_INTER]) THEN
    SUBGOAL_THEN `~(holds (W,R) V p (x:W)) /\ (holds (W,R) V p (x:W))`
      MP_TAC THENL
    [SUBGOAL_THEN `(x:W) IN
                     {w:W | w IN W /\
                            holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                            ~(holds (W,R) V p w)} /\
                     x IN
                      {w:W | w IN W /\
                             holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                             ~(holds (W,R) V (Box p) w) /\ holds (W,R) V p w}`
                   MP_TAC THENL
      [ASM_MESON_TAC[]; ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
     ASM_MESON_TAC[]];
    DISCH_TAC] THEN
   CLAIM_TAC "EMPTY_X0" `(X_0:W->bool) = {}` THENL
   [CLAIM_TAC "w'_IN_X0_THEN_x_IN_X1"
     `!w'. w' IN (X_0:W->bool) ==> ?x. ((R:W->W->bool) w' x /\ x IN X_1)` THENL
    [REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `(w':W) IN
                   {w | w IN W /\
                        holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                        ~(holds (W,R) V p w)} ` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
     ASM_REWRITE_TAC[IN_ELIM_THM] THEN
     INTRO_TAC "IN_X0_THEN_IN_W IN_X0_THEN_ForA IN_X0_THEN_NonForB" THEN
     CLAIM_TAC "IN_X0_THEN_REFL" `((R:W->W->bool) w' w')` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
     CLAIM_TAC "For1" `holds (W,R) V (Box (p --> Box p) --> p) (w':W)` THENL
     [SUBGOAL_THEN `holds (W,R) V (Box (Box (p --> Box p) --> p)) (w':W)`
      MP_TAC THENL
      [ASM_REWRITE_TAC[];
      MODAL_SCHEMA_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
     CLAIM_TAC "Not_For2" `~ holds (W,R) V (Box (p --> Box p)) (w':W)` THENL
     [SUBGOAL_THEN `~holds (W,R) V p (w':W) /\
                     holds (W,R) V (Box (p --> Box p) --> p) (w':W)` MP_TAC THENL
       [ASM_MESON_TAC[]; MODAL_SCHEMA_TAC THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
     SUBGOAL_THEN `?x. ((R:W->W->bool) w' x /\ holds (W,R) V (p) (x:W) /\
                        ~holds (W,R) V (Box p) (x:W))` MP_TAC THENL
     [SUBGOAL_THEN `~holds (W,R) V (Box (p --> Box p)) (w':W)` MP_TAC THENL
      [ASM_MESON_TAC[];
       MODAL_SCHEMA_TAC THEN ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
       INTRO_TAC "@z. a b @k. c" THEN EXISTS_TAC `z:W` THEN
       REPEAT CONJ_TAC THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
     INTRO_TAC "@x. REL_x p Not_Box_p" THEN EXISTS_TAC `(x:W)` THEN
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN
       `(x:W) IN {w | w IN W /\
                      holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                      ~holds (W,R) V (Box p) w /\ holds (W,R) V p w}`
       MP_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
      [ASM_MESON_TAC[];
       SUBGOAL_THEN `!z:W. R x z ==> holds (W,R) V (Box (p --> Box p) --> p) z`
         MP_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN CLAIM_TAC "REL_z" `(R:W->W->bool) w' z` THENL
        [ASM_MESON_TAC[];
         SUBGOAL_THEN `holds (W,R) V (Box (Box (p --> Box p) --> p)) (w':W)`
           MP_TAC THENL
         [ASM_REWRITE_TAC[];
          MODAL_SCHEMA_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_MESON_TAC[]]];
         MODAL_SCHEMA_TAC THEN ASM_MESON_TAC[]]];
      ASM_MESON_TAC[]];
     ALL_TAC] THEN
    CLAIM_TAC "w'_IN_X1_THEN_x_IN_X0 "
               `! w'. w' IN (X_1:W->bool) ==>
                      ?x. ((R:W->W->bool) w' x /\ x IN X_0)` THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(w':W) IN
                      {w | w IN W /\
                           holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                           ~holds (W,R) V (Box p) w /\ holds (W,R) V p w} ` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      INTRO_TAC "IN_X1_THEN_IN_W IN_X1_THEN_ForA IN_X1_THEN_NonForB IN_X1_THEN_ForC" THEN
      SUBGOAL_THEN `?x. (R:W->W->bool) w' x /\ ~holds (W,R) V p (x:W)` MP_TAC THENL
       [SUBGOAL_THEN `~holds (W,R) V (Box p) (w':W)` MP_TAC THENL
         [ASM_MESON_TAC[]; MODAL_SCHEMA_TAC THEN ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
          INTRO_TAC "@z. (a b) c" THEN EXISTS_TAC `z:W` THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      INTRO_TAC "@x. REL_x Not_p" THEN EXISTS_TAC `(x:W)` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:W) IN
                    {w | w IN W /\
                         holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                         ~(holds (W,R) V p w)}` MP_TAC THENL
      [ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[];
        SUBGOAL_THEN `!z. R x z ==> (holds (W,R) V (Box (p --> Box p) --> p) (z:W))` MP_TAC THENL
        [GEN_TAC THEN DISCH_TAC THEN CLAIM_TAC "REL_z" `(R:W->W->bool) w' z` THENL
         [ASM_MESON_TAC[];
          SUBGOAL_THEN `holds (W,R) V (Box (Box (p --> Box p) --> p)) (w':W)` MP_TAC THENL
          [ASM_REWRITE_TAC[]; MODAL_SCHEMA_TAC THEN DISCH_TAC THEN
           FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]];
         MODAL_SCHEMA_TAC THEN ASM_MESON_TAC[]]];
       ASM_MESON_TAC[]];
      ALL_TAC] THEN
    ABBREV_TAC `(X:W->bool) = X_0 UNION X_1` THEN
    CLAIM_TAC "EMPTY_UN" `(X:W->bool) = {}` THENL
     [SUBGOAL_THEN `WWF (\x y. (R:W->W->bool) y x)` MP_TAC THENL
       [ASM_MESON_TAC[WWF_IND]; ALL_TAC] THEN
      REWRITE_TAC[WWF_EQ] THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `(\x:W. x IN X)`) THEN
      REWRITE_TAC[IN_FLD] THEN ANTS_TAC THENL
       [REWRITE_TAC[IN_FLD] THEN CLAIM_TAC "+" `X:W->bool SUBSET W` THENL
         [MAP_EVERY EXPAND_TAC ["X"; "X_0"; "X_1"] THEN SET_TAC[]; HYP SET_TAC "REFL" []];
        DISCH_TAC] THEN
      SUBGOAL_THEN `~ ?x. x:W IN X` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[MEMBER_NOT_EMPTY;
                        NOT_EXISTS_THM; DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP] THEN
        REWRITE_TAC[TAUT `(~p \/ q) <=> (p ==> q)`] THEN GEN_TAC THEN DISCH_TAC THEN
        SUBGOAL_THEN `(x:W IN X_0 \/ x IN X_1) /\ ~(x IN X_0 /\ x IN X_1)` MP_TAC THENL
         [ASM_MESON_TAC[IN_UNION; DISJOINT; IN_DISJOINT]; ALL_TAC] THEN
        STRIP_TAC THENL
         [SUBGOAL_THEN `(?y. (R:W->W->bool) x y /\ y IN X_1)` MP_TAC THENL
           [ASM_MESON_TAC[]; INTRO_TAC "@y. REL IN" THEN EXISTS_TAC `y:W` THEN
            ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_UNION]];
          SUBGOAL_THEN `(?y. (R:W->W->bool) x y /\ y IN X_0)` MP_TAC THENL
           [ASM_MESON_TAC[]; INTRO_TAC "@y. REL IN" THEN EXISTS_TAC `y:W` THEN
            ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_UNION]]];
        ASM_MESON_TAC[MEMBER_NOT_EMPTY]];
      ASM_MESON_TAC[EMPTY_UNION]];
    ALL_TAC] THEN
   SUBGOAL_THEN `~(?x. x IN {w | w IN (W:W->bool) /\
                       holds (W,R) V (Box (Box (p --> Box p) --> p)) w /\
                       ~holds (W,R) V p w})` MP_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
   REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
   REFUTE_THEN MP_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `?(x:W). (holds (W,R) V (Box (Box (p --> Box p) --> p)) x /\
                          ~holds (W,R) V p x) /\
                         x IN W` MP_TAC THENL
   [UNDISCH_TAC `~holds (W,R) V (Box (Box (p --> Box p) --> p) --> p) (w:W)` THEN
    MODAL_SCHEMA_TAC THEN ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_TAC THEN EXISTS_TAC `w:W` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]; ALL_TAC] THEN
  INTRO_TAC "GRZ" THEN
  CLAIM_TAC "REFL TRANS" `REFLEXIVE (W:W->bool) R /\ TRANSITIVE W R` THENL
  [REWRITE_TAC[MODAL_REFL; T_SCHEMA_DEF; TRANSITIVE] THEN
   CONJ_TAC THENL 
   [HYP_TAC "GRZ -> +" (REWRITE_RULE[]) THEN
    MODAL_SCHEMA_TAC THEN
    ASM_MESON_TAC[]; 
    ALL_TAC] THEN
   REFUTE_THEN MP_TAC THEN
   INTRO_TAC "NOT_TRANS" THEN
   HYP_TAC "NOT_TRANS: @x y z. NOT_TRANS" (REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
   HYP_TAC "GRZ -> +" (REWRITE_RULE[holds_in]) THEN
   ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
   EXISTS_TAC `Atom p` THEN
   EXISTS_TAC `\a:(char)list w. ~(w:W = x) /\ (R:W->W->bool) x w` THEN
   EXISTS_TAC `x:W` THEN
   ASM_REWRITE_TAC[holds; NOT_IMP] THEN
   INTRO_TAC "!w'; w'" THEN
   ASM_CASES_TAC `w'= x:W` THENL
   [ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
     EXISTS_TAC `y:W` THEN
     ASM_REWRITE_TAC[] THEN 
     CONJ_TAC THENL
     [ASM_MESON_TAC[]; 
    EXISTS_TAC `z:W` THEN ASM_MESON_TAC[]];
     ASM_MESON_TAC[]]; ALL_TAC] THEN 
  ASM_REWRITE_TAC[GSYM REFLEXIVE; GSYM TRANSITIVE] THEN
  REFUTE_THEN MP_TAC THEN 
  INTRO_TAC "Not_WWF" THEN
  HYP_TAC "Not_WWF -> +" (REWRITE_RULE[WWF; NOT_EXISTS_THM; IN; DE_MORGAN_THM; 
                                       NOT_FORALL_THM; NOT_IMP; fld; IN_ELIM_THM; 
                                       TAUT `(~p \/ q) <=> (p ==> q)`]) THEN
  INTRO_TAC "@P. (non_empty rel) dist" THEN
  let _,concl = dest_imp(concl (ISPECL[`\x y. (P:W->bool) x /\ P y /\ (R:W->W->bool) x y /\ ~(x = y)`] 
                                DEPENDENT_CHOICE)) in
    SUBGOAL_THEN concl (X_CHOOSE_THEN `w_:num->W` (LABEL_TAC "dep_ch")) THENL 
    [MATCH_MP_TAC DEPENDENT_CHOICE; ALL_TAC] THENL
  [ASM_REWRITE_TAC[fld; IN_ELIM_THM; GSYM MEMBER_NOT_EMPTY] THEN
   ASM_MESON_TAC[]; ALL_TAC] THEN
  HYP_TAC "dep_ch" (REWRITE_RULE[IN_ELIM_THM]) THEN
  ABBREV_TAC `In = {i:num | !j:num. j < i ==> ~(((w_:num->W) j) = w_ i)}` THEN
  POP_ASSUM (LABEL_TAC "In_def") THEN
  HYP_TAC "GRZ -> +" (REWRITE_RULE[holds_in]) THEN 
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  CLAIM_TAC "dep_ch_trans" `!k:num h:num. k <= h ==> R ((w_:num->W) k)  (w_ h)` THENL
  [REPEAT INDUCT_TAC THENL
   [HYP_TAC "REFL" (REWRITE_RULE[REFLEXIVE]) THEN ASM_MESON_TAC[];
    DISCH_THEN (K ALL_TAC) THEN
     HYP_TAC "TRANS" (REWRITE_RULE[TRANSITIVE]) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     EXISTS_TAC `(w_:num->W) h` THEN
     SUBGOAL_THEN `(R:W->W->bool) ((w_:num->W) 0) (w_ h)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ASM_MESON_TAC[]];
    ARITH_TAC;
    ASM_CASES_TAC `SUC k = SUC h` THENL
    [HYP_TAC "REFL" (REWRITE_RULE[REFLEXIVE]) THEN ASM_MESON_TAC[];
     DISCH_TAC THEN 
      HYP_TAC "TRANS" (REWRITE_RULE[TRANSITIVE]) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `(w_:num->W) h` THEN
      REPEAT CONJ_TAC THENL
      [ASM_MESON_TAC[];
       ASM_MESON_TAC[];
       ASM_MESON_TAC[];
       FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
       ASM_MESON_TAC[]]]]; ALL_TAC] THEN
  CLAIM_TAC "ANTSYM" `ANTISYMMETRIC (W:W->bool) (R:W->W->bool)` THENL
  [REFUTE_THEN MP_TAC THEN
   INTRO_TAC "ANTSYM" THEN
   HYP_TAC "ANTSYM: @x y. ANTSYM" (REWRITE_RULE[ANTISYMMETRIC; NOT_FORALL_THM; NOT_IMP]) THEN
   HYP_TAC "GRZ -> +" (REWRITE_RULE[holds_in]) THEN 
   REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
   EXISTS_TAC `Atom p` THEN
   EXISTS_TAC `\a:(char)list w. ~ (w:W = x)` THEN
   EXISTS_TAC `x:W` THEN
   ASM_REWRITE_TAC[] THEN
   ONCE_REWRITE_TAC[holds]  THEN
   REWRITE_TAC [NOT_IMP] THEN
   CONJ_TAC THENL
   [ONCE_REWRITE_TAC[holds] THEN
    INTRO_TAC "!w'; w'_IN xRw'" THEN
    ASM_CASES_TAC `w'=x:W` THENL
    [ONCE_REWRITE_TAC[holds] THEN
     ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
     DISCH_THEN (K ALL_TAC) THEN
     ONCE_REWRITE_TAC[holds] THEN
     REWRITE_TAC[NOT_IMP; NOT_FORALL_THM] THEN
     EXISTS_TAC `y:W` THEN
     ASM_REWRITE_TAC[] THEN
     ONCE_REWRITE_TAC[holds] THEN
     REWRITE_TAC [NOT_IMP] THEN
     ASM_REWRITE_TAC[holds] THEN
     REWRITE_TAC [NOT_FORALL_THM; NOT_IMP] THEN
     EXISTS_TAC `x:W` THEN
     ASM_REWRITE_TAC[holds];
    ASM_REWRITE_TAC[holds]];
   REWRITE_TAC[holds]]; ALL_TAC] THEN
  CLAIM_TAC "0_In" `0 IN In` THENL
  [HYP_TAC "In_def" (GSYM) THEN 
   ASM_REWRITE_TAC[IN_ELIM_THM] THEN ARITH_TAC; ALL_TAC] THEN
  CLAIM_TAC "1_In" `1 IN In` THENL
  [HYP_TAC "In_def" (GSYM) THEN 
   ASM_REWRITE_TAC[IN_ELIM_THM] THEN 
   GEN_TAC THEN
   ASM_CASES_TAC `j = 0` THENL
   [ASM_MESON_TAC[ONE];
    ASM_ARITH_TAC]; ALL_TAC] THEN
  CLAIM_TAC "Prop1_In" 
            `!n:num. 2*n IN In ==> 
               ?m':num. 2*m' +1 IN In /\ R ((w_:num->W) (2 * n)) ((w_:num->W) (2 * m' + 1))` THENL 
  [INTRO_TAC "!n; 2n" THEN 
   ASM_CASES_TAC `2 * (n:num) + 1 IN In` THEN
   POP_ASSUM (LABEL_TAC "n") THENL
   [EXISTS_TAC `n:num` THEN 
   ASM_MESON_TAC[ADD1]; ALL_TAC] THEN
   ASM_CASES_TAC `n = 0` THENL
   [EXISTS_TAC `0` THEN 
   ASM_REWRITE_TAC[ARITH] THEN
   ASM_MESON_TAC[ONE]; ALL_TAC] THEN
   HYP_TAC "n: +"  (REWRITE_RULE[]) THEN
   HYP_TAC "In_def" (GSYM) THEN ASM_REWRITE_TAC[IN_ELIM_THM; NOT_FORALL_THM; NOT_IMP] THEN
   INTRO_TAC "@j. j w_j" THEN
   EXISTS_TAC `n - 1` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[MATCH_MP (ARITH_RULE `~(n = 0) ==> 2 * (n - 1) + 1 = 2 * n - 1`) 
                         (ASSUME `~(n = 0)`)] THEN
    REFUTE_THEN MP_TAC THEN INTRO_TAC "RAA" THEN
    HYP_TAC "RAA: @k. RAA_min RAA_eq" (REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    SUBGOAL_THEN `~ ANTISYMMETRIC (W:W->bool) (R:W->W->bool)` MP_TAC THENL
    [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[ANTISYMMETRIC; NOT_FORALL_THM; NOT_IMP] THEN
    EXISTS_TAC `(w_:num->W) k` THEN
    EXISTS_TAC `(w_:num->W) (k+1)` THEN
    REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[ADD1];
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ASM_MESON_TAC[ADD1]]; ALL_TAC] THEN
   HYP_TAC "TRANS: TR" (REWRITE_RULE[TRANSITIVE]) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `(w_:num->W) j` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]; 
    ASM_MESON_TAC[ADD1]; 
    REWRITE_TAC[MATCH_MP (ARITH_RULE `~(n = 0) ==> 2 * (n - 1) + 1 = 2 * n - 1`) 
                         (ASSUME `~(n = 0)`)] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     MATCH_MP_TAC (ARITH_RULE `j < 2 *n + 1 /\ ~(j = 2 * n) ==> j <= 2*n -1 `) THEN
     ASM_REWRITE_TAC[] THEN REFUTE_THEN MP_TAC THEN DISCH_TAC THEN
     SUBGOAL_THEN `(w_:num->W) (2*n)  = w_ (2 * n + 1)` MP_TAC THENL
     [ASM_MESON_TAC[];ASM_MESON_TAC[ADD1]]]; ALL_TAC] THEN
  CLAIM_TAC "Prop2_In" 
            `!m:num. (2*m + 1) IN In ==> 
               ?n':num. 2*n' IN In /\ R ((w_:num->W) (2 * m + 1)) ((w_:num->W) (2 * n'))` THENL
  [INTRO_TAC "!m; suc_2m" THEN 
   ASM_CASES_TAC `2 * (m:num) + 2 IN In` THEN
   POP_ASSUM (LABEL_TAC "m") THENL
   [EXISTS_TAC `m + 1:num` THEN 
    ASM_REWRITE_TAC[ARITH_RULE `2*(m +1) = 2*m +2`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `2*m +2 = (2*m +1) +1`; GSYM ADD1]; ALL_TAC] THEN   
   HYP_TAC "m: +"  (REWRITE_RULE[]) THEN
   HYP_TAC "In_def" (GSYM) THEN ASM_REWRITE_TAC[IN_ELIM_THM; NOT_FORALL_THM; NOT_IMP] THEN
   INTRO_TAC "@j. j w_j" THEN
   EXISTS_TAC `m:num` THEN
   CONJ_TAC THENL
   [REFUTE_THEN MP_TAC THEN INTRO_TAC "RAA" THEN
    HYP_TAC "RAA: @k. RAA_min RAA_eq" (REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    SUBGOAL_THEN `~ ANTISYMMETRIC (W:W->bool) (R:W->W->bool)` MP_TAC THENL
    [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[ANTISYMMETRIC; NOT_FORALL_THM; NOT_IMP] THEN
    EXISTS_TAC `(w_:num->W) k` THEN
    EXISTS_TAC `(w_:num->W) (k+1)` THEN
    REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[ADD1];
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ASM_MESON_TAC[ADD1]]; ALL_TAC] THEN
   HYP_TAC "TRANS: TR" (REWRITE_RULE[TRANSITIVE]) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `(w_:num->W) j` THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]; 
    ASM_REWRITE_TAC[ARITH_RULE `2*m +2 = (2*m +1) +1`; GSYM ADD1]; 
    REWRITE_TAC[MATCH_MP (ARITH_RULE `~(n = 0) ==> 2 * (n - 1) + 1 = 2 * n - 1`) 
                         (ASSUME `~(n = 0)`)] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     MATCH_MP_TAC (ARITH_RULE `j < 2 *m + 2 /\ ~(j = 2 * m + 1) ==> j <= 2*m `) THEN
     ASM_REWRITE_TAC[] THEN REFUTE_THEN MP_TAC THEN DISCH_TAC THEN
     SUBGOAL_THEN `(w_:num->W) (2*m +1)  = w_ (2 * m + 2)` MP_TAC THENL
     [ASM_MESON_TAC[];
      ASM_REWRITE_TAC[ARITH_RULE `2*m +2 = (2*m +1) +1`; GSYM ADD1]]]; ALL_TAC] THEN
  EXISTS_TAC `Atom p` THEN
  EXISTS_TAC `\a:(char)list x. ~ ?n:num. (2 * n) IN (In:num->bool) /\ x = (w_:num->W) (2 * n)` THEN
  EXISTS_TAC `(w_:num->W) 0` THEN
  CONJ_TAC THENL
  [HYP_TAC "dep_ch -> +" (SPECL [`0`]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[holds] THEN
  REWRITE_TAC[NOT_IMP] THEN
  CONJ_TAC THENL
  [ALL_TAC;
   REWRITE_TAC[holds] THEN
   EXISTS_TAC `0` THEN  ASM_REWRITE_TAC[ARITH]] THEN
  ONCE_REWRITE_TAC[holds] THEN
  INTRO_TAC "!w'; w'_IN Rel_w0_w'" THEN
  ASM_CASES_TAC `?i:num. (2 * i) IN In /\ w' = ((w_:num->W) (2*i))` THENL
  [ALL_TAC;
   REWRITE_TAC[holds] THEN ASM_MESON_TAC[ARITH]] THEN
  ONCE_REWRITE_TAC[holds] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  DISCH_THEN (K ALL_TAC) THEN
  ONCE_REWRITE_TAC[holds] THEN
  REWRITE_TAC[NOT_IMP; NOT_FORALL_THM] THEN
  FIRST_X_ASSUM MP_TAC THEN
  INTRO_TAC "@i. w'_IN_In w'" THEN
  HYP_TAC "Prop1_In -> +" (SPECL [`i:num`]) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  HYP_TAC "w'" (GSYM) THEN ASM_REWRITE_TAC[] THEN
  HYP_TAC "In_def" (GSYM) THEN ASM_REWRITE_TAC[] THEN
  INTRO_TAC "@m'. w_2m'suc_IN_In Rel_w'_w_2m'suc" THEN
  EXISTS_TAC `(w_:num->W) (2 * m' +1)` THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[holds] THEN
  REWRITE_TAC[NOT_IMP] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[holds] THEN
   ASM_REWRITE_TAC[IN_ELIM_THM] THEN 
   STRIP_TAC THEN
   ASM_CASES_TAC `2 * (m':num) + 1 < 2 * (n:num)` THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN  `~((w_:num->W) (2 * n) = w_ (2 * m' + 1))` MP_TAC THENL
  [HYP_TAC "w_2m'suc_IN_In" (REWRITE_RULE[IN_ELIM_THM]) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC (ARITH_RULE `~(a < b) /\ ~(a = b) ==> b < a`) THEN
   ASM_REWRITE_TAC[] THEN 
   ASM_MESON_TAC[EVEN_DOUBLE; ODD_DOUBLE; ADD1; EVEN_AND_ODD]; ALL_TAC] THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ONCE_REWRITE_TAC[holds] THEN
   REWRITE_TAC[NOT_IMP; NOT_FORALL_THM] THEN
   HYP_TAC "Prop2_In -> +" (SPECL [`m':num`]) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   HYP_TAC "In_def" (GSYM) THEN ASM_REWRITE_TAC[] THEN
   INTRO_TAC "@n'. w_2n'_IN_In Rel_w_2m'suc_w_2n'" THEN
   EXISTS_TAC `(w_:num->W) (2 * n')` THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[]; 
    ASM_REWRITE_TAC[holds] THEN ASM_MESON_TAC[]]);;
