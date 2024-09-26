(* ========================================================================= *)
(* Decision procedure for the provability logic GL.                                          *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

let COMPLETENESS_NUM =
  let COMPLETENESS_THEOREM_NUM =
    REWRITE_RULE[num_INFINITE]
      (INST_TYPE [`:num`,`:A`] COMPLETENESS_THEOREM_GEN)
  and HOLDS_BOX_EQ = prove
   (`!W R p w:A.
       ITF (W,R) /\ w IN W
       ==> (holds (W,R) V (Box p) w <=>
            (!y. y IN W /\ R w y ==> holds (W,R) V (Box p --> p) y))`,
    INTRO_TAC "!W R p w; WR w" THEN REWRITE_TAC[holds] THEN
    EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    CLAIM_TAC "tnt" `TRANSNT(W:A->bool,R)` THENL
    [MATCH_MP_TAC ITF_NT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC
     (REWRITE_RULE [holds_in; holds; RIGHT_IMP_FORALL_THM; IMP_IMP]
                   TRANSNT_IMP_LOB) THEN
    EXISTS_TAC `w:A` THEN HYP_TAC "tnt" (REWRITE_RULE[TRANSNT]) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]) in
 prove
 (`!p. (!W R V w:num.
          (!x y z:num. R y z ==> R x y ==> R x z) /\
          (!p w. w IN W /\
                 (!y. y IN W /\ R w y /\ holds (W,R) V (Box p) y
                      ==> holds (W,R) V p y)
                 ==> holds (W,R) V (Box p) w) /\
          (!Q p w. w IN W /\
                   (!y. y IN W /\ R w y /\ holds (W,R) V (Box p) y
                        ==> holds (W,R) V p y \/ Q)
                   ==> holds (W,R) V (Box p) w \/ Q) /\
          (!w w'. R w w'
                  ==> !p. holds (W,R) V (Box p) w ==> holds (W,R) V p w') /\
          (!p w. holds (W,R) V (Box p) w
                 ==> !w'. R w w' ==> holds (W,R) V p w') /\
          w IN W
          ==> holds (W,R) V p w)
       ==> [GL_AX . {} |~ p]`,
  GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN DISCH_TAC THEN
  MATCH_MP_TAC COMPLETENESS_THEOREM_NUM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "itf" THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [ASM_MESON_TAC[ITF]; ALL_TAC] THEN
  MATCH_MP_TAC (MESON [] `P /\ (P ==> Q) ==> P /\ Q`) THEN
  CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HOLDS_BOX_EQ] THEN
   ONCE_REWRITE_TAC[holds] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  DISCH_TAC THEN
  CONJ_TAC THENL [POP_ASSUM MP_TAC THEN MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[holds] THEN ASM_MESON_TAC[ITF]);;

(* ------------------------------------------------------------------------- *)
(* The work horse of the tactic.                                             *)
(* ------------------------------------------------------------------------- *)

module Rule_gl = struct

  (* Non-recursive building block tactics. *)

  let GEN_BOX_RIGHT_TAC (kacc:thm_tactic) (kholds:thm_tactic): tactic =
    let ptac =
      CONJ_TAC THENL
      [FIRST_ASSUM MATCH_ACCEPT_TAC;
       GEN_TAC THEN
       DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
                                   (CONJUNCTS_THEN2 kacc kholds))] in
    let ttac th = (MATCH_MP_TAC th THEN ptac) in
    USE_THEN "boxr1" ttac ORELSE USE_THEN "boxr2" ttac

  (* Non-recursive building box theorem-tacticals. *)

  let ACC_TCL:thm_tactical = fun k acc ->
    USE_THEN "trans" (fun trans ->
      let f = MATCH_MP (MATCH_MP trans acc) in
      ASSUM_LIST (MAP_EVERY k o mapfilter f))

  (* Recursive theorem-tacticals. *)

  let rec SATURATE_ACC_TCL:thm_tactical = fun ttac th ->
    LABEL_TAC "acc" th THEN
    STEP_BOXL1_TCL ttac th THEN
    ACC_TCL (SATURATE_ACC_TCL ttac) th

  let SATURATE_ACC_TAC:thm_tactic = fun th g ->
    (STEP_BOXL1_TCL HOLDS_TAC th THEN
    SATURATE_ACC_TCL HOLDS_TAC th)
    g

  let BOX_RIGHT_TAC = GEN_BOX_RIGHT_TAC SATURATE_ACC_TAC HOLDS_TAC

  (* Main tactic. *)

  let GL_RIGHT_TAC : tactic =
    CONV_TAC HOLDS_NNFC_UNFOLD_CONV THEN
    PURE_ASM_REWRITE_TAC[AND_CLAUSES; OR_CLAUSES; NOT_CLAUSES] THEN
    CONV_TAC CNF_CONV THEN
    REPEAT CONJ_TAC THEN
    TRY (NEG_RIGHT_TAC HOLDS_TAC)

  let GL_STEP_TAC : tactic =
    (FIRST o map CHANGED_TAC)
      [GL_RIGHT_TAC;
       SORT_BOX_TAC THEN BOX_RIGHT_TAC]

  let INNER_GL_TAC : tactic = REPEAT GL_STEP_TAC

end;;

(* ------------------------------------------------------------------------- *)
(* Generate a countermodel.                                                  *)
(* ------------------------------------------------------------------------- *)

let the_gl_countermodel : term ref = ref `F`;;

let GL_BUILD_COUNTERMODEL : tactic =
  let drop_labels =
    ["trans"; "boxr1"; "boxr2"; "boxl1"; "boxl2"] in
  let drop_assumption s = mem s drop_labels in
  let filter_asl =
    mapfilter (fun s,t -> if drop_assumption s then fail() else concl t ) in
  fun asl,w ->
    let l = filter_asl asl in
    the_gl_countermodel :=
      end_itlist (curry mk_conj) (l @ map mk_neg (striplist dest_disj w));
    failwith
      "Contermodel stored in reference the_gl_countermodel.";;

(* ------------------------------------------------------------------------- *)
(* Top-level invocation.                                                     *)
(* ------------------------------------------------------------------------- *)

let GL_TAC : tactic =
  REPEAT GEN_TAC THEN REPEAT (CONV_TAC let_CONV) THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[diam_DEF; dotbox_DEF] THEN MATCH_MP_TAC COMPLETENESS_NUM THEN
  REPEAT GEN_TAC THEN INTRO_TAC "trans boxr1 boxr2 boxl1 boxl2 w" THEN
  REPEAT GEN_TAC THEN Rule_gl.INNER_GL_TAC THEN GL_BUILD_COUNTERMODEL;;

let GL_RULE (tm:term) : thm =
  prove(tm,GL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some arithmetical principles investigated via provability in GL           *)
(*                                                                           *)
(* Modal formulas can be realised as sentences (i.e. closed formulas) of     *)
(* Peano Arithmetic (PA). The Box is thus interpreted as the predicate of    *)
(* formal provability in PA, Bew(x).                                         *)
(*                                                                           *)
(* Under this interpretation, we will read modal formulas as follows:        *)
(* - Box p = p is provable in PA;                                            *)
(* - Not (Box (Not p)) = p is consistent with PA                             *)
(* - Not (Box p) = p is unprovable in PA                                     *)
(* - Box (Not p) = p is refutable in PA                                      *)
(* - (Box p) || (Box (Not p)) = p is decidable in PA                         *)
(* - Not (Box p) && Not (Box (Not p)) = p is undecidable in PA               *)
(* - Box (p <-> q) = p and q are equivalent over PA                          *)
(* - Box (False) = PA is inconsistent                                        *)
(* - Not (Box False) = Diam True = PA is consistent                          *)
(* ------------------------------------------------------------------------- *)

(*---------------------------------------------------------------------------*)
(* Formalised Second Incompleteness Theorem:                                 *)
(* In PA, the following is provable: If PA is consistent, it cannot prove    *)
(* its own consistency                                                       *)
(*---------------------------------------------------------------------------*)

let GL_second_incompleteness_theorem = time GL_RULE
  `[GL_AX . {} |~ Not (Box False) --> Not (Box (Diam True))]`;;

(*---------------------------------------------------------------------------*)
(* PA ignores unprovability statements                                       *)
(*---------------------------------------------------------------------------*)

let GL_PA_ignorance = time GL_RULE
  `!p. [GL_AX . {} |~ (Box False) <-> Box (Diam p)]`;;

(* ------------------------------------------------------------------------- *)
(* If PA does not prove its inconsistency, then its consistency is           *)
(*   undecidable.                                                            *)
(* ------------------------------------------------------------------------- *)

let GL_PA_undecidability_of_consistency = time GL_RULE
  `[GL_AX . {} |~ Not (Box (Box False))
                  --> Not (Box (Not (Box False))) &&
                      Not (Box (Not (Not (Box False))))]`;;

(* ------------------------------------------------------------------------- *)
(* If a sentence is equivalent to its own unprovability, and if PA does not  *)
(* prove its inconsistency, then that sentence is undecidable.               *)
(* ------------------------------------------------------------------------- *)

let GL_undecidability_of_Godels_formula = time GL_RULE
  `!p. [GL_AX . {} |~ Box (p <-> Not (Box p)) && Not (Box (Box False))
                      --> Not (Box p) && Not (Box (Not p))]`;;

(* ------------------------------------------------------------------------- *)
(* If a reflection principle implies the second iterated consistency         *)
(*   assertion, then the converse implication holds too.                     *)
(* ------------------------------------------------------------------------- *)

let GL_reflection_and_iterated_consistency = time GL_RULE
  `!p. [GL_AX . {} |~ Box ((Box p --> p) --> Diam (Diam True))
                      --> (Diam (Diam True) --> (Box p --> p))]`;;

(* ------------------------------------------------------------------------- *)
(* A Godel sentence is equiconsistent with a consistency statement           *)
(* ------------------------------------------------------------------------- *)

let GL_Godel_sentence_equiconsistent_consistency = time GL_RULE
  `!p. [GL_AX . {} |~ Box (p <-> Not (Box p)) <->
                      Box (p <-> Not (Box False))]`;;

(* ------------------------------------------------------------------------- *)
(* For any arithmetical senteces p q, p is equivalent to unprovability       *)
(* of q --> p iff p is equivalent to consistency of q                        *)
(* ------------------------------------------------------------------------- *)

let GL_arithmetical_fixpoint = time GL_RULE
  `!p q. [GL_AX . {} |~ Dotbox (p <-> Not (Box (q --> p))) <->
                        Dotbox (p <-> Diam q)]`;;

(* ------------------------------------------------------------------------- *)
(* Valid in GL but not in K.                                                 *)
(* ------------------------------------------------------------------------- *)

time GL_RULE
`!a. [GL_AX . {} |~ Box(Diam(Box(Diam(a)))) <-> Box(Diam(a))]`;;
