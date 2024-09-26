(* ========================================================================= *)
(* Decision procedure for the provability logic K.                           *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2024.              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Serve?  Semplificare. *)
let K_COMPLETENESS_NUM =
  let K_COMPLETENESS_THEOREM_NUM =
    REWRITE_RULE[num_INFINITE]
      (INST_TYPE [`:num`,`:A`] K_COMPLETENESS_THM_GEN) in
 prove
 (`!p. (!W R V w:num.
          (!p w. w IN W /\
                 (!y. y IN W /\ R w y ==> holds (W,R) V p y)
                 ==> holds (W,R) V (Box p) w) /\
          (!Q p w. w IN W /\
                   (!y. y IN W /\ R w y ==> holds (W,R) V p y \/ Q)
                   ==> holds (W,R) V (Box p) w \/ Q) /\
          (!w w'. R w w'
                  ==> !p. holds (W,R) V (Box p) w ==> holds (W,R) V p w') /\
          (!p w. holds (W,R) V (Box p) w
                 ==> !w'. R w w' ==> holds (W,R) V p w') /\
          w IN W
          ==> holds (W,R) V p w)
       ==> [{} . {} |~ p]`,
  GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN DISCH_TAC THEN
  MATCH_MP_TAC K_COMPLETENESS_THEOREM_NUM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "itf" THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [REWRITE_TAC[holds] THEN ASM_MESON_TAC[K_FRAME_CAR]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[holds] THEN ASM_MESON_TAC[K_FRAME_CAR]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[holds] THEN ASM_MESON_TAC[K_FRAME_CAR]; ALL_TAC] THEN
  REWRITE_TAC[holds] THEN ASM_MESON_TAC[K_FRAME_CAR]);;

(* ------------------------------------------------------------------------- *)
(* The work horse of the tactic.                                             *)
(* ------------------------------------------------------------------------- *)

(* module Rule_K = struct *)

  (* Non-recursive building block tactics. *)

let GEN_BOX_RIGHT_TAC (kacc:thm_tactic) : tactic =
  let ptac =
    CONJ_TAC THENL
    [FIRST_ASSUM MATCH_ACCEPT_TAC;
     GEN_TAC THEN
     DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC kacc)] in
  let ttac th = (MATCH_MP_TAC th THEN ptac) in
  USE_THEN "boxr1" ttac ORELSE USE_THEN "boxr2" ttac;;

let rec SATURATE_ACC_TCL:thm_tactical = fun ttac th ->
  LABEL_TAC "acc" th THEN STEP_BOXL1_TCL ttac th;;

let SATURATE_ACC_TAC:thm_tactic = fun th g ->
  (STEP_BOXL1_TCL HOLDS_TAC th THEN SATURATE_ACC_TCL HOLDS_TAC th) g;;

  (* Recursive theorem-tacticals. *)

let BOX_RIGHT_TAC = GEN_BOX_RIGHT_TAC SATURATE_ACC_TAC;;

  (* Main tactic. *)

let K_RIGHT_TAC : tactic =
  CONV_TAC HOLDS_NNFC_UNFOLD_CONV THEN
  PURE_ASM_REWRITE_TAC[AND_CLAUSES; OR_CLAUSES; NOT_CLAUSES] THEN
  CONV_TAC CNF_CONV THEN
  REPEAT CONJ_TAC THEN
  TRY (NEG_RIGHT_TAC HOLDS_TAC);;

let K_STEP_TAC : tactic =
  (FIRST o map CHANGED_TAC)
    [K_RIGHT_TAC;
     SORT_BOX_TAC THEN BOX_RIGHT_TAC];;

let INNER_K_TAC : tactic = REPEAT K_STEP_TAC;;

(* end;; *)

(* ------------------------------------------------------------------------- *)
(* Generate a countermodel.                                                  *)
(* ------------------------------------------------------------------------- *)

let the_K_countermodel : term ref = ref `F`;;

let K_BUILD_COUNTERMODEL : tactic =
  let drop_labels =
    ["trans"; "boxr1"; "boxr2"; "boxl1"; "boxl2"] in
  let drop_assumption s = mem s drop_labels in
  let filter_asl =
    mapfilter (fun s,t -> if drop_assumption s then fail() else concl t ) in
  fun asl,w ->
    let l = filter_asl asl in
    the_K_countermodel :=
      end_itlist (curry mk_conj) (l @ map mk_neg (striplist dest_disj w));
    failwith
      "Contermodel stored in reference the_K_countermodel.";;

(* ------------------------------------------------------------------------- *)
(* Top-level invocation.                                                     *)
(* ------------------------------------------------------------------------- *)

let K_TAC : tactic =
  REPEAT GEN_TAC THEN REPEAT (CONV_TAC let_CONV) THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[diam_DEF; dotbox_DEF] THEN MATCH_MP_TAC K_COMPLETENESS_NUM THEN
  REPEAT GEN_TAC THEN INTRO_TAC "boxr1 boxr2 boxl1 boxl2 w" THEN
  REPEAT GEN_TAC THEN
  (* Rule_gl.INNER_K_TAC THEN *)
  INNER_K_TAC THEN
  K_BUILD_COUNTERMODEL;;

let K_RULE (tm:term) : thm =
  prove(tm,K_TAC);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

K_RULE `!a b. [{} . {} |~ Box (a && b) <-> Box a && Box b]`;;

K_RULE `!a b. [{} . {} |~ Box a || Box b --> Box (a || b)]`;;

g `!a. [{} . {} |~ Box a --> a]`;;
e (TRY K_TAC);;
!the_K_countermodel;;

g `!a b. [{} . {} |~ Box (a || b) --> Box a || Box b]`;;
e (TRY K_TAC);;
!the_K_countermodel;;