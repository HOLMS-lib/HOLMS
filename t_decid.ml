(* ========================================================================= *)
(* Decision procedure for the modal logic T.                                 *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

needs "HOLMS/t_completeness.ml";;
needs "HOLMS/gen_countermodel.ml";;

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

let IN_RF_CLAUSES = prove
 (`!W:W->bool R.
     (W,R) IN RF
     ==> (!x. x IN W ==> R x x) /\
         (!w w'. R w w'
                 ==> !p. holds (W,R) V (Box p) w ==> holds (W,R) V p w') /\
         (!w p. holds (W,R) V (Box p) w
                 ==> !w'. R w w' ==> holds (W,R) V p w')`,
  REWRITE_TAC[IN_RF; IN_FINITE_FRAME; REFLEXIVE] THEN
  MESON_TAC[HOLDS_LEFT_BOX]);;

let T_COMPLETENESS_NUM =
 let T_COMPLETENESS_THEOREM_NUM =
   REWRITE_RULE[num_INFINITE]
     (INST_TYPE [`:num`,`:A`] T_COMPLETENESS_THM_GEN) in
 prove
 (`!p. (!W:num->bool R.
          (W,R) IN RF
          ==> !V w. w IN W /\ R w w ==> holds (W,R) V p w)
       ==> [T_AX . {} |~ p]`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC T_COMPLETENESS_THEOREM_NUM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in] THEN
  INTRO_TAC "![W] [R]; rf" THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[IN_RF_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Top-level invocation.                                                     *)
(* ------------------------------------------------------------------------- *)

let IN_RF_RULES =
  let tm = `(W:num->bool,R) IN RF` in
  let th = MATCH_MP IN_RF_CLAUSES (ASSUME tm) in
  CONJUNCTS th;;

let T_TAC : tactic =
  GEN_HOLMS_TAC MATCH_BOX_RIGHT_TAC T_COMPLETENESS_NUM IN_RF_RULES;;

holms_register_tactic `T_AX` T_TAC;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
let PREPARE_TAC = HOLMS_PREPARE_TAC T_COMPLETENESS_NUM;;
let SATURATE_TAC = HOLMS_SATURATE_TAC IN_RF_RULES;;
let STEP_TAC = HOLMS_STEP_TAC SATURATE_TAC;;
let INNER_TAC = INNER_HOLMS_TAC SATURATE_TAC;;
let box_right_tac = BOX_RIGHT_THEN SATURATE_TAC;;
let right_tac = HOLMS_RIGHT_TAC SATURATE_TAC;;
*)

g `!a. [T_AX . {} |~ Box a --> a]`;;
(*
e PREPARE_TAC;;
e (STEP_TAC 4);;
*)
e T_TAC;;
top_thm();;

(* ------------------------------------------------------------------------- *)
(* Tests.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Axioms *)
HOLMS_RULE `!a. [T_AX . {} |~ Box a --> a]`;;

(* ------------------------------------------------------------------------- *)
(* Countermodels.                                                            *)
(* ------------------------------------------------------------------------- *)

let T_HOLMS_CERTIFY_COUNTERMODEL : term -> term -> thm =
  let ltm = `RF:(num->bool)#(num->num->bool)->bool` in
  fun ctm tm ->
    let fm = rand (snd (strip_forall tm))
    and eth = mk_countermodel_existence_thm ctm in
    prove (mk_not_valid_ptm ltm fm,
           CERTIFY_COUNTERMODEL_TAC eth);;

(* ------------------------------------------------------------------------- *)
(* Non-axiom examples.                                                       *)
(* ------------------------------------------------------------------------- *)

(* K4_AX *)
let tm = `!a. [T_AX . {} |~ Box a --> Box Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
T_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* B_AX *)
let tm = `!a. [T_AX . {} |~ a --> Box Diam a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
T_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* S5_AX *)
let tm = `!a. [T_AX . {} |~ Diam a --> Box Diam  a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
T_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* GL_AX *)
let tm = `!a. [T_AX . {} |~ Box (Box a --> a) --> Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
T_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* ------------------------------------------------------------------------- *)
(* Furter examples.                                                          *)
(* ------------------------------------------------------------------------- *)

let tm = `!a. [T_AX . {} |~ a --> Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
T_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

let tm = `!a. [T_AX . {} |~ a --> Box Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
T_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

needs "Library/iter.ml";;

let tm = `!a. [T_AX . {} |~ a --> ITER 5 (Box) a]`;;
let tm = run_conv (TOP_SWEEP_CONV num_CONV THENC REWRITE_CONV [ITER]) tm;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
time (T_HOLMS_CERTIFY_COUNTERMODEL ctm) tm;;   (* CPU time (user): 0.810217 *)
