(* ========================================================================= *)
(* Decision procedure for the modal logic S5.                                *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

needs "HOLMS/s5_completeness.ml";;
needs "HOLMS/gen_countermodel.ml";;

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

let IN_REF_CLAUSES = prove
 (`!W:W->bool R.
     (W,R) IN REF
     ==> (!x. x IN W ==> R x x) /\
         (!x y z. R x y ==> R x z ==> R y z /\ R z y) /\
         (!w w'. R w w'
                 ==> !p. holds (W,R) V (Box p) w ==> holds (W,R) V p w') /\
         (!w p. holds (W,R) V (Box p) w
                 ==> !w'. R w w' ==> holds (W,R) V p w')`,
  REWRITE_TAC[IN_REF; IN_FINITE_FRAME; REFLEXIVE; EUCLIDEAN] THEN
  MESON_TAC[HOLDS_LEFT_BOX]);;

let S5_COMPLETENESS_NUM =
 let S5_COMPLETENESS_THEOREM_NUM =
   REWRITE_RULE[num_INFINITE]
     (INST_TYPE [`:num`,`:A`] S5_COMPLETENESS_THM_GEN) in
 prove
 (`!p. (!W:num->bool R.
          (W,R) IN REF
          ==> !V w. w IN W /\ R w w ==> holds (W,R) V p w)
       ==> [S5_AX . {} |~ p]`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC S5_COMPLETENESS_THEOREM_NUM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in] THEN
  INTRO_TAC "![W] [R]; rf" THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[IN_REF_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Top-level invocation.                                                     *)
(* ------------------------------------------------------------------------- *)

let IN_REF_RULES =
  let tm = `(W:num->bool,R) IN REF` in
  let th = MATCH_MP IN_REF_CLAUSES (ASSUME tm) in
  CONJUNCTS th;;

let S5_TAC : tactic =
  GEN_HOLMS_TAC MATCH_BOX_RIGHT_TAC S5_COMPLETENESS_NUM IN_REF_RULES;;

holms_register_tactic `S5_AX` S5_TAC;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
let mustfail f x =
  if try ignore(f x); false
     with Failure _ -> true
  then report "mustfail: OK"
  else failwith "mustfail: Does not fail.";;

let PREPARE_TAC = HOLMS_PREPARE_TAC S5_COMPLETENESS_NUM;;
let SATURATE_TAC = HOLMS_SATURATE_TAC IN_REF_RULES;;
let STEP_TAC = HOLMS_STEP_TAC SATURATE_TAC;;
let INNER_TAC = INNER_HOLMS_TAC SATURATE_TAC;;
let box_right_tac = BOX_RIGHT_THEN SATURATE_TAC;;
let right_tac = HOLMS_RIGHT_TAC SATURATE_TAC;;

g `!a. [S5_AX . {} |~ Diam a --> Box Diam a]`;;
e (REWRITE_TAC[diam_DEF] THEN PREPARE_TAC);;
e (CHECK_NUM_WORLD_TAC 4);;
e (STEP_TAC 4);;
e (CHANGED_TAC SORT_BOX_TAC);;
e (STEP_TAC 4);;
e (box_right_tac 4);;
e (BOX_RIGHT_THEN MP_TAC 4);;
e (MATCH_MP_TAC HOLDS_RIGHT_BOX_ALT_NUM);;
*)

g `!a. [S5_AX . {} |~ Box a --> Box Box a]`;;
e S5_TAC;;
top_thm();;

(* ------------------------------------------------------------------------- *)
(* Testing HOLMS_RULE on axioms.                                             *)
(* ------------------------------------------------------------------------- *)

(* 0.07276 *)
time HOLMS_RULE `!a. [S5_AX . {} |~ Diam a --> Box Diam a]`;;
(* 0.006639 *)
time HOLMS_RULE `!a. [S5_AX . {} |~ Box a --> a]`;;

(* ------------------------------------------------------------------------- *)
(* Countermodels.                                                            *)
(* ------------------------------------------------------------------------- *)

let S5_HOLMS_CERTIFY_COUNTERMODEL : term -> term -> thm =
  let ltm = `REF:(num->bool)#(num->num->bool)->bool` in
  fun ctm tm ->
    let fm = rand (snd (strip_forall tm))
    and eth = mk_countermodel_existence_thm ctm in
    prove (mk_not_valid_ptm ltm fm,
           CERTIFY_COUNTERMODEL_TAC eth);;

(* ------------------------------------------------------------------------- *)
(* Non-axiom examples.                                                       *)
(* ------------------------------------------------------------------------- *)

(* T_AX 0.006801 *)
time HOLMS_RULE `!a. [S5_AX . {} |~ Box a --> a]`;;

(* K4_AX 0.052886 *)
time HOLMS_RULE `!a. [S5_AX . {} |~ Box a --> Box Box a]`;;

(* B_AX 0.03246 *)
time HOLMS_RULE `!a. [S5_AX . {} |~ a --> Box Diam a]`;;

(* S5_AX 0.069377 *)
time HOLMS_RULE `!a. [S5_AX . {} |~ Diam a --> Box Diam a]`;;

(* GL_AX *)
(* let tm = `!a. [S5_AX . {} |~ Box (Box a --> a) --> Box a]`;; *)

(* ------------------------------------------------------------------------- *)
(* Further examples.                                                         *)
(* ------------------------------------------------------------------------- *)

(* 0.077454 *)
time HOLMS_RULE `[S5_AX . {} |~ Box (a && b) <-> Box a && Box b]`;;

let tm = `!a. [S5_AX . {} |~ a --> Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
S5_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

let tm = `!a. [S5_AX . {} |~ a --> Box Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
S5_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

needs "Library/iter.ml";;

let tm = `!a. [S5_AX . {} |~ a --> ITER 3 (Box) a]`;;
let tm = run_conv (TOP_SWEEP_CONV num_CONV THENC REWRITE_CONV[ITER]) tm;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
time (S5_HOLMS_CERTIFY_COUNTERMODEL ctm) tm;;   (* CPU time (user): 0.841517 *)
