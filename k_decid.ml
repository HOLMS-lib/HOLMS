(* ========================================================================= *)
(* Decision procedure for the provability logic K.                           *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Collect the countermodel from the unfinished proof context.               *)
(* ------------------------------------------------------------------------- *)

(* TODO: Move elsewhere *)
let HOLMS_COLLECT_COUNTERMODEL : tactic =
  fun asl,w ->
    let pos_lits = map (concl o snd) asl
    and neg_lits = map mk_neg (striplist dest_disj w) in
    the_HOLMS_countermodel := end_itlist (curry mk_conj) (pos_lits @ neg_lits);
    failwith "Countermodel stored in reference the_HOLMS_countermodel.";;

(* ------------------------------------------------------------------------- *)
(* Top-level invocation.                                                     *)
(* ------------------------------------------------------------------------- *)

(* TODO: Move elsewhere *)
let TOP_HOLMS_TAC MATCH_BOX_RIGHT_TAC (compl_thm : thm) (rules : thm list) : int -> tactic =
  let PREPARE_TAC = HOLMS_PREPARE_TAC compl_thm
  and SATURATE_TAC = HOLMS_SATURATE_TAC rules in
  let INNER_TAC = INNER_HOLMS_TAC (MATCH_BOX_RIGHT_TAC,SATURATE_TAC) in
  fun (n : int) ->
    PREPARE_TAC THEN INNER_TAC n THEN HOLMS_COLLECT_COUNTERMODEL;;

let GEN_HOLMS_TAC MATCH_BOX_RIGHT_TAC (compl_thm : thm) (rules : thm list) : tactic =
  let TOP_TAC = TOP_HOLMS_TAC MATCH_BOX_RIGHT_TAC compl_thm rules in
  fun (_,w) as gl ->
    let fm = rand (snd (strip_forall w)) in
    let n = count_modal_subformulas fm in
    TOP_TAC (int_pow 2 n) gl;;

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

let IN_FINITE_FRAME_CLAUSES = prove
 (`!W:W->bool R.
     (W,R) IN FINITE_FRAME
     ==> (!w w'. R w w'
                 ==> !p. holds (W,R) V (Box p) w ==> holds (W,R) V p w') /\
         (!w p. holds (W,R) V (Box p) w
                 ==> !w'. R w w' ==> holds (W,R) V p w')`,
  REWRITE_TAC[IN_FINITE_FRAME] THEN MESON_TAC[HOLDS_LEFT_BOX]);;

let K_COMPLETENESS_NUM =
 let K_COMPLETENESS_THEOREM_NUM =
   REWRITE_RULE[num_INFINITE]
     (INST_TYPE [`:num`,`:A`] K_COMPLETENESS_THM_GEN) in
 prove
 (`!p. (!W:num->bool R.
          (W,R) IN FINITE_FRAME
          ==> !V w. w IN W ==> holds (W,R) V p w)
       ==> [{} . {} |~ p]`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC K_COMPLETENESS_THEOREM_NUM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Top-level invocation.                                                     *)
(* ------------------------------------------------------------------------- *)

let K_TAC : tactic =
  let tm = `(W:num->bool,R) IN FINITE_FRAME` in
  let th = MATCH_MP IN_FINITE_FRAME_CLAUSES (ASSUME tm) in
  let rules = CONJUNCTS th in
  GEN_HOLMS_TAC MATCH_BOX_RIGHT_TAC K_COMPLETENESS_NUM rules;;

holms_register_tactic `{}:form->bool` K_TAC;;

(* ------------------------------------------------------------------------- *)
(* Countermodels.                                                            *)
(* ------------------------------------------------------------------------- *)

let K_HOLMS_CERTIFY_COUNTERMODEL : term -> term -> thm =
  let ltm = `FINITE_FRAME:(num->bool)#(num->num->bool)->bool` in
  fun ctm tm ->
    let fm = rand (snd (strip_forall tm))
    and eth = mk_countermodel_existence_thm ctm in
    prove (mk_not_valid_ptm ltm fm,
           CERTIFY_COUNTERMODEL_TAC eth);;

(* ------------------------------------------------------------------------- *)
(* Non-axiom examples.                                                       *)
(* ------------------------------------------------------------------------- *)

(* T_AX *)
let tm = `!a. [{} . {} |~ Box a --> a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
K_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* K4_AX *)
let tm = `!a. [{} . {} |~ Box a --> Box Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
K_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* B_AX *)
let tm = `!a. [{} . {} |~ a --> Box Diam a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
K_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* K_AX *)
let tm = `!a. [{} . {} |~ Diam a --> Box Diam  a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
K_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* GL_AX *)
let tm = `!a. [{} . {} |~ Box (Box a --> a) --> Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
K_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* ------------------------------------------------------------------------- *)
(* Furter examples.                                                          *)
(* ------------------------------------------------------------------------- *)

let tm = `!a. [{} . {} |~ a --> Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
K_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

let tm = `!a. [{} . {} |~ a --> Box Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
K_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

needs "Library/iter.ml";;

let run_conv conv tm = rhs (concl (conv tm));;
let tm = `!a. [{} . {} |~ a --> ITER 8 (Box) a]`;;
let tm = run_conv (TOP_SWEEP_CONV num_CONV THENC REWRITE_CONV [ITER]) tm;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
time (K_HOLMS_CERTIFY_COUNTERMODEL ctm) tm;;   (* CPU time (user): 0.335567 *)
