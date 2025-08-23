(* ========================================================================= *)
(* Tools for the generation of certified countermodels.                      *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Miscellanea.                                                              *)
(* ------------------------------------------------------------------------- *)

let IMP_DISJ = MESON[] `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;;

(* ------------------------------------------------------------------------- *)
(* Refined version of membership lemmas for frames.                          *)
(* ------------------------------------------------------------------------- *)

(* K *)
(* Just IN_FINITE_FRAME *)

(* T *)
let IN_RF_ALT = prove
 (`!W:A->bool R.
     (W,R) IN RF <=>
     ~(W = {}) /\
     (!x y. R x y ==> x IN W /\ y IN W) /\
     FINITE W /\
     (!x. x IN W ==> R x x)`,
  MESON_TAC[RF_DEF; IN_FINITE_FRAME; REFLEXIVE; IN_ELIM_PAIR_THM]);;

(* K4 *)
let IN_TF_ALT = prove
 (`!W:A->bool R.
     (W,R) IN TF <=>
     ~(W = {}) /\
     (!x y. R x y ==> x IN W /\ y IN W) /\
     FINITE W /\
     (!x y z. R x y /\ R y z ==> R x z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_TF_DEF; IN_FINITE_FRAME; TRANSITIVE] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* S4 *)
let IN_RTF_ALT = prove
 (`!W:A->bool R.
     (W,R) IN RTF <=>
     ~(W = {}) /\
     (!x y. R x y ==> x IN W /\ y IN W) /\
     FINITE W /\
     (!x. x IN W ==> R x x) /\
     (!x y z. R x y /\ R y z ==> R x z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_RTF_DEF; IN_FINITE_FRAME; REFLEXIVE; TRANSITIVE] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* B *)
let IN_RSF_ALT = prove
 (`!W:A->bool R. (W,R) IN RSF <=>
     ~(W = {}) /\
     (!x y. R x y ==> x IN W /\ y IN W) /\
     FINITE W /\
     (!x. x IN W ==> R x x) /\
     (!x y. R x y ==> R y x )`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_RSF_DEF; IN_FINITE_FRAME; REFLEXIVE; SYMETRIC] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* S5 *)
let IN_REF_ALT = prove
 (`(W:W->bool,R:W->W->bool) IN REF <=>
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W /\
   (!x. x IN W ==> R x x) /\
   (!x y z:W. R x y /\ R x z ==> R z y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_REF_DEF; IN_FINITE_FRAME; REFLEXIVE; EUCLIDEAN] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* GL *)
let IN_ITF_ALT = prove
 (`!W:A->bool R.
     (W,R) IN ITF <=>
     ~(W = {}) /\
     (!x y. R x y ==> x IN W /\ y IN W) /\
     FINITE W /\
     (!x. ~R x x) /\
     (!x y z. R x y /\ R y z ==> R x z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_ITF_DEF; IN_FINITE_FRAME; IRREFLEXIVE; TRANSITIVE] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Auxiliary OCaml procedures.                                               *)
(* ------------------------------------------------------------------------- *)

let dest_acc_atom = dest_binop `R:num->num->bool`;;
let is_acc_atom = is_binop `R:num->num->bool`;;

(* ------------------------------------------------------------------------- *)
(* Compare two terms and return a pair of subterms that differs.  More       *)
(* precisely, given two terms, it fails if they are equal and return the     *)
(* outermost, rightmost pair of subterms that differ otherwise.              *)
(* ------------------------------------------------------------------------- *)

(* Not used. *)
let rec compare_terms tm1 tm2 : term * term =
  if tm1 = tm2 then failwith "compare_terms: equal terms" else
  match tm1,tm2 with
  | Comb(f1,x1),Comb(f2,x2) ->
      (try compare_terms x1 x2 with Failure _ -> compare_terms f1 f2)
  | Abs(v1,b1),Abs(v2,b2) ->
      (try compare_terms v1 v2 with Failure _ -> compare_terms b1 b2)
  | _,_ -> tm1,tm2;;

(* ------------------------------------------------------------------------- *)
(* Scan a term to find accessibility atoms in a term of the form `R x y`,    *)
(* where `x` e `y` are of type `:num`.                                       *)
(* ------------------------------------------------------------------------- *)

(* Not used. *)
let find_acc_atoms =
  let rec find_acc_atoms acc l =
    match l with
    | [] -> setify acc
    | tm :: l ->
        if is_acc_atom tm then
          find_acc_atoms (tm :: acc) l
        else if is_comb tm then
          find_acc_atoms acc (rator tm :: rand tm :: l)
        else if is_var tm || is_const tm then
          find_acc_atoms acc l
        else
          failwith "find_acc_atoms" in
  fun tm -> find_acc_atoms [] [tm];;

(* Example: *)
(*
let tml = find_acc_atoms !the_HOLMS_countermodel;;
*)

(* ------------------------------------------------------------------------- *)
(* Refined version of the HOLDS_LEMMA.                                       *)
(* ------------------------------------------------------------------------- *)

let HOLDS_ACCREL_WD_LEMMA = prove
 (`!W:A->bool R.
     (!x y. R x y ==> x IN W /\ y IN W)
     ==> (!V w. ~holds (W,R) V False w) /\
         (!V w. holds (W,R) V True w) /\
         (!V s w. holds (W,R) V (Atom s) w <=> V s w) /\
         (!V p w. holds (W,R) V (Not p) w <=> ~holds (W,R) V p w) /\
         (!p V q w. holds (W,R) V (p && q) w <=>
                    holds (W,R) V p w /\ holds (W,R) V q w) /\
         (!p V q w. holds (W,R) V (p || q) w <=>
                    holds (W,R) V p w \/ holds (W,R) V q w) /\
         (!p V q w. holds (W,R) V (p --> q) w <=>
                    holds (W,R) V p w ==> holds (W,R) V q w) /\
         (!p V q w. holds (W,R) V (p <-> q) w <=>
                    (holds (W,R) V p w <=> holds (W,R) V q w)) /\
         (!w V p. holds (W,R) V (Box p) w <=>
                  (!w'. R w w' ==> holds (W,R) V p w'))`,
  REWRITE_TAC[holds] THEN MESON_TAC[holds]);;

(* Resolve existentials of metavariables with atomic formulas.  *)

let EXISTS_ATOM_TAC : tactic =
  let num_ty = `:num` in
  let mk_modal_atom : string -> term =
    let atom_tm = `Atom` in
    fun s -> mk_comb(atom_tm,mk_string s) in
  fun _,w as gl ->
    try let vtm,_ = dest_exists w in
        let s,ty = dest_var vtm in
        if ty = num_ty then fail() else
        EXISTS_TAC (mk_modal_atom s) gl
    with Failure _ -> failwith "EXISTS_ATOM_TAC";;

(* ------------------------------------------------------------------------- *)
(* OCaml representation of the genererated countermodel.                     *)
(* ------------------------------------------------------------------------- *)

(* Metavariables occurring in the modal formula. *)
let get_modal_metavars : term -> term list =
  let form_ty = `:form` in
  filter ((=) form_ty o type_of) o frees;;

(* Instantiation of the metavariables occurring in a formula. *)
let mk_metavar_ilist : term -> (term * term) list =
  let atom_tm = `Atom` in
  let mk_atom = curry mk_comb atom_tm o mk_string o name_of in
  let mk_subst tm = mk_atom tm,tm in
  map mk_subst o get_modal_metavars;;

(* ------------------------------------------------------------------------- *)
(* Build a representation of the model.                                      *)
(* ------------------------------------------------------------------------- *)

let mk_worlds_numseg : int -> term =
  let mk_numseg = mk_binop `(..)`
  and one_tm = `1` in
  fun n -> mk_numseg one_tm (mk_small_numeral n);;

let mk_worlds_def : int -> term =
  let rtm = `W:num->bool` in
  fun n -> mk_eq(rtm, mk_worlds_numseg n);;

(* ------------------------------------------------------------------------- *)
(* Analizes the worlds occurring in the countermodel.
   Returns a triple (n:int, ilist:(term * term) list) where:
   - n is the number of worlds
   - ilist is an instantiation list [`1`,`w`; ...]                           *)
(* ------------------------------------------------------------------------- *)

let get_worlds : term -> int * (term * term) list =
  let num_ty = `:num` in
  fun ctm ->
    let worlds = filter ((=) num_ty o type_of) (frees ctm) in
    let num_worlds = length worlds in
    let nworlds = map mk_small_numeral (1--num_worlds) in
    let world_ilist = zip nworlds worlds in
    num_worlds, world_ilist;;

(* ------------------------------------------------------------------------- *)
(* Extract atoms from the countermodel.                                      *)
(* ------------------------------------------------------------------------- *)

(* Extract evaluation atoms. *)
let get_eval_atoms : term list -> term list =
  let dest_eval_atom =
    let pth = prove
     (`(holds (W:num->bool,R) V (Atom s) w <=> V s w = T) /\
       (~holds (W:num->bool,R) V (Atom s) w <=> V s w = F)`,
      REWRITE_TAC[holds]) in
    rhs o concl o GEN_REWRITE_CONV I [pth] in
  mapfilter dest_eval_atom;;

(* Define the accessibility relation. *)
let MK_ACC_EXISTS_THM =
  let TRIVIAL_ACCREL_EXISTS = prove(`?R:num->num->bool.
      (!x y. R x y = F) /\
      (!S. T ==> (!x y. R x y ==> S x y)) /\
      (!x y. R x y = F)`,
    EXISTS_TAC `\x:num y:num. F` THEN REWRITE_TAC[]) in
  let mk_acc_rules : (term * term) list -> term =
    let rtm = `R:num->num->bool` in
    fun acc_pairs ->
      end_itlist (curry mk_conj)
                 (map (uncurry (mk_binop rtm)) acc_pairs) in
  fun acc_pairs ->
    match try Some (mk_acc_rules acc_pairs) with Failure _ -> None with
    | None -> TRIVIAL_ACCREL_EXISTS
    | Some acc_rules -> prove_inductive_relations_exist acc_rules;;

(* Define the evaluation function *)
let MK_EVAL_EXISTS_THM : term list -> thm =
  let vtm = `V:string->num->bool` in
  fun eval_atoms ->
    if eval_atoms = [] then TRUTH else
    let eval_clauses =
      end_itlist (curry mk_conj) eval_atoms in
    let eval_descr = mk_exists(vtm,eval_clauses) in
    prove_general_recursive_function_exists eval_descr;;

let MK_WORLDSET_EXISTS_THM (worlds_def : term) : thm =
  let ltm,rtm = dest_eq worlds_def in
  let patt = mk_exists(ltm,mk_eq(rtm,ltm)) in
  EXISTS (patt,rtm) (REFL rtm);;

(* MK_WORLDSET_EXISTS_THM `W = {1}`;; *)

let mk_countermodel_existence_thm : term -> thm =
  let pth = MESON [] `(?x:A. P x) /\ (?y:B. Q y) <=> ?x y. P x /\ Q y` in
  fun ctm ->
  (* Define the universe of worlds. *)
  let num_worlds, world_ilist = get_worlds ctm in
  let WORLDSET_EXISTS_THM =
    MK_WORLDSET_EXISTS_THM (mk_worlds_def num_worlds) in
  (* List of atoms in the countermodel. *)
  let ctml =
    let ctm' = vsubst (mk_metavar_ilist ctm @ world_ilist) ctm in
    striplist dest_conj ctm' in
  (* Define the accessibility relation. *)
  let ACC_EXISTS_THM =
    (* Extract accessibility pairs. *)
    let acc_pairs = mapfilter dest_acc_atom ctml in
    MK_ACC_EXISTS_THM acc_pairs
  (* Define evaluation function. *)
  and EVAL_EXISTS_THM =
    let eval_atoms = get_eval_atoms ctml in
    MK_EVAL_EXISTS_THM eval_atoms
  in
  let th = end_itlist CONJ
    [WORLDSET_EXISTS_THM; ACC_EXISTS_THM; EVAL_EXISTS_THM] in
  PURE_REWRITE_RULE [pth; RIGHT_AND_EXISTS_THM] th;;

(* ------------------------------------------------------------------------- *)
(* The main tactic.                                                          *)
(* ------------------------------------------------------------------------- *)

let dest_exists_countermodel_thm eth =
  let _,btm = strip_exists (concl eth) in
  let w,btm' = dest_conj btm in
  let r,v = dest_conj btm' in
  let r_rules,r' = dest_conj r in
  let r_induct,r_cases = dest_conj r' in
  (w,(r_rules,r_induct,r_cases),v);;

let MK_WORLDS_FINITE_THM : thm -> thm =
  let gl_tm = `FINITE (W:num->bool)` in
  let tac =
    DISCH_THEN (LABEL_TAC "W") THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[FINITE_NUMSEG] in
  fun eth ->
    let w,_,_ = dest_exists_countermodel_thm eth in
    let gl = mk_imp(w,gl_tm) in
    UNDISCH_ALL (prove (gl, tac));;

let MK_WORLDS_NOT_EMPTY_THM : thm -> thm =
  let gl_tm = `~(W:num->bool = {})` in
  let tac =
    DISCH_THEN (LABEL_TAC "W") THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[NUMSEG_EMPTY] THEN NUM_REDUCE_TAC in
  fun eth ->
    let w,_,_ = dest_exists_countermodel_thm eth in
    let gl = mk_imp(w,gl_tm) in
    UNDISCH_ALL (prove (gl, tac));;

(* let MK_WORLDS_FINITE_NOT_EMPTY_THM (eth : thm) : thm =
  CONJ (MK_WORLDS_FINITE_THM eth)
       (MK_WORLDS_NOT_EMPTY_THM eth);; *)

let MK_ACCREL_WD_THM : thm -> thm =
  let wd_term = `!x y:num. R x y ==> x IN W /\ y IN W` in
  let tac =
    DISCH_THEN (LABEL_TAC "R_induct") THEN
    DISCH_THEN (LABEL_TAC "W") THEN
    REMOVE_THEN "R_induct" MATCH_MP_TAC THEN
    EXPAND_TAC "W" THEN REWRITE_TAC[IN_NUMSEG] THEN NUM_REDUCE_TAC in
  fun eth ->
    let w,(_,r_induct,_),_ = dest_exists_countermodel_thm eth in
    let gl = mk_imp(r_induct,mk_imp(w,wd_term)) in
    UNDISCH_ALL (prove (gl, tac));;

let MK_ACCREL_REFL_THM : thm -> thm =
  let gl_tm = `!x:num. x IN W ==> R x x` in
  let tac =
    MAP_EVERY (DISCH_THEN o LABEL_TAC) ["w"; "r_rules"] THEN
    HYP_TAC "w" (CONV_RULE (LAND_CONV NUMSEG_CONV)) THEN
    EXPAND_TAC "W" THEN REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    USE_THEN "r_rules" (fun th -> REWRITE_TAC[th]) in
  fun eth ->
    let w,(r_rules,_,r_cases),_ = dest_exists_countermodel_thm eth in
    let gl = itlist (curry mk_imp) [w; r_rules] gl_tm in
    UNDISCH_ALL (prove (gl, tac));;

let MK_ACCREL_IRREFL_THM : thm -> thm =
  let pth = MESON [] `(!x y:num. R x y ==> ~(x = y)) ==> (!x:num. ~R x x)` in
  let PREPARE_IND_TAC = MATCH_MP_TAC pth in
  let gl_tm = `!x:num. ~R x x` in
  let tac =
    DISCH_THEN (LABEL_TAC "r_induct") THEN PREPARE_IND_TAC THEN
    USE_THEN "r_induct" MATCH_MP_TAC THEN NUM_REDUCE_TAC in
  fun eth ->
    let _,(_,r_induct,_),_ = dest_exists_countermodel_thm eth in
    let gl = mk_imp(r_induct,gl_tm) in
    UNDISCH (prove (gl, tac));;

let MK_ACCREL_TRANS_THM : thm -> thm =
  let gl_tm = `!x y z:num. R x y /\ R y z ==> R x z` in
  let tac =
    DISCH_THEN (LABEL_TAC "R_induct") THEN
    DISCH_THEN (LABEL_TAC "R_cases") THEN
    DISCH_THEN (LABEL_TAC "R_rules") THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REMOVE_THEN "R_induct" MATCH_MP_TAC THEN
    USE_THEN "R_cases" (fun th ->
      CONV_TAC (ONCE_DEPTH_CONV (BINDER_CONV
        (GEN_REWRITE_CONV LAND_CONV [th] THENC NUM_REDUCE_CONV)))) THEN
    USE_THEN "R_rules" (fun th ->
      REWRITE_TAC[th; IMP_DISJ; FORALL_AND_THM; FORALL_UNWIND_THM2]) in
  fun eth ->
    let _,(r_rules,r_induct,r_cases),_ = dest_exists_countermodel_thm eth in
    let gl = mk_imp(r_induct,mk_imp(r_cases,mk_imp(r_rules,gl_tm))) in
    UNDISCH_ALL (prove (gl, tac));;

let MK_ACCREL_EUCLID_THM : thm -> thm =
  let gl_tm = `!x y z:num. R x y /\ R x z ==> R z y` in
  let tac =
    DISCH_THEN (LABEL_TAC "R_induct") THEN
    DISCH_THEN (LABEL_TAC "R_cases") THEN
    DISCH_THEN (LABEL_TAC "R_rules") THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REMOVE_THEN "R_induct" MATCH_MP_TAC THEN
    USE_THEN "R_cases" (fun th ->
      CONV_TAC (ONCE_DEPTH_CONV (BINDER_CONV
        (GEN_REWRITE_CONV LAND_CONV [th] THENC NUM_REDUCE_CONV)))) THEN
    USE_THEN "R_rules" (fun th ->
      REWRITE_TAC[th; IMP_DISJ; FORALL_AND_THM; FORALL_UNWIND_THM2]) in
  fun eth ->
    let _,(r_rules,r_induct,r_cases),_ = dest_exists_countermodel_thm eth in
    let gl = mk_imp(r_induct,mk_imp(r_cases,mk_imp(r_rules,gl_tm))) in
    UNDISCH_ALL (prove (gl, tac));;

let MK_ACCREL_SYM_THM : thm -> thm =
  let gl_tm = `!x y:num. R x y ==> R y x` in
  let tac =
    DISCH_THEN (LABEL_TAC "R_induct") THEN
    DISCH_THEN (LABEL_TAC "R_rules") THEN
    REMOVE_THEN "R_induct" MATCH_MP_TAC THEN
    USE_THEN "R_rules" (fun th -> REWRITE_TAC[th]) in
  fun eth ->
    let _,(r_rules,r_induct,_),_ = dest_exists_countermodel_thm eth in
    let gl = mk_imp(r_induct,mk_imp(r_rules,gl_tm)) in
    UNDISCH_ALL (prove (gl, tac));;

(* K *)
let MK_IN_FINITE_FRAME : thm -> thm =
  let rule = CONV_RULE (REWR_CONV (GSYM IN_FINITE_FRAME)) in
  fun eth ->
    rule (end_itlist CONJ
                     [MK_WORLDS_NOT_EMPTY_THM eth;
                      MK_ACCREL_WD_THM eth;
                      MK_WORLDS_FINITE_THM eth]);;

(* T *)
let MK_IN_RF : thm -> thm =
  let rule = CONV_RULE (REWR_CONV (GSYM IN_RF_ALT)) in
  fun eth ->
    rule (end_itlist CONJ
                     [MK_WORLDS_NOT_EMPTY_THM eth;
                      MK_ACCREL_WD_THM eth;
                      MK_WORLDS_FINITE_THM eth;
                      MK_ACCREL_REFL_THM eth]);;

(* K4 *)
let MK_IN_TF_THM : thm -> thm =
  let rule = CONV_RULE (REWR_CONV (GSYM IN_TF_ALT)) in
  fun eth ->
    rule (end_itlist CONJ
                     [MK_WORLDS_NOT_EMPTY_THM eth;
                      MK_ACCREL_WD_THM eth;
                      MK_WORLDS_FINITE_THM eth;
                      MK_ACCREL_TRANS_THM eth]);;

(* S4 *)
let MK_IN_RTF_THM : thm -> thm =
  let rule = CONV_RULE (REWR_CONV (GSYM IN_RTF_ALT)) in
  fun eth ->
    rule (end_itlist CONJ
                     [MK_WORLDS_NOT_EMPTY_THM eth;
                      MK_ACCREL_WD_THM eth;
                      MK_WORLDS_FINITE_THM eth;
                      MK_ACCREL_REFL_THM eth;
                      MK_ACCREL_TRANS_THM eth]);;

(* B *)
let MK_IN_RSF_THM : thm -> thm =
  let rule = CONV_RULE (REWR_CONV (GSYM IN_RSF_ALT)) in
  fun eth ->
    rule (end_itlist CONJ
                     [MK_WORLDS_NOT_EMPTY_THM eth;
                      MK_ACCREL_WD_THM eth;
                      MK_WORLDS_FINITE_THM eth;
                      MK_ACCREL_REFL_THM eth;
                      MK_ACCREL_SYM_THM eth]);;

(* S5 *)
let MK_IN_REF_THM : thm -> thm =
  let rule = CONV_RULE (REWR_CONV (GSYM IN_REF_ALT)) in
  fun eth ->
    rule (end_itlist CONJ
                     [MK_WORLDS_NOT_EMPTY_THM eth;
                      MK_ACCREL_WD_THM eth;
                      MK_WORLDS_FINITE_THM eth;
                      MK_ACCREL_REFL_THM eth;
                      MK_ACCREL_EUCLID_THM eth]);;

(* GL *)
let MK_IN_ITF_THM : thm -> thm =
  let rule = CONV_RULE (REWR_CONV (GSYM IN_ITF_ALT)) in
  fun eth ->
    rule (end_itlist CONJ
                     [MK_WORLDS_NOT_EMPTY_THM eth;
                      MK_ACCREL_WD_THM eth;
                      MK_WORLDS_FINITE_THM eth;
                      MK_ACCREL_IRREFL_THM eth;
                      MK_ACCREL_TRANS_THM eth]);;

(* ------------------------------------------------------------------------- *)
(* Tests and examples.                                                       *)
(* ------------------------------------------------------------------------- *)

let ctm = `holds (W,R) V (Atom "a") w /\
           ~holds (W,R) V (Atom "a") y /\
           w:num IN W /\ y IN W /\ z IN W /\
           R w y /\ R w z`;;
let eth = mk_countermodel_existence_thm ctm;;
MK_WORLDS_NOT_EMPTY_THM eth;;
MK_ACCREL_WD_THM eth;;
MK_WORLDS_FINITE_THM eth;;
MK_ACCREL_IRREFL_THM eth;;

let ctm = `holds (W,R) V (Atom "a") w /\
           ~holds (W,R) V (Atom "a") y /\
           w:num IN W /\ y IN W /\ z IN W /\
           R w y`;;
let eth = mk_countermodel_existence_thm ctm;;
MK_WORLDS_NOT_EMPTY_THM eth;;
MK_ACCREL_WD_THM eth;;
MK_WORLDS_FINITE_THM eth;;
MK_ACCREL_IRREFL_THM eth;;

let ctm = `holds (W,R) V (Atom "a") w /\
           ~holds (W,R) V (Atom "a") y /\
           w:num IN W /\ y IN W /\ z IN W`;;
let eth = mk_countermodel_existence_thm ctm;;
MK_WORLDS_NOT_EMPTY_THM eth;;
MK_ACCREL_WD_THM eth;;
MK_WORLDS_FINITE_THM eth;;
MK_ACCREL_TRANS_THM eth;;
MK_ACCREL_SYM_THM eth;;
MK_ACCREL_IRREFL_THM eth;;
MK_ACCREL_EUCLID_THM eth;;
MK_IN_TF_THM eth;;

let ctm = `holds (W,R) V (Atom "a") w /\
           ~holds (W,R) V (Atom "a") y /\
           w:num IN W /\ y IN W /\ z IN W /\
           R w y /\ R y z /\ R w z`;;
let eth = mk_countermodel_existence_thm ctm;;
MK_WORLDS_NOT_EMPTY_THM eth;;
MK_ACCREL_WD_THM eth;;
MK_WORLDS_FINITE_THM eth;;
MK_ACCREL_TRANS_THM eth;;
MK_ACCREL_IRREFL_THM eth;;
MK_IN_TF_THM eth;;

let ctm = `holds (W,R) V (Atom "a") w /\
           ~holds (W,R) V (Atom "a") y /\
           w:num IN W /\ y IN W /\ z IN W /\
           R w y /\ R y z /\ R w z /\
           R w w /\ R y y /\ R z z`;;
let eth = mk_countermodel_existence_thm ctm;;
MK_WORLDS_NOT_EMPTY_THM eth;;
MK_ACCREL_WD_THM eth;;
MK_WORLDS_FINITE_THM eth;;
MK_ACCREL_TRANS_THM eth;;
MK_IN_TF_THM eth;;
MK_ACCREL_REFL_THM eth;;
MK_IN_RTF_THM eth;;

let ctm = `w:num IN W /\ ~holds (W,R) V (Atom "a") w /\ R w w`;;
let eth = mk_countermodel_existence_thm ctm;;
MK_WORLDS_NOT_EMPTY_THM eth;;
MK_ACCREL_WD_THM eth;;
MK_WORLDS_FINITE_THM eth;;
MK_ACCREL_REFL_THM eth;;
MK_ACCREL_TRANS_THM eth;;
MK_ACCREL_SYM_THM eth;;
MK_IN_TF_THM eth;;
MK_IN_RTF_THM eth;;
MK_IN_RSF_THM eth;;
MK_IN_REF_THM eth;;

let ctm = `w:num IN W /\ y IN W /\
           ~holds (W,R) V (Atom "a") w /\
           R w w /\ R y y /\ R w y /\ R y w`;;
let eth = mk_countermodel_existence_thm ctm;;
MK_WORLDS_NOT_EMPTY_THM eth;;
MK_ACCREL_WD_THM eth;;
MK_WORLDS_FINITE_THM eth;;
MK_ACCREL_REFL_THM eth;;
MK_ACCREL_TRANS_THM eth;;
MK_IN_TF_THM eth;;
MK_IN_RTF_THM eth;;
MK_IN_RSF_THM eth;;
MK_IN_REF_THM eth;;

let in_frames_assoc = ref
  [`FINITE_FRAME:(num->bool)#(num->num->bool)->bool`,
   MK_IN_FINITE_FRAME; (* K *)
   `RF:(num->bool)#(num->num->bool)->bool`, MK_IN_RF;       (* T *)
   `TF:(num->bool)#(num->num->bool)->bool`, MK_IN_TF_THM;   (* K4 *)
   `RTF:(num->bool)#(num->num->bool)->bool`, MK_IN_RTF_THM; (* S4 *)
   `RSF:(num->bool)#(num->num->bool)->bool`, MK_IN_RSF_THM; (* B *)
   `REF:(num->bool)#(num->num->bool)->bool`, MK_IN_REF_THM; (* S5 *)
   `ITF:(num->bool)#(num->num->bool)->bool`, MK_IN_ITF_THM  (* GL *)
  ];;

let MK_IN_FRAMES_TAC : thm -> tactic =
  let dest_in = dest_binary "IN" in
  fun eth (_,w) as gl ->
    let x,s = dest_in w in
    match try Some (assoc s !in_frames_assoc)
          with Failure _ -> None
    with
      None -> failwith "IN_FRAMES_CONV"
    | Some f -> ACCEPT_TAC (f eth) gl;;

let mk_not_valid_ptm : term -> term -> term =
  let valid_ptm = `L:(num->bool)#(num->num->bool)->bool |= fm` in
  let lvar,fmvar = dest_binary "|=" valid_ptm in
  fun ltm fm ->
    let ptm = vsubst [ltm,lvar; fm,fmvar] valid_ptm in
    mk_neg(list_mk_forall(frees ptm, ptm));;

let CERTIFY_COUNTERMODEL_TAC (eth : thm) : tactic =
  REWRITE_TAC[valid; diam_DEF; NOT_FORALL_THM; NOT_IMP; EXISTS_PAIR_THM] THEN
  REPEAT EXISTS_ATOM_TAC THEN
  DESTRUCT_TAC "@W R V. W (acc_rules acc_induct acc_cases) V" eth THEN
  EXISTS_TAC `W:num->bool` THEN
  EXISTS_TAC `R:num->num->bool` THEN
  CLAIM_TAC "acc_wd" `!x y:num. R x y ==> x IN W /\ y IN W` THENL
  [REMOVE_THEN "acc_induct" MATCH_MP_TAC THEN EXPAND_TAC "W" THEN
   REWRITE_TAC[IN_NUMSEG] THEN NUM_REDUCE_TAC;
   ALL_TAC] THEN

  CONJ_TAC THENL [
   (* `W,R IN FRAMES` *)
   MK_IN_FRAMES_TAC eth;
   ALL_TAC] THEN
  (* Evaluaton of the formula. *)
  REWRITE_TAC[holds_in; NOT_FORALL_THM] THEN
  EXISTS_TAC `V:string->num->bool` THEN
  REMOVE_THEN "acc_wd"
    (fun th -> REWRITE_TAC[MATCH_MP HOLDS_ACCREL_WD_LEMMA th]) THEN
  REMOVE_THEN "W" SUBST_VAR_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV NUMSEG_CONV) THEN
  REWRITE_TAC[NOT_IMP; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
  (REPEAT o CHANGED_TAC)
   (USE_THEN "acc_cases" (fun th ->
     CONV_TAC (ONCE_DEPTH_CONV (BINDER_CONV
       (GEN_REWRITE_CONV LAND_CONV [th] THENC NUM_REDUCE_CONV)))) THEN
    HYP REWRITE_TAC "V" [FORALL_UNWIND_THM2; UNWIND_THM2;
      MESON[] `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
      FORALL_AND_THM; IMP_CONJ; RIGHT_OR_DISTRIB; EXISTS_OR_THM]);;
