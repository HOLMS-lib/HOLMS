(* ========================================================================= *)
(* Helper functions and tools for decisionp procedures.                      *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

needs "HOLMS/gen_completeness.ml";;

(* ------------------------------------------------------------------------- *)
(* OCaml procedure that returns a list of subformulas of a modal formula.    *)
(* ------------------------------------------------------------------------- *)

let modal_subformulas : term -> term list =
  let rec subform (acc:term list) (l:term list) : term list =
    match l with
    | [] -> setify acc
    | tm :: l ->
      match tm with
      | Var(_, Tyapp("form",_))
      | Const("True",_)
      | Const("False",_)
          -> subform acc l
      | Comb(Const("Atom",_), _)
          -> subform acc l
      | Comb(Const("Not",_), arg)
      | Comb(Const("Box",_), arg)
          -> subform (arg :: acc) (arg :: l)
      | Comb(Comb(Const("&&",_), arg1), arg2)
      | Comb(Comb(Const("||",_), arg1), arg2)
      | Comb(Comb(Const("-->",_), arg1), arg2)
      | Comb(Comb(Const("<->",_), arg1), arg2)
          -> subform (arg1 :: arg2 :: acc) (arg1 :: arg2 :: l)
      | _ -> failwith ("modal_subformulas "^string_of_term tm) in
  fun tm -> subform [] [tm];;

(* Examples: *)
(*
modal_subformulas `Box (Atom a) && Not (Atom a --> True)`;;
modal_subformulas `Box a && Not (a --> True)`;;
*)

let count_modal_subformulas fm =
  1 + length (modal_subformulas fm);;

(* ------------------------------------------------------------------------- *)
(* Tactic that counts the number of worlds in the context.                   *)
(* Assumes that worlds are free variables of type `:num`.                    *)
(* ------------------------------------------------------------------------- *)

let modal_worlds : term -> term list =
  let num_ty = `:num` in
  let isworld = check ((=) num_ty o snd o dest_var) in
  fun tm -> setify (mapfilter isworld (frees tm));;

let ctx_num_worlds : goal -> int =
  let mk_ctx (asl,w) = itlist (curry mk_imp o concl o snd) asl w in
  fun gl ->
    let m = length (modal_worlds (mk_ctx gl)) in
    m;;

let CHECK_NUM_WORLD_TAC : int -> tactic =
  fun n gl ->
    let m = ctx_num_worlds gl in
    report (string_of_int m^" worlds");
    let tac = if m >= n then FAIL_TAC "CHECK_NUM_WORLD_TAC" else ALL_TAC in
    tac gl;;

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

let HOLDS_NNFC_UNFOLD = prove
 (`(!V w:W. ~holds (W,R) V False w) /\
   (!V w. holds (W,R) V True w) /\
   (!V s w. holds (W,R) V (Atom s) w <=> V s w) /\
   (!V p w. holds (W,R) V (Not p) w <=> ~holds (W,R) V p w) /\
   (!p V q w.
      holds (W,R) V (p && q) w <=> holds (W,R) V p w /\ holds (W,R) V q w) /\
   (!p V q w.
      holds (W,R) V (p || q) w <=> holds (W,R) V p w \/ holds (W,R) V q w) /\
   (!p V q w.
      holds (W,R) V (p --> q) w <=>
      ~holds (W,R) V p w \/ holds (W,R) V q w) /\
   (!p V q w.
      holds (W,R) V (p <-> q) w <=>
      (holds (W,R) V p w \/ ~holds (W,R) V q w) /\
      (~holds (W,R) V p w \/ holds (W,R) V q w))`,
  REWRITE_TAC[holds] THEN MESON_TAC[]);;

let HOLDS_LEFT_BOX = prove
 (`!W:W->bool R.
     (!x y. R x y ==> x IN W /\ y IN W)
     ==> !w w' p. R w w' /\ holds (W,R) V (Box p) w ==> holds (W,R) V p w'`,
  REWRITE_TAC[holds] THEN MESON_TAC[]);;

let HOLDS_RIGHT_BOX = prove
 (`!W:W->bool R p w.
     w IN W /\
     (!y. y IN W /\ R w y ==> holds (W,R) V p y)
     ==> holds (W,R) V (Box p) w`,
  REWRITE_TAC[holds] THEN MESON_TAC[]);;

let HOLDS_RIGHT_BOX_ALT = prove
 (`!W:W->bool R Q p w.
     w IN W /\
     (!y. y IN W /\ R w y ==> holds (W,R) V p y \/ Q)
     ==> holds (W,R) V (Box p) w \/ Q`,
  MESON_TAC[HOLDS_RIGHT_BOX]);;

(* ------------------------------------------------------------------------- *)
(* Additional theorem-tactics.                                               *)
(* ------------------------------------------------------------------------- *)

let DISCARD_TAC : thm_tactic =
  let truth_tm = concl TRUTH in
  fun th ->
    let tm = concl th in
    if tm = truth_tm then ALL_TAC else
    fun (asl,w as g) ->
      if exists (fun a -> aconv tm (concl(snd a))) asl then ALL_TAC g
      else failwith "DISCARD_TAC: not already present";;

let NEG_RIGHT_TAC (k:thm_tactic) : tactic =
  let pth = MESON []
    `((~P \/ Q) <=> (P ==> Q)) /\
     (~P <=> (P ==> F))` in
  GEN_REWRITE_TAC I [pth] THEN DISCH_THEN k;;

let NEG_LEFT_TAC : thm_tactic =
  let pth = MESON [] `~P ==> (P \/ Q) ==> Q` in
  MATCH_MP_TAC o MATCH_MP pth;;

let NEG_CONTR_TAC : thm_tactic =
  let pth = MESON [] `~P ==> P ==> Q` in
  fun th -> MATCH_MP_TAC (MATCH_MP pth th) THEN
            FIRST_X_ASSUM MATCH_ACCEPT_TAC;;

let SIMP_CLAUSE_TAC:thm_tactic =
  fun th -> GEN_REWRITE_TAC DEPTH_CONV [th; OR_CLAUSES; NOT_CLAUSES];;

(* TODO: Ottimizzare? *)
(* TRIVIAL_ASSUME_TAC: Takes a literal l and:
   - if l = F or the negation of an assumption, close the goal;
   - if l = T or a an assumption, discard it;
   - fails otherwise.
*)
let TRIVIAL_ASSUME_TAC:thm_tactic =
  fun th -> MAPFILTER_FIRST ((|>) th) [CONTR_TAC; DISCARD_TAC; NEG_CONTR_TAC];;

(* ASSUME_LITERAL_TAC: Takes a literal l and:
   - if l is positive, assume it with label s
   - if l is negative, put its opposite in disjunction in the conclusion.
*)
let ASSUME_LITERAL_TAC (s:string) : thm_tactic =
  let label_tac = LABEL_TAC s in
  fun th -> try NEG_LEFT_TAC th with Failure _ -> label_tac th;;

(* ------------------------------------------------------------------------- *)
(* Additional tacticals.                                                     *)
(* ------------------------------------------------------------------------- *)

(* RULE_THEN rule ttac : thm_tactic *)
(* Applies rule on the theorem then passes it to the continuation tactic. *)
let RULE_THEN (rule : thm -> thm) : thm_tactical = fun ttac th ->
  ttac (rule th);;

(* GEN_REWRITE_THEN : conv -> thm list -> thm_tactic *)
(* Uses GEN_REWRITE and passes it to the continuation tactic. *)
let GEN_REWRITE_THEN conv thl = RULE_THEN (GEN_REWRITE_RULE conv thl);;

(* RES_THEN ttac imp : thm_tactic *)
(* Instantiate the antecedent of imp with one of the assumption of the goal
   then pass it to the continuation tactic.
   Fails only if imp is not an implicative theorem. *)
let RES_THEN : thm_tactical = fun ttac imp ->
  let m = try MATCH_MP imp
          with Failure _ -> failwith "RES_THEN: Not implicative." in
  ASSUM_LIST (fun asl -> EVERY (mapfilter (ttac o m) asl));;

(* ------------------------------------------------------------------------- *)
(* Saturation machinery.                                                     *)
(* ------------------------------------------------------------------------- *)

let HOLMS_STRIP_THEN (thl : thm list) : thm_tactical =
  let RW_TAC = GEN_REWRITE_THEN I thl in
  FIRST_TCL[CONJUNCTS_THEN; DISJ_CASES_THEN; RES_THEN; RW_TAC];;

(* HOLMS_SATURATE_TAC : thm list -> thm_tactic *)
(* Main recursive saturation tactic.  Never fails. *)
let rec HOLMS_SATURATE_TAC =
  let REPEAT_STRIP_THEN = REPEAT_TCL (HOLMS_STRIP_THEN[HOLDS_NNFC_UNFOLD]) in
  fun thl ->
    REPEAT_STRIP_THEN
    (fun th -> TRIVIAL_ASSUME_TAC th ORELSE
               (SIMP_CLAUSE_TAC th THEN
                ASSUME_LITERAL_TAC "sat" th THEN
                ASM_ANTE_RES_THEN thl (HOLMS_SATURATE_TAC thl) th));;

(* ------------------------------------------------------------------------- *)
(* Tactics for right rules.                                                  *)
(* ------------------------------------------------------------------------- *)

let MATCH_BOX_RIGHT_TAC : tactic =
  let HOLDS_RIGHT_BOX_NUM = prove
   (`!p w:num.
       w IN W /\
       (!y. y IN W /\ R w y ==> holds (W,R) V p y)
       ==> holds (W,R) V (Box p) w`,
    MATCH_ACCEPT_TAC HOLDS_RIGHT_BOX)
  and HOLDS_RIGHT_BOX_ALT_NUM = prove
   (`!Q p w:num.
       w IN W /\
       (!y. y IN W /\ R w y ==> holds (W,R) V p y \/ Q)
       ==> holds (W,R) V (Box p) w \/ Q`,
    MATCH_ACCEPT_TAC HOLDS_RIGHT_BOX_ALT) in
  (MATCH_MP_TAC HOLDS_RIGHT_BOX_NUM ORELSE
   MATCH_MP_TAC HOLDS_RIGHT_BOX_ALT_NUM) THEN
  CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; GEN_TAC];;

(* TODO: Si può semplificare ptac (?ridurre a SATURATE_TAC?) *)
let BOX_RIGHT_THEN : (tactic * thm_tactic) -> int -> tactic =
  fun (MATCH_BOX_RIGHT_TAC,SATURATE_TAC) ->
    fun n -> CHECK_NUM_WORLD_TAC n THEN
             MATCH_BOX_RIGHT_TAC THEN DISCH_THEN SATURATE_TAC

let HOLMS_RIGHT_TAC (SATURATE_TAC : thm_tactic) : tactic =
  PURE_ASM_REWRITE_TAC[HOLDS_NNFC_UNFOLD;
                       AND_CLAUSES; OR_CLAUSES; NOT_CLAUSES] THEN
  CONV_TAC (NNFC_CONV THENC CNF_CONV) THEN
  REPEAT CONJ_TAC THEN
  (* TODO: TRY è superfluo(?) *)
  TRY (NEG_RIGHT_TAC SATURATE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let dest_box = function
    Comb(Const("Box",_),tm) -> tm
  | _ -> failwith "dest_box";;

let dest_holds = function
    Comb(Comb(Comb(Comb(Const("holds",_),_),_),tm),_) -> tm
  | _ -> failwith "dest_holds";;

(* ------------------------------------------------------------------------- *)
(* Sorting clauses.                                                          *)
(* ------------------------------------------------------------------------- *)

let holds_rank tm =
  try 0,dest_holds(dest_neg tm) with Failure _ ->
  try let x = dest_holds tm in
      try 1,dest_box x with Failure _ -> 2,x
  with Failure _ -> 3,tm;; (* This case should never occur in practice. *)

(* Must be a total order, otherwise we may have loops in the main tactic. *)
let holds_lt tm1 tm2 =
  let c1 = compare tm1 tm2 in
  if c1 = 0 then false else
  let r1,x1 = holds_rank tm1
  and r2,x2 = holds_rank tm2 in
  if r1 <> r2 then r1 < r2 else
  let c2 = compare x1 x2 in
  if c2 = 0 then c1 > 0 else
  if free_in x1 x2 then true else
  if free_in x2 x1 then false else
  c2 > 0;;

let SORT_BOX_CONV : conv =
  let f = list_mk_disj o uniq o mergesort holds_lt o striplist dest_disj in
  fun tm -> DISJ_ACI_RULE (mk_eq(tm,f tm));;

let SORT_BOX_TAC : tactic = CONV_TAC SORT_BOX_CONV;;

(* ------------------------------------------------------------------------- *)
(* The work horse of the tactic.                                             *)
(* ------------------------------------------------------------------------- *)

(* TODO: Cosa mettere in coda a intro_tac?  Forse SATURATE_TAC? *)
let HOLMS_PREPARE_TAC : thm_tactic =
  let rewr_tac = REWRITE_TAC[diam_DEF; dotbox_DEF]
  and intro_tac = INTRO_TAC "![W] [R]; frame; ![V] [w]" THEN STRIP_TAC in
  fun compl_thm ->
    REPEAT GEN_TAC THEN REPEAT (CONV_TAC let_CONV) THEN REPEAT GEN_TAC THEN
    rewr_tac THEN MATCH_MP_TAC compl_thm THEN
    intro_tac THEN REPEAT GEN_TAC;;

let HOLMS_STEP_TAC (MATCH_BOX_RIGHT_TAC,SATURATE_TAC) : int -> tactic =
  let box_right_tac = BOX_RIGHT_THEN (MATCH_BOX_RIGHT_TAC,SATURATE_TAC)
  and right_tac = HOLMS_RIGHT_TAC SATURATE_TAC in
  fun n -> (FIRST o map CHANGED_TAC)
             [right_tac;
              SORT_BOX_TAC THEN box_right_tac n];;

let INNER_HOLMS_TAC (MATCH_BOX_RIGHT_TAC,SATURATE_TAC) : int -> tactic =
  let STEP_TAC = HOLMS_STEP_TAC (MATCH_BOX_RIGHT_TAC,SATURATE_TAC) in
  fun  (n : int) -> REPEAT (STEP_TAC n);;

(* ------------------------------------------------------------------------- *)
(* Dispatch mechanism.                                                       *)
(* Define HOLMS_TAC, HOLMS_RULE and HOLMS_BUILD_COUNTERMODEL.                *)
(* ------------------------------------------------------------------------- *)

let holms_decid_tactics : (term * tactic) list ref = ref [];;
(*
  [`{}:form->bool`,K_TAC;
   `T_AX`,T_TAC;
   `K4_AX`,K4_TAC;
   `GL_AX`,GL_TAC];;
*)

let holms_register_tactic (tm : term) (tac : tactic) : unit =
  holms_decid_tactics := (tm,tac) :: !holms_decid_tactics;;

let get_holms_tactic (tm : term) : tactic =
  assoc tm !holms_decid_tactics;;

let holms_dispatch_tac : term -> tactic =
  let ptm = `[S . H |~ p]` in
  let _,[tmS;_;_] = strip_comb ptm in
  fun tm ->
    let inst = term_match [] ptm tm in
    let tm_ax = instantiate inst tmS in
    get_holms_tactic tm_ax ;;

(* Example: *)
(* holms_dispatch `[K4_AX . {} |~ Box a --> a]`;; *)

let HOLMS_DISPATCH_TAC : tactic =
  fun (asl,w) as gl -> holms_dispatch_tac w gl;;

let HOLMS_TAC : tactic =
  REPEAT (GEN_TAC ORELSE CONV_TAC (CHANGED_CONV let_CONV)) THEN
  REWRITE_TAC[diam_DEF; dotbox_DEF] THEN HOLMS_DISPATCH_TAC;;

let HOLMS_RULE (tm : term) : thm =
  prove(tm,HOLMS_TAC);;

let the_HOLMS_countermodel : term ref = ref `no_countermodel:bool`;;

let HOLMS_BUILD_COUNTERMODEL tm =
  let proved = try ignore (HOLMS_RULE tm); true
               with Failure _ -> false in
  if proved then failwith "There is no countermodel." else
  let th = REWRITE_CONV [] !the_HOLMS_countermodel in
  rhs (concl th);;
