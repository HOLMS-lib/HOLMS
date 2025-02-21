(* ========================================================================= *)
(* Helper functions and tools for decisionp procedures.                      *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

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
(* Some additional theorem-tactics.                                          *)
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

let HOLDS_NNFC_UNFOLD_CONV : conv =
  GEN_REWRITE_CONV TOP_DEPTH_CONV
    [HOLDS_NNFC_UNFOLD; OR_CLAUSES; AND_CLAUSES] THENC
  NNFC_CONV;;

(* ------------------------------------------------------------------------- *)
(* Non-recursive building block tactics.                                     *)
(* ------------------------------------------------------------------------- *)

let STRIP_HOLDS_TCL:thm_tactical =
  let strip_tcl:thm_tactical = FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN] in
  let rule = CONV_RULE HOLDS_NNFC_UNFOLD_CONV in
  fun ttac -> REPEAT_TCL strip_tcl ttac o rule;;

let ASSUME_HOLDS_LITERAL_TAC:thm_tactic =
  let rewr_tac th =
    let pth = MESON[]
      `(T \/ p <=> T) /\ (p \/ T <=> T) /\
       (F \/ p <=> p) /\ (p \/ F <=> p)` in
      GEN_REWRITE_TAC DEPTH_CONV [th; pth] in
  let lbl_tac th = rewr_tac th THEN
                   (CONTR_TAC th ORELSE
                    DISCARD_TAC th ORELSE
                    LABEL_TAC "holds" th) in
  fun th ->
    rewr_tac th THEN
    FIRST (mapfilter (fun ttac -> ttac th)
                     [NEG_CONTR_TAC; NEG_LEFT_TAC; lbl_tac]);;

let STEP_BOXL1_TCL : thm_tactical = fun k acc ->
  USE_THEN "boxl1" (fun boxl1 ->
    try let f = MATCH_MP (MATCH_MP boxl1 acc) in
        ASSUM_LIST (MAP_EVERY (STRIP_HOLDS_TCL k) o mapfilter f)
    with Failure _ -> ALL_TAC);;

let STEP_BOXL2_TCL : thm_tactical = fun k hth ->
  USE_THEN "boxl2" (fun boxl2 ->
    try let f = MATCH_MP (MATCH_MP boxl2 hth) in
        ASSUM_LIST (MAP_EVERY (STRIP_HOLDS_TCL k) o mapfilter f)
    with Failure _ -> ALL_TAC);;

let rec HOLDS_TAC:thm_tactic = fun th ->
  ASSUME_HOLDS_LITERAL_TAC th THEN
  TRY (STEP_BOXL2_TCL HOLDS_TAC th);;

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
  try ignore (HOLMS_RULE tm);
      failwith "There is no countermodel."
  with Failure _ ->
    report "Countermodel found:";
    let th = REWRITE_CONV [] !the_HOLMS_countermodel in
    print_term (rhs (concl th));
    report "";;
