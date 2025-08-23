(* ------------------------------------------------------------------------- *)
(* Some additional theorem-tactics.                                          *)
(* ------------------------------------------------------------------------- *)

let HOLDS_NNFC_UNFOLD_CONV : conv =
  GEN_REWRITE_CONV TOP_DEPTH_CONV
    [HOLDS_NNFC_UNFOLD; OR_CLAUSES; AND_CLAUSES; NOT_CLAUSES] THENC
  NNFC_CONV;;

(* ------------------------------------------------------------------------- *)
(* Non-recursive building block tactics.                                     *)
(* ------------------------------------------------------------------------- *)

let STRIP_HOLDS_TCL:thm_tactical =
  let strip_tcl:thm_tactical = FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN] in
  let rule = CONV_RULE HOLDS_NNFC_UNFOLD_CONV in
  fun ttac -> REPEAT_TCL strip_tcl ttac o rule;;

let TRIVIAL_ASSUME_LITERAL_THEN:thm_tactical =
  fun ttac th -> TRIVIAL_ASSUME_TAC th ORELSE
                 (SIMP_CLAUSE_TAC th THEN ttac th);;

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

let rec HOLDS_TAC:thm_tactic =
  let assume_tac = TRIVIAL_ASSUME_LITERAL_THEN (ASSUME_LITERAL_TAC "holds") in
  fun th -> assume_tac th THEN TRY (STEP_BOXL2_TCL HOLDS_TAC th);;

(* ------------------------------------------------------------------------- *)
(* General tactics for saturation.                                           *)
(* ------------------------------------------------------------------------- *)

let HOLDS_SIMP_THEN : thm_tactical =
  fun ttac -> ttac o CONV_RULE (CHANGED_CONV HOLDS_NNFC_UNFOLD_CONV);;

(* let SATURATE_STRIP_THEN (thl : thm list) : thm_tactical =
  FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN; IMP_RES_THEN'; HOLDS_SIMP_THEN];; *)

let SATURATE_STRIP_THEN : thm_tactical =
  FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN; IMP_RES_THEN'; HOLDS_SIMP_THEN];;

(* TODO: Fattorizzare con TRIVIAL_ASSUME_LITERAL_THEN. *)
let rec SATURATE_TAC thl th =
  (REPEAT_TCL SATURATE_STRIP_THEN)
  (fun th ->
    TRIVIAL_ASSUME_TAC th ORELSE
    (SIMP_CLAUSE_TAC th THEN
     ASSUME_LITERAL_TAC "sat" th THEN
     ASM_ANTE_RES_THEN thl (SATURATE_TAC thl) th))
  th;;

(* ------------------------------------------------------------------------- *)
(* BOX_RIGHT_TAC (uses SATURATE_TAC).                                        *)
(* ------------------------------------------------------------------------- *)

let BOX_RIGHT_TAC thl : int -> tactic =
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
  fun n ->
    let ptac =
      CONJ_TAC THENL
      [FIRST_ASSUM MATCH_ACCEPT_TAC;
       GEN_TAC THEN
       DISCH_THEN (CONJUNCTS_THEN (SATURATE_TAC thl))] in
    let ttac th = MATCH_MP_TAC th THEN ptac in
    CHECK_NUM_WORLD_TAC n THEN
    (ttac HOLDS_RIGHT_BOX_NUM ORELSE ttac HOLDS_RIGHT_BOX_ALT_NUM);;

(* ------------------------------------------------------------------------- *)
(* Useful for tracing and debugging.                                         *)
(* ------------------------------------------------------------------------- *)

(* let ANTE_RES_THEN' = TRACE_TCL "ANTE_RES_THEN'" ANTE_RES_THEN';; *)
(* let IMP_RES_THEN' = TRACE_TCL "IMP_RES_THEN'" IMP_RES_THEN';; *)
(* let HOLDS_SIMP_THEN = TRACE_TCL "HOLDS_SIMP_THEN" HOLDS_SIMP_THEN;; *)
(* let SATURATE_STRIP_THEN = TRACE_TCL "SATURATE_STRIP_THEN"
                                        SATURATE_STRIP_THEN;; *)
(* let SATURATE_ASSUME_TAC = TRACE_TCL "SATURATE_ASSUME_TAC"
                                       SATURATE_ASSUME_TAC;; *)
(* let SATURATE_TAC = TRACE_TTAC "SATURATE_TAC" SATURATE_TAC;; *)
