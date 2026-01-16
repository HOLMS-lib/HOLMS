(* ========================================================================= *)
(* Experiments with translations of modal formulas.                          *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2026.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Run a conversion.                                                         *)
(* ------------------------------------------------------------------------- *)

let run_conv (conv:conv) tm =
  let etm =
    try concl (conv tm)
    with Failure _ -> failwith "run_conv: Conversion fails" in
  try rhs etm
  with Failure _ -> failwith "run_conv: Not equational";;  

(* ------------------------------------------------------------------------- *)
(* Check the result of a conversion.                                         *)
(* ------------------------------------------------------------------------- *)

let check_conv conv tm1 tm2 =
  let tm = try run_conv conv tm1
           with Failure s -> failwith ("check_conv: "^s) in
  if tm = tm2 then () else failwith "check_conv: Not the expected result";; 

(* ------------------------------------------------------------------------- *)
(* Translation: Box  ~~>  Dotbox.                                            *)
(* ------------------------------------------------------------------------- *)

let TRANSL = define
  `(!s. TRANSL (Atom s) = Atom s) /\
   TRANSL True = True /\
   TRANSL False = False /\
   (!p. TRANSL (Not p) = Not (TRANSL p)) /\
   (!p q. TRANSL (p && q) = TRANSL p && TRANSL q) /\
   (!p q. TRANSL (p || q) = TRANSL p || TRANSL q) /\
   (!p q. TRANSL (p --> q) = TRANSL p --> TRANSL q) /\
   (!p q. TRANSL (p <-> q) = TRANSL p <-> TRANSL q) /\
   (!p. TRANSL (Box p) = Dotbox (TRANSL p))`;;

let TRANSL_CONV:conv = REWRITE_CONV[TRANSL];;

(* ------------------------------------------------------------------------- *)
(* Tests.                                                                    *)
(* ------------------------------------------------------------------------- *)

check_conv TRANSL_CONV `TRANSL (Atom a)` `Atom a`;;
check_conv TRANSL_CONV `TRANSL True` `True`;;
check_conv TRANSL_CONV `TRANSL False` `False`;;
check_conv TRANSL_CONV `TRANSL (Not True)` `Not True`;;
check_conv TRANSL_CONV `TRANSL (Atom a --> Atom b)` `Atom a --> Atom b`;;
check_conv TRANSL_CONV `TRANSL (p --> q)` `TRANSL p --> TRANSL q`;;
check_conv TRANSL_CONV `TRANSL (Box (Atom a))` `Dotbox Atom a`;;
check_conv TRANSL_CONV `TRANSL (Box (p --> Box q))`
                       `Dotbox (TRANSL p --> Dotbox TRANSL q)`;;

(* ------------------------------------------------------------------------- *)
(* Examples: Prove a formula of S4 via its tranlation in K4.                 *)
(* ------------------------------------------------------------------------- *)

(* Example: Box a --> a *)
let tm = `[K4_AX . {} |~ TRANSL (Box Atom a --> Atom a)]`;;
let tm' = run_conv TRANSL_CONV tm;;
time HOLMS_RULE tm';; (* CPU time (user): 0.059983 *)

(* Example: Box (Box (a --> Box a) --> a) --> a *)
let tm = `[GL_AX . {} |~ TRANSL (Box (Box (Atom a --> Box Atom a) --> Atom a) --> Atom a)]`;;
let tm' = run_conv TRANSL_CONV tm;;
time HOLMS_RULE tm';; (* CPU time (user): 0.064883 *)

(* ------------------------------------------------------------------------- *)
(* Examples: Prove a formula of S4 via its tranlation in GL.                 *)
(* ------------------------------------------------------------------------- *)

(* Example: Box a --> a *)
let tm = `[GL_AX . {} |~ TRANSL (Box Atom a --> Atom a)]`;;
let tm' = run_conv TRANSL_CONV tm;;
time HOLMS_RULE tm';; (* CPU time (user): 0.002222 *)

(* ------------------------------------------------------------------------- *)
(* General theorem.                                                          *)
(* ------------------------------------------------------------------------- *)

g `!p. [S4_AX . {} |~ p] ==> [K4_AX . {} |~ TRANSL p]`;;
(* TODO *)

(* ------------------------------------------------------------------------- *)
(* "God" translation: GOD (p --> q)  ~~>  Box (GOD p --> GOD q).             *)
(* ------------------------------------------------------------------------- *)

let GOD = define
  `(!s. GOD (Atom s) = Box Atom s) /\
   GOD True = Box True /\
   GOD False = False /\
   (!p. GOD (Not p) = Box Not (GOD p)) /\
   (!p q. GOD (p && q) = GOD p && GOD q) /\
   (!p q. GOD (p || q) = GOD p || GOD q) /\
   (!p q. GOD (p --> q) = Box (GOD p --> GOD q)) /\
   (!p q. GOD (p <-> q) = Box (GOD p --> GOD q) && Box (GOD q --> GOD p))`;;

let GOD_CONV:conv = REWRITE_CONV[TRANSL; GOD];;

(* ------------------------------------------------------------------------- *)
(* Examples: Prove a formula of intuitionistic propositional logic           *)
(* via its tranlation in GL.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Example: Prove formula (p --> p). *)
let tm = `[GL_AX . {} |~ TRANSL (GOD (Atom "p" --> Atom "p"))]`;;
let tm' = run_conv GOD_CONV tm;;
HOLMS_RULE tm';;

(* Example: Excluded Middle (p || Not p) is not provable. *)
let tm = `[GL_AX . {} |~ TRANSL (GOD (Atom "p" || Not Atom "p"))]`;;
let tm' = run_conv GOD_CONV tm;;
let tm' = subst [`p:form`,`Atom "p"`] tm';;
let tm' = run_conv (REWRITE_CONV[dotbox_DEF]) tm';;
HOLMS_RULE tm';;
let ctm = HOLMS_BUILD_COUNTERMODEL tm';;
GL_HOLMS_CERTIFY_COUNTERMODEL ctm tm';;

(* ------------------------------------------------------------------------- *)
(* ML function for modal formula translations (Box  ~~>  Dotbox).            *)
(* ------------------------------------------------------------------------- *)

let rec transl tm =
  if tm = modal_true_tm || tm = modal_false_tm || is_modal_atom tm then tm else
  if is_modal_not tm then mk_modal_not(transl(rand tm)) else
  if is_modal_conj tm || is_modal_disj tm ||
     is_modal_imp tm || is_modal_iff tm then
    let ftm,rtm = dest_comb tm in
    let optm,ltm = dest_comb ftm in
    mk_comb(mk_comb(optm,transl ltm),transl rtm)
  else if not (is_modal_box tm) then failwith "transl" else
  let tm' = transl (rand tm) in
  mk_modal_conj(mk_modal_box tm') tm';;

try transl `p --> q` with Failure _ -> `"OK"`;;
transl `Atom a`;;
transl `True`;;
transl `False`;;
transl `Not True`;;
transl `Atom "p" --> Atom "q"`;;
transl `Box (Atom "a")`;;
