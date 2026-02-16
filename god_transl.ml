(* ========================================================================= *)
(* Experiments with the "GOD" translation.                                   *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2026.                                  *)
(* ========================================================================= *)

needs "HOLMS/grz_tests.ml";;

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

let GOD_TRANSL_CONV : conv = REWRITE_CONV[TRANSL; GOD];;

(* ------------------------------------------------------------------------- *)
(* Examples: Prove a formula of intuitionistic propositional logic           *)
(* via its tranlation in GL.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Example: Prove formula (p --> p). *)
`[GRZ_AX . {} |~ GOD (Atom "p" --> Atom "p")]`
|> run_conv GOD_TRANSL_CONV
|> run_conv GRZ_CONV;;

(* Example: Excluded Middle: (p || Not p) is not provable "in GOD". *)
let tm = `[GL_AX . {} |~ TRANSL (GOD (Atom "p" || Not Atom "p"))]`;;
let tm' = tm
          |> run_conv GOD_TRANSL_CONV
          |> run_conv (REWRITE_CONV[dotbox_DEF]);;
check_conv_false GL_CONV tm';;
(* Countermodel *)
let ctm = !the_HOLMS_countermodel
          |> vsubst[`R_PLUS (W:num->bool) R`,`R:num->num->bool`];;

(* ------------------------------------------------------------------------- *)
(* GOD tests.                                                                *)
(* ------------------------------------------------------------------------- *)

let mk_god_proves =
  let grzv_tm = `[GRZ_AX . {} |~ GOD p]` in
  fun tm -> let tm' = vsubst ipatoms tm in
            vsubst [tm',ptm] grzv_tm;;

let GOD_CONV = PURE_REWRITE_CONV[GOD] THENC GRZ_CONV;;
let test_god_proves = check_conv_true GOD_CONV o mk_god_proves;;
let test_god_disproves = check_conv_false GOD_CONV o mk_god_proves;;

(* Proves. *)
test_god_proves `p --> q || q --> p`;;
test_god_disproves `q || (q --> (p || Not q))`;;
(* Questi sotto non terminano (provati per circa 30min)! *)
(* test_god_proves `(q --> p) --> (Not p --> Not q)`;; *)
(* test_god_proves `(Not p --> q || r) --> (Not p --> q) || (Not p --> r)`;; *)

(* Disproves. *)
test_god_disproves `p || Not p`;;
test_god_disproves `Not Not p --> p`;;
(* Questi sotto non terminano (provati per circa 30min)! *)
(* test_god_disproves `(Not p --> Not q) --> (q --> p)`;; *)

(* ************************************************************************* *)
(* ************************************************************************* *)
(*                                                                           *)
(*                     Size of the unctractable terms                        *)
(*                                                                           *)
(* ************************************************************************* *)
(* ************************************************************************* *)

let swap (x,y) = (y,x);;

(* ------------------------------------------------------------------------- *)
(* First example (reversed contrapositive):                                  *)
(* (Not p --> Not q) --> (q --> p)                                           *)
(* ------------------------------------------------------------------------- *)

g `[GRZ_AX . {} |~ GOD ((Not Atom "p" --> Not Atom "q")
                        --> (Atom "q" --> Atom "p"))]`;;
e (REWRITE_TAC[GOD]);;
(* e (CONV_TAC GRZ_CONV);; *)
e (CONV_TAC (GEN_REWRITE_CONV I [GRZ_TRANSL]));;
e (CONV_TAC (GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV)
                              [TRANSL; diam_DEF; dotbox_DEF]));;
(* e GL_TAC;; *)

`(Not p --> Not q) --> (q --> p)`
|> mk_god_proves
|> run_conv (REWRITE_CONV[GOD; GRZ_TRANSL; TRANSL; diam_DEF; dotbox_DEF])
|> rand
|> subst (map swap ipatoms)
;;

(*
val tm : term =
  `Box (Box (Box Not (Box p && p) && Not (Box p && p) -->
             Box Not (Box q && q) && Not (Box q && q)) &&
        (Box Not (Box p && p) && Not (Box p && p) -->
         Box Not (Box q && q) && Not (Box q && q)) -->
        Box (Box q && q --> Box p && p) && (Box q && q --> Box p && p)) &&
   (Box (Box Not (Box p && p) && Not (Box p && p) -->
         Box Not (Box q && q) && Not (Box q && q)) &&
    (Box Not (Box p && p) && Not (Box p && p) -->
     Box Not (Box q && q) && Not (Box q && q)) -->
    Box (Box q && q --> Box p && p) && (Box q && q --> Box p && p))`
*)

(* ------------------------------------------------------------------------- *)
(* Second example:                                                           *)
(* (Not p --> q || r) --> (Not p --> q) || (Not p --> r)                     *)
(* ------------------------------------------------------------------------- *)

g `[GRZ_AX . {} |~
    GOD ((Not Atom "p" --> Atom "q" || Atom"r")
         --> (Not Atom "p" --> Atom "q") ||
             (Not Atom "p" --> Atom"r"))]`;;
e (REWRITE_TAC[GOD]);;
(* e (CONV_TAC GRZ_CONV);; *)
e (CONV_TAC (GEN_REWRITE_CONV I [GRZ_TRANSL]));;
e (CONV_TAC (GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV)
                              [TRANSL; diam_DEF; dotbox_DEF]));;
(* e GL_TAC;; *)

`(Not p --> q || r) --> (Not p --> q) || (Not p --> r)`
|> mk_god_proves
|> run_conv (REWRITE_CONV[GOD; GRZ_TRANSL; TRANSL; diam_DEF; dotbox_DEF])
|> rand
|> subst (map swap ipatoms)
;;

(*
val it : term =
  `Box (Box (Box Not (Box p && p) && Not (Box p && p) -->
             Box q && q || Box r && r) &&
        (Box Not (Box p && p) && Not (Box p && p) -->
         Box q && q || Box r && r) -->
        Box (Box Not (Box p && p) && Not (Box p && p) --> Box q && q) &&
        (Box Not (Box p && p) && Not (Box p && p) --> Box q && q) ||
        Box (Box Not (Box p && p) && Not (Box p && p) --> Box r && r) &&
        (Box Not (Box p && p) && Not (Box p && p) --> Box r && r)) &&
   (Box (Box Not (Box p && p) && Not (Box p && p) -->
         Box q && q || Box r && r) &&
    (Box Not (Box p && p) && Not (Box p && p) --> Box q && q || Box r && r) -->
    Box (Box Not (Box p && p) && Not (Box p && p) --> Box q && q) &&
    (Box Not (Box p && p) && Not (Box p && p) --> Box q && q) ||
    Box (Box Not (Box p && p) && Not (Box p && p) --> Box r && r) &&
    (Box Not (Box p && p) && Not (Box p && p) --> Box r && r))`
*)
