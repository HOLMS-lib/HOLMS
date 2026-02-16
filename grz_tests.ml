(* ========================================================================= *)
(* Tests for the Grzegorczyk Logic (Grz).                                    *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025-26.                               *)
(* ========================================================================= *)

needs "HOLMS/grz.ml";;

(* ------------------------------------------------------------------------- *)
(* Basic usage examples.                                                     *)
(* ------------------------------------------------------------------------- *)

HOLMS_RULE `[GRZ_AX . {}
             |~ Box (Box (Atom "p" --> Box Atom "p") --> Atom "p")
                --> Atom "p"]`;;

HOLMS_BUILD_COUNTERMODEL
  `[GRZ_AX . {} |~  Box(Box Atom "p" --> Atom "p") --> Box Atom "p"]`;;

GRZ_CONV `[GRZ_AX . {}
           |~ Box (Box (Atom "p" --> Box Atom "p") --> Atom "p")
              --> Atom "p"]`;;

GRZ_CONV `[GRZ_AX . {} |~  Box(Box Atom "p" --> Atom "p") --> Box Atom "p"]`;;

(* ------------------------------------------------------------------------- *)
(* Tests, examples.                                                          *)
(* ------------------------------------------------------------------------- *)

let pnames = explode "abpqr";;
let pvars = map (fun s -> mk_var(s,form_ty)) pnames
and patoms = map (mk_modal_atom o mk_string) pnames;;
let ipatoms = zip patoms pvars;;
let [atm;btm;ptm;qtm;rtm] = pvars;;
let [a_atom;b_atom;p_atom;q_atom;r_atom] = patoms;;

(* ------------------------------------------------------------------------- *)
(* GZR tests.                                                                *)
(* ------------------------------------------------------------------------- *)

let mk_grz_proves =
  let grzv_tm = `[GRZ_AX . {} |~ p]` in
  fun tm -> let tm' = vsubst ipatoms tm in
            vsubst [tm',ptm] grzv_tm;;

let test_grz_proves = check_conv_true GRZ_CONV o mk_grz_proves;;
let test_grz_disproves = check_conv_false GRZ_CONV o mk_grz_proves;;

(* Proves. *)
test_grz_proves `Box (Box (p --> Box p) --> p) --> p`;;
test_grz_proves `Box p --> p`;;
test_grz_proves `Box Box p --> Box p`;;
test_grz_proves `Box p --> Diam p`;;
test_grz_proves `Box (p --> q) --> (Box p --> q)`;;
test_grz_proves `Box (p --> Box q) --> (p --> q)`;;
test_grz_proves `Diam Box p --> Diam p`;;
test_grz_proves `((a --> Box b) --> Box b) && ((Not a --> Box b) --> Box b) --> Box b`;;
test_grz_proves `Box(Box(a --> Box a) --> Box a) --> Box a`;;
test_grz_proves `(Not p --> Not q) --> (q --> p)`;;

(* Disproves. *)
test_grz_disproves `Box(Box a --> a) --> Box a`;;
test_grz_disproves `Diam a --> Box Diam a`;;
test_grz_disproves `Box(Box a --> b) && Box(Box b --> a)`;;
test_grz_disproves `a --> Diam Box a`;;
test_grz_disproves `Diam Box a --> Box Diam a`;;
test_grz_disproves `p || (Not p && Box(p --> Box p))`;;
test_grz_disproves `Box Diam a --> Box b`;;
