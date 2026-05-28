(* ========================================================================= *)
(* Examples and Statistics from "Grzegorczyk Logic Unlocked" , Woloszyn 2025 *)
(* https://arxiv.org/pdf/2505.09836                                          *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2026.                                  *)
(* ========================================================================= *)

let CONTINGENT = new_definition
  `CONTINGENT p = Diam p && Diam Not p`;;

let PENULTIMATE = new_definition
  `PENULTIMATE p = p && Diam Not p && Box (Not p --> Box Not p)`;;

(* Schema *)
g `[GRZ_AX . {} |~
    CONTINGENT (Atom "p")
    --> Diam(PENULTIMATE (Atom "p") || PENULTIMATE (Not Atom "p"))]`;;
e (REWRITE_TAC[CONTINGENT; PENULTIMATE]);;
e (REWRITE_TAC[diam_DEF]);;
e (GEN_REWRITE_TAC I [GRZ_TRANSL]);;
e (CONV_TAC (RAND_CONV TRANSL_CONV));;
time e (CONV_TAC GRZ_CONV);;  (* 44.951151 *)
e (REWRITE_TAC[dotbox_DEF]);;
e (CONV_TAC (NNF_CONV THENC CNF_CONV));;
top_thm();;

parse_as_prefix("B");;
let tm = (rhs o concl) ((NNF_CONV THENC CNF_CONV)
`~ (B ~ a /\ ~ a) /\
     ~ (B ~ ~ a /\ ~ ~ a) ==>
     ~ (B ~ (a /\
                   ~ (B ~ ~ a /\ ~ ~ a) /\
                   B (~ a ==> B ~ a /\ ~ a) /\
                   (~ a ==> B ~ a /\ ~ a) \/
                   ~ a /\
                   ~ (B ~ ~ ~ a /\ ~ ~ ~ a) /\
                   B (~ ~ a ==> B ~ ~ a /\ ~ ~ a) /\
                   (~ ~ a ==> B ~ ~ a /\ ~ ~ a)) /\
          ~ (a /\
               ~ (B ~ ~ a /\ ~ ~ a) /\
               B (~ a ==> B ~ a /\ ~ a) /\
               (~ a ==> B ~ a /\ ~ a) \/
               ~ a /\
               ~ (B ~ ~ ~ a /\ ~ ~ ~ a) /\
               B (~ ~ a ==> B ~ ~ a /\ ~ ~ a) /\
               (~ ~ a ==> B ~ ~ a /\ ~ ~ a)))`);;

let cl = striplist dest_conj tm;;
length cl;;
(* ~~~> 44 *)

end_itlist min (map (length o striplist dest_disj) cl);;
(* ~~~> 7 *)

end_itlist min (map (length o striplist dest_disj) cl);;
(* ~~~> 3 *)

let rec size tm =
  try let a,b = try dest_conj tm with Failure _ ->
                try dest_disj tm with Failure _ ->
                try dest_imp tm with Failure _ ->
                fail ()
      in size a + size b + 1
  with Failure _ ->
  try let a = try dest_neg tm with Failure _ ->
              try let f,x = dest_comb tm in
                      if name_of f = "B" then x else fail()
              with Failure _ ->
              fail()
      in size a + 1
  with Failure _ ->
    1;;

size tm;;
(* ~~~> 4359 *)

(* \Diamond a \land \Diamond \neg a \to
     \Diamond (a \land
           \Diamond \neg a \land
           \Box (\neg a \to \Box \neg a) \lor
           \neg a \land
           \Diamond \neg \neg a \land
           \Box (\neg \neg a \to \Box \neg \neg a)) *)

(*

\neg \boxdot \neg a \land \neg \boxdot \neg \neg a \to
     \neg \boxdot \neg (a \land
                     \neg \boxdot \neg \neg a \land
                     \boxdot (\neg a \to \boxdot \neg a) \lor
                     \neg a \land
                     \neg \boxdot \neg \neg \neg a \land
                     \boxdot (\neg \neg a \to \boxdot \neg \neg a))

*)

HOLMS_BUILD_COUNTERMODEL
  `[GRZ_AX . {} |~ Diam Box Atom "p" --> Box Diam Atom "p"]`;;
(*
   holds (W,R_PLUS W R) V (Box p) y' /\
   V "p" y' /\
   holds (W,R_PLUS W R) V (Box Not (Box p && p)) y' /\
   R_PLUS W R w y' /\
   y' IN W /\
   holds (W,R_PLUS W R) V (Box Not p) y /\
   holds (W,R_PLUS W R) V (Box Not (Box Not p && Not p)) y /\
   R_PLUS W R w y /\
   y IN W /\
   w IN W /\
   W,R_PLUS W R IN ITF /\
   ~V "p" y
*)

HOLMS_BUILD_COUNTERMODEL
  `[GRZ_AX . {} |~ Box (Box Atom "p" --> Atom "p") --> Box Atom "p"]`;;
(*
   holds (W,R_PLUS W R) V (Box p) y /\
   R_PLUS W R w y /\
   y IN W /\
   holds (W,R_PLUS W R) V (Box (Box p && p --> p)) w /\
   V "p" w /\
   w IN W /\
   W,R_PLUS W R IN ITF /\
   ~V "p" y`
*)
