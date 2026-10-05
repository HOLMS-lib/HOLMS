# `HOLMS.SetConsistent`

Lean module: [`../HOLMS/SetConsistent.lean`](../HOLMS/SetConsistent.lean)

HOL Light source: [`../../setconsistent.ml`](../../setconsistent.ml)

This note records choices specific to consistency and maximal extensions. The
project-wide decision to use sets rather than lists is explained in
[`../CONVENTIONS.md`](../CONVENTIONS.md).

## One consistency interface

`SETCONSISTENT S X` is defined directly as non-derivability of modal falsity
from the set `X`. `MAXIMAL_SETCONSISTENT S p X` means that `X` is consistent
and decides every subformula of the distinguished formula `p`.

The module translates `setconsistent.ml`; it does not introduce parallel
list-valued versions of consistency or maximality from `consistent.ml`.
Consequently weakening and extension hypotheses are set inclusions, and later
canonical worlds can use the same type without conversion through
`set_of_list`.

## Subsentences and closure

`Subsentence q p` is an inductive proposition saying that `q` is either a
subformula of `p` or the negation of one. Its finiteness theorem is obtained
from the finite subformula set and a finite image under negation.

Maximal-consistency lemmas expose membership as derivability for relevant
subformulas and their negations. The Boolean closure results for negation,
conjunction, disjunction, implication, and equivalence are then phrased
directly as membership equivalences. This API is designed for rewriting in the
canonical truth lemma and avoids an intermediate iterated conjunction of a
list.

The historical misspelling `MIONOR` in the conjunction closure theorem name
is retained for compatibility with the HOL Light theorem name.

## Maximal extension

`EXTEND_MAXIMAL_SETCONSISTENT` performs finite recursion over the `Finset` of
subformulas of `p`. At each step it inserts either the formula or its negation,
using `SETCONSISTENT_EXTEND_CASES` to preserve consistency. The resulting set
is shown to contain the original context, consist only of subsentences, remain
finite, and decide every subformula.

This construction replaces the list enumeration, duplicate removal, and
permutation obligations of the HOL Light list presentation. The finset is an
implementation device for recursion; the theorem's logical input and output
remain sets.

`NONEMPTY_MAXIMAL_SETCONSISTENT` obtains a canonical world containing `¬p`
from the consistency of the singleton negation, using the calculus's
double-negation and contradiction results. It is the entry point used by the
generic countermodel construction.

## Source material not reproduced

No bridges to `CONSISTENT`, no-repetition lists, or list permutations are
provided. They would recreate a representation boundary deliberately removed
from the Lean development. A local list or finset may still enumerate a finite
set, but it does not define a second logical notion of consistency.
