# `HOLMS.GenCompleteness`

Lean module: [`../HOLMS/GenCompleteness.lean`](../HOLMS/GenCompleteness.lean)

HOL Light source: [`../../gen_completeness.ml`](../../gen_completeness.ml)

This note records the implementation of the generic canonical-model
construction. Shared conventions, especially the choice of set-valued worlds,
are in [`../CONVENTIONS.md`](../CONVENTIONS.md).

## Canonical objects

Canonical worlds have type `Set Form`. `PARAMETRIC_STD_WORLD` describes the
world predicate abstractly, while `GEN_STANDARD_WORLD` specializes it to
maximal set-consistent subsentences. Standard frames and models therefore use
the ambient world type `Set Form`, and the canonical valuation makes an atom
true exactly when that atom belongs to the current world.

`STANDARD_EVAL` and the historically named `SET_STANDARD_EVAL` denote the
same valuation. The equality theorem is kept to preserve a useful comparison
point with the source without creating two implementations.

The HOL Light characterization theorem `GEN_STANDARD_WORLD` is named
`GEN_STANDARD_WORLD_EQ` in Lean because `GEN_STANDARD_WORLD` already names
the definition.

In HOL Light, `STANDARD_EVAL` acts on list worlds and `SET_STANDARD_EVAL` on
set worlds. Both act on set worlds in Lean and are definitionally equal.

## Truth lemma

`GEN_TRUTH_LEMMA` is proved by induction on the formula. The propositional
cases rewrite with the closure equivalences from `SetConsistent`; the modal
case uses the standard-frame condition and the induction hypothesis at each
successor.

The theorem retains the source assumption that the distinguished formula is
not derivable. The structural truth-lemma proof does not use that assumption
directly, but keeping it in the interface matches the generic HOL Light result
and the countermodel theorems that consume it.

The substantially shorter proof is mainly a consequence of set-valued worlds,
not of an inherent advantage of Lean over HOL Light. Membership closure is
already stated in the form required by the induction, so there is no passage
through a list, `set_of_list`, or `CONJLIST`.

## Finiteness and accessibility

Canonical-frame finiteness follows because every world is a subset of the
finite set of subsentences. Lean can therefore apply finiteness of the set of
subsets directly, rather than enumerating duplicate-free lists.

Box contents are set comprehensions. `GEN_BOX_CONTENT` contains the unboxed
contents of boxes in a world; `GEN_BOX_CONTENT_K4` additionally retains the
boxed formulas needed by stronger canonical relations. The historical theorem
name `XK_SUBLIST_XK4` is preserved, but its Lean conclusion is set inclusion
rather than a list relation.

The private theorem `box_derivation_from_context` is the local lifting
principle used by accessibility: a derivation from a context can be lifted
under `box` when the target context contains the box of every hypothesis. It
replaces the source construction through boxed lists and iterated
conjunctions. It remains private until another module needs the same fact; at
that point it should be promoted to a proof-theoretic module rather than
duplicated.

The generic successor is obtained by extending
`insert (¬q) (GEN_BOX_CONTENT w)` to a maximal set-consistent world. Set
inclusion expresses all preservation obligations.

## Countermodels and validity transport

`GEN_COUNTERMODEL` and `GEN_COUNTERMODEL_ALT` construct finite canonical
countermodels directly on set-valued worlds. The source's second conversion
from list worlds to set worlds is unnecessary.

There is one important cost to the chosen representation: the full type
`Set Form` is not countable. To establish completeness over an arbitrary
infinite carrier, the implementation embeds only the finite subtype of worlds
designated by the particular canonical frame. It transports the frame and
valuation along that embedding and proves the old and new models bisimilar;
`Form.valid_of_bisimilar` then transfers validity. This finite-subtype
transport replaces the source's countability argument without adding a
cardinality assumption or an axiom.

## Source material not reproduced

The `MEM_FLATMAP_LEMMA` family is replaced by membership in set
comprehensions. Permutation and `set_of_list` invariance lemmas, together with
the auxiliary `GEN_STDWORLDS` and `GEN_STDREL` predicates, are omitted because
their only role was to cross the discarded list/set boundary.
