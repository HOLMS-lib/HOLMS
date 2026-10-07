# Consistency and maximal consistent extensions

This chapter develops consistency of collections of modal formulas,
maximal consistency relative to a fixed formula, Boolean membership laws,
and finite maximal extensions. Statements and informal proofs are presented
together, independently of proof-assistant syntax.

The prerequisites are [subformulas and modal syntax](Modal.md) and the
[axiomatic calculus](Calculus.md), particularly weakening, the deduction
theorem, and classical propositional reasoning. See the
[mathematical documentation index](README.md) for other chapters.
The primary formal references are
[HOL Light's `setconsistent.ml`](../setconsistent.ml) and
[Lean's `HOLMS/SetConsistent.lean`](../lean/HOLMS/SetConsistent.lean).
Names in **Formalization references** occur in both files unless explicitly
distinguished; Lean names are relative to namespace `HOLMS`.
Implementation choices are discussed in the
[SetConsistent translation notes](../lean/translation/SetConsistent.md).

## 1. Collections of hypotheses and representation conventions

Fix a collection $S$ of additional global axioms. We write $S;X\vdash q$
for derivability from local hypotheses $X$, as in [Calculus](Calculus.md).
The formula $\bot$ denotes falsity, and $q\preceq p$ means that $q$ is a
subformula of $p$, including the case $q=p$.

We speak of **collections of formulas** wherever their representation is
irrelevant. The notation $q\in X$ means that $q$ is available in $X$;
$X\subseteq Y$ means that every formula available in $X$ is available in
$Y$; and $X\cup\{q\}$ means adjoining $q$. Order and repeated occurrences
play no role in these judgments. This notation can be read independently of
whether a finite collection is stored as a set, a finite set, or a list.
Finiteness is asserted explicitly when required; no finiteness is implicit
in the word “collection.” General contexts may be infinite and therefore
need not admit a finite-list representation.

**Note on the formal developments.** The results below follow the set-based
interface in `setconsistent.ml` and `SetConsistent.lean`. HOL Light also has
a list-based presentation in [`consistent.ml`](../consistent.ml). Its
consistency notion depends on the formulas occurring in the list; its
maximal-consistency notion additionally requires no repetitions. Those
representation conditions are not part of the mathematical notion adopted
here. This chapter does not give a parallel exposition of the list interface,
and there is no natural-language translation of
[`conjlist.ml`](../conjlist.ml): its iterated-conjunction machinery is not
needed for the arguments below. Any restriction to finitely many formulas,
subformulas, or subsentences will nevertheless be stated precisely.

## 2. Consistency

Define **consistency relative to $S$** by

$$
\operatorname{Con}_S(X)\iff S;X\nvdash\bot.
$$

Here $S;X\nvdash q$ is the assertion that there is no derivation of $q$
from the indicated axioms and hypotheses. This is a syntactic notion; it
is not defined by the existence of a satisfying model.

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `SETCONSISTENT`.

### 2.1 Contradictory conclusions and contradictory members

**Statements.** If $\operatorname{Con}_S(X)$, then for every formula $q$,

$$
\neg\bigl((S;X\vdash q)\land(S;X\vdash\neg q)\bigr),
\qquad
\neg\bigl(q\in X\land\neg q\in X\bigr).
$$

**Comment.** A consistent collection neither proves nor contains both sides
of a contradiction. It may contain neither; consistency alone does not
decide every formula.

**Proof.** Derivations of $q$ and $\neg q$ give $\bot$ by the contradiction
rule of the calculus, violating consistency. If both formulas are members
of $X$, hypothesis introduction gives the two forbidden derivations.
$\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `SETCONSISTENT_NC`,
`IN_SETCONSISTENT_NC`. Their statements use the classically equivalent
forms $(S;X\nvdash q)\lor(S;X\nvdash\neg q)$ and
$q\notin X\lor\neg q\notin X$.
The calculus rule used is `MLK_NC_ALT`.

### 2.2 Removing hypotheses preserves consistency

**Statement.**

$$
\operatorname{Con}_S(X),\quad Y\subseteq X
\quad\Longrightarrow\quad\operatorname{Con}_S(Y).
$$

**Proof.** If $S;Y\vdash\bot$, weakening along $Y\subseteq X$ gives
$S;X\vdash\bot$, contrary to consistency of $X$. $\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `SETCONSISTENT_SUBSET`, using
hypothesis weakening (`MODPROVES_MONO2` in the calculus).

### 2.3 Consistency of a single hypothesis

**Statement.** For every formula $q$,

$$
\operatorname{Con}_S(\{q\})\iff S;\varnothing\nvdash\neg q.
$$

**Proof.** The deduction theorem and the defining equivalence for negation
give

$$
S;\{q\}\vdash\bot
\quad\Longleftrightarrow\quad
S;\varnothing\vdash q\to\bot
\quad\Longleftrightarrow\quad
S;\varnothing\vdash\neg q.
$$

Negate both ends of this equivalence. $\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `SETCONSISTENT_SING`.
The proof uses `MODPROVES_DEDUCTION_LEMMA` and `MLK_not_def` from the calculus.

### 2.4 One of the two possible extensions is consistent

**Statement.** For every formula $q$,

$$
\operatorname{Con}_S(X)\Longrightarrow
\bigl(\operatorname{Con}_S(X\cup\{q\})\lor
      \operatorname{Con}_S(X\cup\{\neg q\})\bigr).
$$

**Comment.** This is the step used to decide formulas while constructing a
maximal consistent extension. It asserts existence of a consistent choice,
not an algorithm for determining which choice works.

**Proof.** Suppose both extensions are inconsistent. From
$S;X\cup\{q\}\vdash\bot$, the deduction theorem gives
$S;X\vdash q\to\bot$, hence $S;X\vdash\neg q$. Inconsistency of the
other extension similarly gives $S;X\vdash\neg q\to\bot$. Modus ponens
now yields $S;X\vdash\bot$, contradicting consistency of $X$.
Thus at least one extension is consistent. $\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `SETCONSISTENT_EXTEND_CASES`.
The proof above follows Lean. HOL Light combines the two discharged
implications by disjunction elimination and applies excluded middle; both
arguments use the same deduction and classical reasoning principles.

## 3. Maximal consistency relative to a formula

Fix a distinguished formula $p$. Define

$$
\operatorname{Max}_S(p,X)\iff
\operatorname{Con}_S(X)\ \land\
\forall q\preceq p,\ (q\in X\lor\neg q\in X).
$$

Thus $X$ is **maximally consistent relative to $p$** when it is consistent
and decides every subformula of $p$.

**Important qualification.** This definition does not say that $X$ is
inclusion-maximal among all consistent collections of arbitrary formulas.
It imposes neither finiteness nor a restriction on which formulas may occur
in $X$. Later extension results impose such restrictions separately. In
particular, “maximal” in this chapter always refers to the displayed
subformula-decision property.

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `MAXIMAL_SETCONSISTENT`.

### 3.1 Consistency and decisions

**Statements.**

$$
\operatorname{Max}_S(p,X)\Longrightarrow\operatorname{Con}_S(X),
$$

$$
\operatorname{Max}_S(p,X),\quad q\preceq p
\quad\Longrightarrow\quad q\in X\lor\neg q\in X.
$$

Together with consistency, the second statement says that **exactly one**
of $q,\neg q$ belongs to $X$, for each $q\preceq p$.

**Proof.** The two implications are the two defining clauses of maximal
consistency. Section 2.1 excludes simultaneous membership, giving the
exactly-one assertion. $\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean):
`MAXIMAL_SETCONSISTENT_IMP_SETCONSISTENT`, `IN_MAXIMAL_SETCONSISTENT_CASES`.
The exactly-one assertion combines the latter with `IN_SETCONSISTENT_NC`;
it is not a separate declaration here.

## 4. Subsentences and the finite collection of relevant formulas

A **subsentence** of $p$ is a subformula of $p$ or the negation of one.
Write $q\preceq_s p$ for this relation and

$$
\operatorname{Sub}(p)=\{q:q\preceq p\},\qquad
\operatorname{Sent}(p)=\{q:q\preceq_s p\}.
$$

Only one additional negation is introduced by this definition. It is not
closure under arbitrary iterated negation, though some further negations
may already occur as subformulas of $p$.

**Formalization references.** [HOL Light](../setconsistent.ml):
`SUBSENTENCE`, introduced by `SUBSENTENCE_RULES`, with generated induction
and cases principles `SUBSENTENCE_INDUCT`, `SUBSENTENCE_CASES`.
[Lean](../lean/HOLMS/SetConsistent.lean): `Subsentence`, whose constructors
are `Subsentence.ofSubformula` and `Subsentence.negOfSubformula`.

### 4.1 Introducing subsentences

**Statements.**

$$
q\preceq p\Longrightarrow q\preceq_s p,\qquad
q\preceq p\Longrightarrow\neg q\preceq_s p.
$$

**Proof.** Apply, respectively, the subformula clause or the
negated-subformula clause of the definition. $\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `SUBFORMULA_IMP_SUBSENTENCE`,
`SUBFORMULA_IMP_NEG_SUBSENTENCE`.

### 4.2 Characterization of all subsentences

**Statement.**

$$
\operatorname{Sent}(p)=
\operatorname{Sub}(p)\cup\{\neg q:q\in\operatorname{Sub}(p)\}.
$$

**Proof.** A subsentence is introduced by one of the two defining clauses,
so it belongs to the corresponding part of the union. Conversely, a member
of either part is a subsentence by the corresponding introduction rule of
Section 4.1. The two collections therefore have exactly the same members.
$\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `SUBSENTENCE_EQ_SUBFORMULA`.

### 4.3 Finiteness of subsentences

**Statement.** For every formula $p$,

$$
|\operatorname{Sent}(p)|<\infty.
$$

**Proof.** A formula has finitely many subformulas, as proved in
[Modal](Modal.md). Applying negation to those formulas still produces only
finitely many formulas. Section 4.2 expresses the subsentences as the union
of these two finite collections. $\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `FINITE_SUBSENTENCE`.
The subformula result is `FINITE_SUBFORMULA` in HOL Light's `modal.ml` and
`Form.finite_subformulas` in Lean's `HOLMS/Modal.lean`.

## 5. Membership and derivability

### 5.1 Relevant formulas belong exactly when they are derivable

**Statements.** If $\operatorname{Max}_S(p,X)$ and $q\preceq p$, then

$$
q\in X\iff S;X\vdash q,
\qquad
\neg q\in X\iff S;X\vdash\neg q.
$$

**Comment.** The negated formula need not itself be a subformula of $p$:
the hypothesis in the second equivalence is still $q\preceq p$. Together
the two statements identify membership with derivability for all
subsentences of $p$. They do not assert deductive closure for arbitrary
formulas outside that collection.

**Proof.** Membership gives derivability by hypothesis introduction in both
cases. Conversely, suppose $S;X\vdash q$. Maximal consistency supplies
$q\in X$ or $\neg q\in X$. In the latter case, hypothesis introduction
gives $S;X\vdash\neg q$, contradicting consistency. Hence $q\in X$.
If instead $S;X\vdash\neg q$, the alternative $q\in X$ would give the
same contradiction, so $\neg q\in X$. $\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean):
`MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE`,
`MAXIMAL_SETCONSISTENT_NOT_SUBFORMULA_MEMBER_IFF_DERIVABLE`.

### 5.2 Consequences of a smaller context are retained

**Statement.**

$$
\operatorname{Max}_S(p,X),\quad A\subseteq X,\quad b\preceq p,\quad
S;A\vdash b
\quad\Longrightarrow\quad b\in X.
$$

**Comment.** This is the closure principle used to turn a derivation from
available hypotheses into membership in a prospective canonical world.

**Proof.** Weaken $S;A\vdash b$ along $A\subseteq X$ to obtain
$S;X\vdash b$. Since $b\preceq p$, Section 5.1 turns this derivation into
$b\in X$. $\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `MAXIMAL_SETCONSISTENT_LEMMA`.

## 6. Boolean membership laws

Throughout this section assume $\operatorname{Max}_S(p,X)$. When a compound
formula is a subformula of $p$, each of its immediate constituents is also
a subformula of $p$, by the subformula descent lemmas in [Modal](Modal.md).
This fact justifies each use of decisions and of Section 5.1 below.

These laws concern membership, not yet semantic satisfaction in a model.
They supply the propositional cases of the later canonical truth lemma.

### 6.1 Truth belongs when relevant

**Statement.**

$$
\top\preceq p\Longrightarrow\top\in X.
$$

**Proof.** Truth is derivable in any local context (`MLK_truth_th` in the
calculus). Since it is a subformula of $p$, Section 5.1 gives membership.
$\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean):
`MAXIMAL_SETCONSISTENT_TRUE_CLOSED`.

### 6.2 Negation complements membership

**Statement.**

$$
\neg q\preceq p\Longrightarrow
\bigl(\neg q\in X\iff q\notin X\bigr).
$$

**Proof.** Consistency excludes simultaneous membership of $q$ and
$\neg q$, giving the forward direction. For the converse, $q\preceq p$
follows from $\neg q\preceq p$. The decision property gives one of
$q,\neg q$ in $X$; if $q$ is absent, $\neg q$ must be present. $\square$

**Note.** The proof actually needs only $q\preceq p$, but both named
closure theorems retain the stronger premise $\neg q\preceq p$ displayed
here, matching the shape used in a truth-lemma induction.

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `MAXIMAL_SETCONSISTENT_NOT_CLOSED`.

### 6.3 Conjunction requires both conjuncts

**Statement.**

$$
(q\land r)\preceq p\Longrightarrow
\bigl((q\land r)\in X\iff(q\in X\land r\in X)\bigr).
$$

**Proof.** The compound formula and both constituents are subformulas of
$p$. Section 5.1 therefore converts their membership claims to derivability
claims. The conjunction rule (`MLK_and`) identifies derivability of
$q\land r$ with derivability of both $q$ and $r$: project in one direction,
and introduce conjunction in the other. Convert back to membership.
$\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean):
`MAXIMAL_SETCONSISTENT_AND_MIONOR_CLOSED` (retaining the source spelling
`MIONOR`).

### 6.4 Disjunction requires a disjunct

**Statement.**

$$
(q\lor r)\preceq p\Longrightarrow
\bigl((q\lor r)\in X\iff(q\in X\lor r\in X)\bigr).
$$

**Comment.** The forward implication uses the decisions made by maximal
consistency. It is not a disjunction property for arbitrary derivations in
the classical calculus.

**Proof.** Suppose $q\lor r\in X$ but neither $q$ nor $r$ belongs to $X$.
Since both are subformulas of $p$, the decision property supplies
$\neg q,\neg r\in X$. Hypothesis introduction and the derived negated-
disjunction rule (`MLK_proves_not_or`) give $S;X\vdash\neg(q\lor r)$.
But $S;X\vdash q\lor r$ by hypothesis introduction, contradicting
consistency. Thus one disjunct belongs.
Conversely, membership of either disjunct gives a derivation of it, and
then of $q\lor r$ by disjunction introduction. Section 5.1 gives membership
of the disjunction. $\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean):
`MAXIMAL_SETCONSISTENT_MINOR_OR_CLOSED`.

### 6.5 Implication preserves membership

**Statement.**

$$
(q\to r)\preceq p\Longrightarrow
\bigl((q\to r)\in X\iff(q\in X\Longrightarrow r\in X)\bigr).
$$

The implication on the right is an assertion about membership; the formula
on the left is a member of the modal language.

**Proof.** If $q\to r$ and $q$ belong to $X$, derive both by hypothesis
introduction and apply modus ponens. Section 5.1 gives $r\in X$.
Conversely, assume that membership of $q$ implies membership of $r$.
Decide $q$. If $q\in X$, then $r\in X$, so derive $r$ and add antecedent
$q$ to obtain $S;X\vdash q\to r$. If $\neg q\in X$, the calculus rule
for a false antecedent (`MLK_imp_introl`) also gives $S;X\vdash q\to r$.
Since the implication is a subformula, Section 5.1 yields its membership.
$\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `MAXIMAL_SETCONSISTENT_IMP_CLOSED`.

### 6.6 Equivalence means agreement of membership

**Statement.**

$$
(q\leftrightarrow r)\preceq p\Longrightarrow
\bigl((q\leftrightarrow r)\in X\iff(q\in X\Longleftrightarrow r\in X)\bigr).
$$

**Proof.** From membership of the biconditional, derive it and extract its
two implications. Modus ponens transports derivability of either side to
the other; Section 5.1 turns this into agreement of membership.

Conversely, assume $q$ and $r$ have the same membership status. If both
belong, derive them and use the rule that two derived formulas are provably
equivalent (`MLK_proves_iff_pos`). If neither belongs, their subformula
decisions give $\neg q,\neg r\in X$. Derive both negations and use the
corresponding negative rule (`MLK_proves_iff_neg`). In either case,
$S;X\vdash q\leftrightarrow r$; Section 5.1 gives the required membership.
The implication-membership law cannot simply be applied to $q\to r$ and
$r\to q$ here, since those formulas need not themselves be subformulas
of $p$. $\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `MAXIMAL_SETCONSISTENT_IFF_CLOSED`.

## 7. Finite maximal extensions

### 7.1 Extending a consistent collection of subsentences

**Statement.** Suppose

$$
\operatorname{Con}_S(X),\qquad |X|<\infty,\qquad
X\subseteq\operatorname{Sent}(p).
$$

Then there is a collection $M$ such that

$$
\operatorname{Max}_S(p,M),\qquad |M|<\infty,\qquad
M\subseteq\operatorname{Sent}(p),\qquad X\subseteq M.
$$

**Comment.** This is a finite extension theorem relative to $p$. Only the
finitely many subformulas of $p$ must be decided. Finiteness counts distinct
available formulas and does not select a representation or an ordering.
Both formal statements include $|X|<\infty$ explicitly, even though it
also follows from $X\subseteq\operatorname{Sent}(p)$ and Section 4.3.

**Proof.** Maintain a current collection $Y$ and a finite collection $U$
of subformulas still to be processed. The invariant is:

1. $Y$ is consistent, finite, and contains only subsentences of $p$.
2. Every subformula $q$ of $p$ is either in $U$ or already decided in $Y$:
   $q\in U$ or $q\in Y$ or $\neg q\in Y$.

We prove by induction on the finite collection $U$ that every $Y$ satisfying
this invariant has an extension $M$ with the required properties and
$Y\subseteq M$. The induction assertion quantifies over **all such current
collections $Y$**, so that it can be used after adding a formula.

If $U$ is empty, every subformula is already decided. Consistency of $Y$
therefore gives $\operatorname{Max}_S(p,Y)$, and take $M=Y$.

For the step, select $q\in U$ and put $U'=U\setminus\{q\}$.
Section 2.4 supplies a consistent choice

$$
Y'=Y\cup\{q\}\qquad\text{or}\qquad Y'=Y\cup\{\neg q\}.
$$

The extension is finite. The added formula is a subsentence because
$q\preceq p$; all previous members remain subsentences. Every subformula
other than $q$ that was pending remains in $U'$, and $q$ is now decided.
Previously made decisions remain present because $Y\subseteq Y'$.
Thus the invariant holds for $U',Y'$. Apply the induction hypothesis to
obtain $M$ extending $Y'$, hence also $Y$.

Start with $Y=X$ and $U=\operatorname{Sub}(p)$. The latter is finite,
and every subformula is initially pending, so the invariant holds. The
induction gives the desired $M$. $\square$

**Note on construction.** Choosing a consistent extension uses classical
reasoning. A finite number of choices does not, by itself, provide a
computable consistency test or a decision procedure for derivability.

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `EXTEND_MAXIMAL_SETCONSISTENT`.
HOL Light inducts on a finite set of pending subformulas; Lean uses a
`Finset` for that induction. Both maintain a context that changes during
the induction, with the invariant described above. No list-conjunction
lemma is required.

### 7.2 A maximal consistent collection containing the negation of a nontheorem

**Statement.** If $p$ is not derivable without local hypotheses, then

$$
S;\varnothing\nvdash p
\quad\Longrightarrow\quad
\exists M,\quad\operatorname{Max}_S(p,M)\ \land\ \neg p\in M
\ \land\ M\subseteq\operatorname{Sent}(p).
$$

**Comment.** This supplies the prospective canonical world that will falsify
$p$ in a later countermodel construction. The collection is nonempty because
it contains $\neg p$. It is also finite, since it is contained in the finite
collection of subsentences, although the named theorem does not list
finiteness as a separate conjunct.

**Proof.** First $\{\neg p\}$ is consistent. Otherwise the singleton
characterization of Section 2.3 gives
$S;\varnothing\vdash\neg\neg p$, and double-negation elimination gives
$S;\varnothing\vdash p$, contrary to the premise. The singleton is finite,
and its member is a subsentence of $p$ because $p\preceq p$.
Apply Section 7.1 to $X=\{\neg p\}$. The resulting $M$ is maximally
consistent relative to $p$, contains only subsentences, and contains
$\neg p$ because it extends the singleton. $\square$

**Formalization references.** [HOL Light](../setconsistent.ml) and
[Lean](../lean/HOLMS/SetConsistent.lean): `NONEMPTY_MAXIMAL_SETCONSISTENT`.

## 8. Role in the wider development

Consistency prevents contradictory information, while decisions on the
subformulas of a fixed formula turn relevant derivability into membership.
The Boolean membership laws make these collections suitable candidates for
canonical worlds. Finite maximal extension supplies such a world containing
the negation of a nontheorem. The later completeness development must still
define accessibility and prove the modal part of the truth lemma; the
present results provide its propositional and extension infrastructure.
