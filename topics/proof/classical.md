# Classical Logic and Proof


This section contains a brief overview of how Mathematical propositions are
stated and proved using classical logic. We will see later that this is not the
only foundational theory of logic and proof.

In fact, classical logic is not well suited to propositions and proof in a
computational context (we will see why later). Alternative foudational theories
are used (Martin-Löf type theory, calculus of constructions) when creating type
theories concerning propositions and proof (for example dependent types).


## Statements

A _statement_ is something that can be clearly interpreted as being true or
false.

Examples:

1. 1 + 1 = 2
2. The square root of 2 is irrational
3. There are a finite number of primes

Here 1. and 2. are true, 3. is false.


## Predicates

A _predicate_ is a statement involving a symbol that is true or false when we
substitute the symbol with an element of a set. For example:

> The natural number `x` is less than `10`.

Let's call the predicate `P(x)` then `P(9)` is true and `P(10)` is false. We
have constructed a _truth function_ from the set of natural numbers, ℕ, to the
set of Booleans, `B = {t, f}`.

> `T : ℕ -> B` where `T(n) = t` if `P(n)` is true and `T(n) = f` if `P(n)` is false

NB: This is not well suited to a computational context because for a general
predicate involving natural numbers we'd have to compute an infinite number of
values to know the truth function.


## Quantifiers

We can make statements that _quantify over_ a predicate.

Let `S` be a subset of `X` (the domain of definition of the predicate). Then we
can for the following statements.

> for all `x ∈ S`, `P(x)` is true
>
> for some `x ∈ S`, `P(x)` is true

The mathematical symbols used are the _universal quantifier_ ∀ for the first and
the _existential quanitifier_ ∃ for the second.

> `∀ x ∈ S: P(x)`
>
> `∃ x ∈ S: P(x)`

Examples:

1. `∀ n ∈ ℕ: ` `n` is even.
2. `∃ n ∈ ℕ: ` `n` is even.

The first is false the second is true.


## Conjunctions

_Conjunctions_ are used to combine existing statements. The regular conjunctions
we use are _and_, _or_, _imples_, _if and only if_ denoted ∧, ∨, ⇒, ⇔.

Their meaning can be given using a _truth table_ which is a way to write down
the truth function for the conjunction.

### And, ∧

| P | Q | P ∧ Q |
|---|---|-------|
| t | t | t     |
| t | f | f     |
| f | t | f     |
| f | f | f     |

### Or, ∨

| P | Q | P ∨ Q |
|---|---|-------|
| t | t | t     |
| t | f | t     |
| f | t | t     |
| f | f | f     |

### Imples, ⇒

| P | Q | P ⇒ Q |
|---|---|-------|
| t | t | t     |
| t | f | f     |
| f | t | t     |
| f | f | t     |

### Imples, ⇔ 

| P | Q | P ⇔ Q |
|---|---|-------|
| t | t | t     |
| t | f | f     |
| f | t | f     |
| f | f | t     |
