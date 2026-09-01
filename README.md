# Interaction Arrows in Agda

[![Proof Check](https://github.com/tgrospic/interaction-arrows-agda/actions/workflows/agda.yml/badge.svg)](https://github.com/tgrospic/interaction-arrows-agda/actions/workflows/agda.yml)

A small executable account of game semantics, built to make one claim precise: for many programs the right *denotation* is a strategy, not a function, and the ordinary function is recovered from it by observation.

```text
strategy : A -i> B
             |
             | observe
             v
function : ⟦ A ⟧ → ⟦ B ⟧
```

The arrow `-i>` is defined independently, as a space of strategies. `→` is derived from it. That direction is the whole point, and it is why `A -i> B` is not an Agda function bundled with extra interaction data.

## The point

An extensional morphism cares only about the observable mapping from inputs to outputs. The meaning of `f : A → B` is settled by asking, for each `a : A`, which `b : B` comes out. So if `∀ a. f a ≡ g a` then `f` and `g` are the same morphism, however differently they communicate, evaluate, schedule, or cause internally.

An interaction morphism `f : A -i> B` can separate two computations whose input-output mapping is identical, because the interaction itself is part of the semantic object.

```text
extensional   =  what result
interaction   =  what result + the structure of obtaining it
```

Collapsing `A -i> B` to `A → B` forgets exactly what does not survive into the input-output relation.

## Where `-i>` comes from

Every definition in this section appears twice: on the left as it is given in the source, on the right as it appears here. The sources are Abramsky's [*Semantics of Interaction*](https://arxiv.org/abs/1312.0121) §1, and Abramsky, Jagadeesan and Malacaria's [*Full Abstraction for PCF*](https://arxiv.org/abs/1311.6125) §4.1, cited below as AJM after its three authors, the way the game semantics literature does to tell it apart from the Hyland and Ong model.

### Games

**Semantics of Interaction §1.** A game is a triple, with Opponent moving first:

$$G = (M_G, \lambda_G, P_G)$$

$$\lambda_G : M_G \to \lbrace P, O \rbrace \qquad P_G \subseteq M_G^{\mathrm{alt}} \text{ non-empty and prefix-closed}$$

$$M_G^{\mathrm{alt}} = \lbrace s \in M_G^{*} \mid \forall i. \mathrm{even}(i) \Rightarrow \lambda_G(s_i) = P \wedge \mathrm{odd}(i) \Rightarrow \lambda_G(s_i) = O \rbrace$$

He justifies two players rather than one on the grounds that the second player *is* the environment, so interaction is represented intrinsically: one-person games would degenerate to transition systems, where interaction has to be added through extra structure on the labels.

**`src/Arena.agda`.** An arena is built rather than described, so that both sides are visible in the type:

```agda
data Arena : Set₁ where
  val : Game → Arena           -- only Opponent asks
  _^⊥ : Arena → Arena          -- role reversal
  _⊗_ : Arena → Arena → Arena  -- disjoint parallel composition
```

`OQ`/`OA` give the questions Opponent may ask and the answers Player owes; `PQ`/`PA` give the reverse. A `Game` from `src/Game.agda` is the degenerate case where only Opponent asks, embedded by `val`, and its values are the complete answers to those questions.

### Strategies

**Semantics of Interaction §1.** A deterministic strategy on $G$ is a non-empty $\sigma \subseteq P_G^{\mathrm{even}}$ with

$$(s1) \varepsilon \in \sigma \qquad (s2) sab \in \sigma \Rightarrow s \in \sigma \qquad (s3) sab, sac \in \sigma \Rightarrow b = c$$

(s1) and (s2) make $\sigma$ a subtree of even-length paths, (s3) is determinacy. He reads $sab \in \sigma$ as "in context $s$, respond to stimulus $a$ with $b$", generalizing the single-valuedness of a partial function's graph, and summarizes strategies as partial functions extended in time.

**`src/Strategy.agda`.** A dialogue over one arena, and a strategy as one dialogue per question Opponent may ask:

```agda
data Tree (G : Arena) (X : Set) : Set where
  return : X → Tree G X
  ask    : (q : PQ G) → (PA G q → Tree G X) → Tree G X
```

```agda
record Strategy (G : Arena) : Set where
  field
    respond : (q : OQ G) → Tree G (OA G q)
```

Because `ask` stores a *function* on answers, (s3) cannot be violated: there is exactly one continuation per answer. (s1) and (s2) hold for any inductive tree. A side condition on a set of plays becomes a typing discipline. A reader with Haskell reflexes will object that this is just the free monad on a container, and that is right: `PQ`/`PA` is a container and `_>>=_` is its substitution. Nothing in the datatype is new. What game semantics adds is taking it as the *hom-set* of a category.

### Linear implication, and the arrow

**Semantics of Interaction §1.** Like the tensor, but with polarity inverted on the left:

$$M_{A \multimap B} = M_A + M_B \qquad \lambda_{A \multimap B} = [ \overline{\lambda_A}, \lambda_B ]$$

$$\overline{\lambda_A}(m) = P \text{ if } \lambda_A(m) = O, \qquad \overline{\lambda_A}(m) = O \text{ if } \lambda_A(m) = P$$

$$P_{A \multimap B} = \lbrace s \in M_{A \multimap B}^{\mathrm{alt}} \mid s \upharpoonright M_A \in P_A \wedge s \upharpoonright M_B \in P_B \rbrace$$

The justification is the function box: on the output side the System produces and the Environment consumes, and those roles reverse on the input side. He then derives the consequence that shapes the code: **the first move of any play in $A \multimap B$ must be in $B$**, since Opponent moves first while every opening move of $A$ is labelled $P$ after inversion.

**`src/Arena.agda` and `src/InteractionArrow.agda`.** Linear implication is that construction, and the arrow is strategies on it:

```agda
_⊸_ : Arena → Arena → Arena
A ⊸ B = (A ^⊥) ⊗ B
```

```agda
_-i>_ : Arena → Arena → Set
A -i> B = Strategy (A ⊸ B)
```

Since `⊸` is an operation on arenas, higher-order arenas such as `(A ⊸ B) ⊸ C` are ordinary types here, and `OQ (A ⊸ B)` computes to `PQ A ⊎ OQ B`: play opens in `B`, exactly as the inversion requires.

### Composition: parallel composition plus hiding

**Semantics of Interaction §1.** The category $\mathcal{G}$ has games as objects, strategies on $A \multimap B$ as morphisms $A \to B$, and composition given by interaction:

$$\sigma \parallel \tau = \lbrace s \in (M_A + M_B + M_C)^{*} \mid s \upharpoonright A,B \in \sigma \wedge s \upharpoonright B,C \in \tau \rbrace$$

$$\sigma ; \tau = (\sigma \parallel \tau)/B = \lbrace s \upharpoonright A,C \mid s \in \sigma \parallel \tau \rbrace$$

The internal $B$ dialogue happens in $\sigma \parallel \tau$ and the restriction $/B$ throws it away.

**`src/InteractionArrow.agda`.** Substitution instead of restriction:

```agda
interact A B C (return x)       σ = return x
interact A B C (ask (inj₁ b) k) σ =
  shift A B C (respond σ (inj₂ b)) >>= λ r → interact A B C (k r) σ
interact A B C (ask (inj₂ c) k) σ = ask (inj₂ c) (λ r → interact A B C (k r) σ)
```

This is why `hide = interact` here. In the trace presentation hiding is a real operation, because $\sigma \parallel \tau$ genuinely contains the $B$ moves. In the tree presentation the result type is `Tree (A ⊸ C) X`, so there is nowhere for a middle move to sit and substitution has already consumed them. Hiding is definitional rather than a second step; the two names are kept because the literature separates the two ideas.

Composition keeps the outer arenas general and restricts the middle one to a game:

```agda
_∘i_ : ∀ {A C} {B : Game} → (val B -i> C) → (A -i> val B) → (A -i> C)
```

That restriction is deliberate and is discussed under the limits below. `left-id`, `right-id` and `assoc` are proved against it, the last through two lemmas about how environments nest through composition.

### Copycat

**Semantics of Interaction §1, Example 1.2.**

$$\mathrm{id}_A = \lbrace s \in P^{\mathrm{even}}_{A_1 \multimap A_2} \mid \forall t \text{ an even-length prefix of } s. t \upharpoonright A_1 = t \upharpoonright A_2 \rbrace$$

**`src/InteractionArrow.agda`.** Two-sided, because after the inversion either side may be asked:

```agda
id-i : ∀ {A} → A -i> A
respond id-i (inj₁ p) = ask (inj₂ p) return
respond id-i (inj₂ o) = ask (inj₁ o) return
```

Whichever side the question arrives on, copy it across and hand back the answer.

### The boolean game, and `Bool⊥`

**Semantics of Interaction §1, Example 1.1.** One opening request, two possible responses:

$$B = (\lbrace *, tt, ff \rbrace, \lbrace * \mapsto O, tt \mapsto P, ff \mapsto P \rbrace, \lbrace \varepsilon, *, *tt, *ff \rbrace)$$

Its strategies are exactly $\lbrace \varepsilon \rbrace$, $\mathrm{Pref}\lbrace *tt \rbrace$ and $\mathrm{Pref}\lbrace *ff \rbrace$, which under inclusion form the flat domain of booleans with $\bot$ below $tt$ and $ff$.

**`src/BoolExample.agda`.**

```agda
Bool⊥ : Set
Bool⊥ = Maybe Bool
```

`Bool⊥` is not a lifting invented for the parallel-or argument. It is that three-element strategy space, and `Maybe Bool` is literally it: `nothing` is the strategy that never answers, `just b` the two that do. That also answers the objection that Agda is total, so this `⊥` must be smuggled divergence: a value goes missing exactly when the context declines to supply it, which is the same notion of divergence `_≈obs_` is built on.

## Why `A → B` is not enough

The convincing case is parallel-or, written `por` below, because it breaks the ordinary arrow inside a pure functional language, with no appeal to networking or effects.

Take lifted booleans, where `⊥` means nontermination, and the perfectly respectable Scott-continuous function over them (`src/BoolExample.agda`):

```agda
Bool⊥ : Set
Bool⊥ = Maybe Bool

por : Bool⊥ × Bool⊥ → Bool⊥
por (just true  , _)           = just true
por (_          , just true)   = just true
por (just false , just false)  = just false
por (_          , _)           = nothing
```

No sequential program implements it. Any sequential program must inspect one argument first: inspect the left and `por (⊥ , true⊥)` diverges before reaching the `true⊥` on the right; inspect the right and `por (true⊥ , ⊥)` diverges symmetrically. The proof in the repo is that case analysis, over the same `BoolStrategy` trees the AND example uses, with divergence supplied by a context that declines:

```agda
no-sequential-por : ¬ (Σ BoolStrategy (λ s → Realizes s por))
no-sequential-por (return b , realizes) = no-return-por b realizes
no-sequential-por (ask (inj₁ left)  k , realizes) with realizes (nothing , just true)
... | ()
no-sequential-por (ask (inj₁ right) k , realizes) with realizes (just true , nothing)
... | ()
no-sequential-por (ask (inj₂ ()) k , realizes)
```

The careful reader will conclude from this that `-i>` simply has more morphisms than `→`, and this is the easiest step to slip on. The collapse

$$\Large \mathrm{ext} : (A \mathbin{\text{-i>}} B) \longrightarrow ([[A]] \to [[B]])$$

fails to be injective *and* fails to be surjective, and the two failures are separate results:

| | What fails | Proved by |
| --- | --- | --- |
| Not injective | `andLR` and `andRL` differ as trees, agree as functions | `src/Audit.agda` |
| Not surjective | `por` is a function with no sequential strategy | `no-sequential-por` in `src/BoolExample.agda` |

So `A → B` is at once too **coarse**, identifying computations that differ, and too **large**, containing functions no sequential program realizes. `ExtensionalArrow` in `src/Extensional.agda` carries realizability as an explicit witness for exactly this reason.

The important part is where the defect sits:

> `A → B` tells you which output depends on which completed input. It does not tell you how the computation is allowed to acquire that input.

The type `por : Bool⊥ × Bool⊥ → Bool⊥` is already correct. It is the *arrow* that is too weak. The extensional hom-set offers all suitable functions, while the language realizes only some of them. Making the hom-set strategies puts the legal pattern of asking and answering inside the morphism, so a sequential and a parallel-or differ as morphisms rather than only in commentary about them.

The same gap opens at higher order. Extensionally, the argument of `f : (A → B) → C` is a completed function, a finished table. A real program interacts with that argument: ask at `a₁`, receive `b₁`, choose `a₂` in light of `b₁`, and so on, then produce `c`. That dialogue is what game semantics denotes, and because `⊸` is an operation on arenas it is an ordinary type here: `(A ⊸ B) ⊸ C` is the arena whose plays are that exchange.

The first objection is always to widen the domain, `(A × State × History × …) → B`, and be done. Abramsky answers it twice in [*Semantics of Interaction*](https://arxiv.org/abs/1312.0121) §1. Once about models in general, where games "provide an explicit representation of the environment, and hence model interaction in an intrinsic fashion", while a labelled transition system has to model it "using some additional structure, typically a *synchronization algebra* on the labels". Widening the domain is that additional structure, relocated into the type. And once about functions in particular: reading `sab ∈ σ` as a generalized graph, he notes that ordinary relations "describe a single stimulus-response event only", whereas strategies "describe repeated interactions between the System and the Environment". Currying gives you a bigger single event, not repeated interaction.

Parallel-or is where the difference bites: nothing is missing from the *data*, only permission to look at the second argument before the first has answered. Widening the domain has a further tell. You immediately need a side condition saying which histories are legal, and that condition is the game you were avoiding.

## Why this is denotational, not operational

This is the objection worth answering directly, because dialogue, interaction and hiding all sound like process calculus. They are not used that way here.

**There is no transition relation.** Nothing in the development has the shape `_⟶_ : Config → Config → Set`, no scheduler, no step index, no fuel, no state threaded through anything. The single trace-shaped definition, `Legal : List (Move G) → Set` in `src/Game.agda`, is not used by any other module.

**A strategy is a value, not a run.** `Tree` is an ordinary inductive type. Its `ask` node stores a *function* `Answer A q → Tree A X`, the entire family of responses at once, not one step of one execution. A strategy is a finished mathematical object that happens to have branching structure, in the same way a power series is a finished object with coefficient structure.

**Observation is a fold, not an interpreter.** `run` is structurally recursive and total:

```agda
run : ∀ {G X} → Tree G X → Env G → X
run (return x) ρ = x
run (ask q k)  ρ = run (k (ρ q)) ρ
```

It consumes a complete environment `ρ : ⟦ A ⟧`, so there is nothing to wait for and no order in which things happen. It is the unique homomorphism from the tree into the value.

**Composition is substitution, not sequencing.** `g ∘i f` does not mean "run `f`, then run `g`". Each question `g` would have asked of `B` is replaced by the tree `f` supplies, using the bind on trees:

```agda
_>>=_ : ∀ {G X Y} → Tree G X → (X → Tree G Y) → Tree G Y
return x >>= k = k x
ask q c  >>= k = ask q (λ a → c a >>= k)
```

That is a structural operation on meanings. Correspondingly, the category laws are proved by induction on the tree, never by simulating executions:

```agda
run-bind : ∀ {G X Y} (t : Tree G X) (k : X → Tree G Y) ρ →
           run (t >>= k) ρ ≡ run (k (run t ρ)) ρ
run-bind (return x) k ρ = refl
run-bind (ask q c)  k ρ = run-bind (c (ρ q)) k ρ
```

**The collapse is a homomorphism.** `ext` is not an evaluator either; it is the map from the richer meaning to the poorer one, and it commutes with the structure on both sides (`src/Extensional.agda`):

```agda
ext-id : ∀ {A : Game} → ext {A} {A} id-i ≗ (λ x → x)
```

```agda
ext-compose : ∀ {A B C : Game} (g : val B -i> val C) (f : val A -i> val B) →
  ∀ ρ q → ext {A} {C} (g ∘i f) ρ q ≡ ext {B} {C} g (ext {A} {B} f ρ) q
```

Two categories of meanings, and a functor between them. That is a denotational design carried out between two semantic levels, with the richer level on top. It is not an operational model of the poorer one. At which point the natural reply is to quotient by observation and call the functions the real meaning. [AJM](https://arxiv.org/abs/1311.6125) do exactly that, and it repays following what they get. §4.1 defines the intrinsic preorder by testing against the Sierpinski game $\Sigma$, which has one question and one possible answer: $x \lesssim_A y$ iff $x;\alpha \sqsubseteq y;\alpha$ for every $\alpha : A \to \Sigma$. The lemmas after it establish that this preorder is pointwise at each type constructor, so the quotient really is extensional. §4.3 then presents the quotient concretely: $D(A)$ is the poset of strategies modulo the induced equivalence, and a morphism $A \to_E B$ is a monotone function $D(A) \to D(B)$ that coincides with $D(\sigma)$ for some strategy $\sigma$, a function "sequentially realised" by $\sigma$ in their phrase. That clause is the whole answer to the objection: quotienting collapses intensional distinctions without ever enlarging the hom-set, so the functions in the extensional model are exactly those some strategy realizes. Theorem 4.15 then proves that model fully abstract for PCF, with Milner's Context Lemma dropping out as a corollary rather than being assumed. `por` realizes nothing and is not among its morphisms.

**The interaction is closed, not performed.** Even the derivation of an ordinary function from a strategy is equational rather than procedural. A value becomes a strategy from the empty game, and observation closes the dialogue:

```agda
I : Game
Question I = ⊥
Answer I = ⊥-elim

quote-value : ∀ {A : Game} → ⟦ A ⟧ → val I -i> val A

observe : ∀ {B : Game} → val I -i> val B → ⟦ B ⟧

ext-via-closure : ∀ {A B : Game} (f : val A -i> val B) (a : ⟦ A ⟧) →
  ∀ q → observe {B} (f ∘i quote-value a) q ≡ ext {A} {B} f a q
```

`observe (f ∘i quote-value a)` is the meaning of a closed system, obtained by composing meanings. Nothing is stepped.

## Modules

- `src/Game.agda` is the one-round question/answer arena used as an object of values.
- `src/Arena.agda` builds arenas: `val`, role reversal `^⊥`, tensor `⊗`, and linear implication `⊸`, with `OQ`/`OA` and `PQ`/`PA` reading off each side.
- `src/Strategy.agda` defines dialogue trees over an arena, their total and partial interpretations, strategies, extensional equality, and the contextual equivalence the category is built on.
- `src/InteractionArrow.agda` defines `A -i> B = Strategy (A ⊸ B)`, copycat, interaction, hiding, composition, and the category laws.
- `src/Extensional.agda` derives `ext`, closes strategies with quoted values, and records which ordinary functions are strategy-realizable.
- `src/BoolExample.agda` gives two AND strategies that query their inputs in opposite orders but compute the same Boolean function, and proves that no sequential dialogue tree realizes parallel-or.
- `src/Concurrent.agda` replaces a total schedule with a partial order, so independent events stay unordered while both cause a later event.
- `src/Category.agda` bundles the interaction category and observation functor as records: hom-setoids, identity, composition, congruence and the laws in `SetoidCategory`, and `ext` with its laws in `SetoidFunctor`.
- `src/Audit.agda` separates the three relations: `_≡_` tells the two AND dialogue trees apart, `_≈ext_` identifies the strategies built from them, and `_≈obs_` tells them apart again.

## The equivalence the category is built on

**AJM §4.1** define the *intrinsic preorder* by testing against the Sierpinski game $\Sigma$, which has one question and one possible answer:

$$\Sigma = (\lbrace q, a \rbrace, \lbrace q \mapsto OQ, a \mapsto PA \rbrace, \lbrace \varepsilon, q, qa \rbrace)$$

$$x \lesssim_A y \iff \forall \alpha : A \to \Sigma. x ; \alpha \sqsubseteq y ; \alpha \iff \forall \alpha : A \to \Sigma. (x ; \alpha)\downarrow \Rightarrow (y ; \alpha)\downarrow$$

A strategy is compared with another by what every test can observe of it, and the extensional model is the quotient by the induced equivalence.

**`src/Strategy.agda`** tests against contexts that may decline to answer:

```agda
PEnv : Arena → Set
PEnv G = (q : PQ G) → Maybe (PA G q)
```

```agda
σ ≈obs τ = ∀ q ρ → runP (respond σ q) ρ ≡ runP (respond τ q) ρ
```

The declining is the point. With total environments every context is itself extensional and observes nothing beyond the induced function, so the relation would collapse. Declining is this development's stand-in for $(x;\alpha)\downarrow$: a context that refuses one question observes whether a strategy needed it.

Extensional equality is kept under its own name and derived, so the two orders of observation are related rather than confused:

```agda
≈obs⇒≈ext : ∀ {G} {σ τ : Strategy G} → σ ≈obs τ → σ ≈ext τ
```

`left-id`, `right-id` and `assoc` are proved at `_≈obs_`, and their `_≈ext_` forms follow from that one lemma.

## What this code does and does not establish

It establishes that `-i>` is a category whose hom-relation is contextual, that `ext` preserves identity and composition, that two dialogue trees with different query orders induce the same Boolean function while remaining distinguishable by a context, and that no dialogue tree realizes parallel-or, proved against `runP`, the same interpreter the hom-relation uses.

"Category" and "functor" name checked records rather than three standalone equations. `src/Category.agda` instantiates

```agda
interaction : SetoidCategory Game
```

with `StrategySetoid (val A ⊸ val B)` as its hom-setoids, so identity, composition, the three laws, and

```agda
∘i-cong : ∀ {A C} {B : Game} {g g′ : val B -i> C} {f f′ : A -i> val B} →
          g ≈obs g′ → f ≈obs f′ → g ∘i f ≈obs g′ ∘i f′
```

are all fields that had to be supplied. Objects are games because composition needs a value arena in the middle; the arenas on either side stay arbitrary. Observation is then

```agda
observation : SetoidFunctor interaction
```

carrying `ext` together with its congruence, identity and composition laws. Its target is written out as functions between game values compared pointwise, rather than bundled as a second category, because composition of functions respects pointwise equality only given extensionality, which this development does not assume.

The distinguishing context is explicit. It answers the right input and declines the left:

```agda
right-only : PEnv (val Inputs ⊸ val Output)
right-only = flat-context (nothing , just false)
```

```agda
andLR-i≈ext-andRL-i : andLR-i ≈ext andRL-i
andLR-i≉andRL-i : ¬ (andLR-i ≈obs andRL-i)
```

Query order is therefore visible inside the equational theory, not only in `_≡_` on syntax.

Limits worth stating plainly, since they are where the development would have to grow next:

- Receptivity is never stated. Determinism and prefix closure hold structurally, because `ask` stores a function on answers, but nothing requires a strategy to accept every legal question.
- Composition restricts the middle arena to a game:

  ```agda
  _∘i_ : ∀ {A C} {B : Game} → (val B -i> C) → (A -i> val B) → (A -i> C)
  ```

  The outer arenas stay general, so higher-order arenas compose on the outside. With a general arena in the middle the two strategies can question each other back and forth across it, and the recursion stops being structural. That is the infinite chattering problem, and showing $\sigma;\tau$ total in its presence is a development of its own, which *Semantics of Interaction* §2 gives a section to. The restriction states that limit in the type rather than postulating past it.
- `Move`, `polarity` and `Legal` in `src/Game.agda` are defined but unused: legality is carried by the arena's two sides rather than by a predicate on plays.

`src/Concurrent.agda` is likewise only a gesture at its source. [Abramsky and Melliès](https://www.cs.ox.ac.uk/people/samson.abramsky/cg.pdf) replace plays-as-sequences with a domain of *positions*, ordered by "reachable by playing further moves", and take a strategy to be a continuous closure operator on that domain, with composition given by composing closure operators. Our module builds the partial order and exhibits two independent events with a common cause; it does not yet carry strategies over it.

## Background

Game semantics is the line of work that made "the morphism is a strategy" precise, and Abramsky is its central figure.

Plotkin posed the problem in 1977, showing that the continuous function model of PCF contains parallel-or, which the language cannot define. Milner framed the matching question that same year: a model whose equalities are exactly observational equivalence.

- G. Plotkin, *LCF considered as a programming language*, Theoretical Computer Science 5 (1977), 223–255. [PDF](https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf)
- R. Milner, *Fully abstract models of typed lambda-calculi*, Theoretical Computer Science 4 (1977), 1–22. [DOI](https://doi.org/10.1016/0304-3975%2877%2990053-6)

The problem stood for roughly two decades, then was solved twice at once, by games. Abramsky, Jagadeesan and Malacaria interpret types as games and terms as history-free strategies, introduce an intrinsic preorder on strategies, and obtain an order-extensional fully abstract model by quotienting the intensional one. Hyland and Ong, and independently Nickau, use innocent strategies over arenas with explicit justification. Both identify the *sequentially realizable* part of the function space, which is exactly why parallel-or is absent from it.

- S. Abramsky, R. Jagadeesan, P. Malacaria, *Full Abstraction for PCF*, Information and Computation 163 (2000), 409–470. [arXiv](https://arxiv.org/abs/1311.6125)
- J. M. E. Hyland, C.-H. L. Ong, *On Full Abstraction for PCF: I, II, and III*, Information and Computation 163 (2000), 285–408. [ORA](https://ora.ox.ac.uk/objects/uuid:63c54392-39f3-46f1-8a68-e6ff0ec90218)

The Interaction Categories program is the structural reading of the same idea, and the one closest in spirit to denotational design: specifications as objects, processes as morphisms, interaction as composition.

- S. Abramsky, S. J. Gay, R. Nagarajan, *Interaction Categories and the Foundations of Typed Concurrent Programming*, Marktoberdorf 1994. [PostScript](https://www.cs.ox.ac.uk/people/samson.abramsky/agn2.ps)
- S. Abramsky, R. Jagadeesan, *Games and Full Completeness for Multiplicative Linear Logic*, Journal of Symbolic Logic 59 (1994), 543–574. [arXiv](https://arxiv.org/abs/1311.6057)

Then the self-correction that matters for the concurrency axis. Sequential game models take a play to be a *sequence* of moves, which imposes a global schedule and orders events that causality never related. Abramsky and Melliès replace plays with closure operators over partial orders and prove full completeness for multiplicative-additive linear logic. `src/Concurrent.agda` is the toy version of that move.

- S. Abramsky, P.-A. Melliès, *Concurrent Games and Full Completeness*, LICS 1999, 431–442. [PDF](https://www.cs.ox.ac.uk/people/samson.abramsky/cg.pdf)

Entry points, if the primary papers are heavy going:

- S. Abramsky, *Semantics of Interaction: an Introduction to Game Semantics*, CLiCS Summer School, Cambridge University Press, 1997, 1–31. [arXiv](https://arxiv.org/abs/1312.0121)
- S. Abramsky, G. McCusker, *Game Semantics*, Marktoberdorf lecture notes, 1999. [PDF](https://www.irif.fr/~mellies/mpri/mpri-ens/articles/abramsky-mccusker-game-semantics.pdf)
- P.-L. Curien, *Definability and Full Abstraction*, a survey of how the question was posed and answered. [PDF](https://www.irif.fr/~curien/gordon-fs-plc.pdf)
- Abramsky's publication list, organized by theme. [Index](https://www.cs.ox.ac.uk/people/samson.abramsky/pubs.html)

A caution the literature is explicit about, and which this repo should not overstate. Nobody proved that the quotient of strategies is isomorphic to *all* functions `A → B`. The point runs the other way: games cut the function space down to what is sequentially realizable. So `-i>` does not simply hold more morphisms than `→`. It holds more structure per computation while realizing fewer extensional functions, and `src/Extensional.agda` reflects this by recording realizability as a witness rather than assuming it.

## Type-checking

The project expects Agda 2.8.0 and `standard-library-2.4`:

```bash
just info                         # active compiler and libraries
just doctor                       # verify the installation
just stdlib-info                  # installed, registered, and selected stdlib
just stdlib-use 2.4               # select a registered version
just stdlib-install 2.4           # install and select an upstream release
just check src/BoolExample.agda   # check one module
just check-all                    # check the complete development
just ci                           # run the same gate as GitHub Actions
just                              # list every available command
```

GitHub Actions runs `just ci` on pushes to `master`,
on version tags, and on pull requests targeting the maintained branch patterns.
The workflow uses the official Agda setup action with Agda 2.8.0 and
standard-library 2.4; it does not depend on a distribution package manager.

## License

This project is available under the [MIT License](LICENSE).
