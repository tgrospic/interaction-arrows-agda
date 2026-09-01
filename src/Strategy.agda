module src.Strategy where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import src.Game
open import src.Arena

-- A strategy is a finite dialogue tree: it either returns, or asks one of the
-- questions Player is allowed to ask and chooses a continuation per answer.
data Tree (G : Arena) (X : Set) : Set where
  return : X → Tree G X
  ask    : (q : PQ G) → (PA G q → Tree G X) → Tree G X

run : ∀ {G X} → Tree G X → Env G → X
run (return x) ρ = x
run (ask q k)  ρ = run (k (ρ q)) ρ

infixl 25 _>>=_
_>>=_ : ∀ {G X Y} → Tree G X → (X → Tree G Y) → Tree G Y
return x >>= k = k x
ask q c  >>= k = ask q (λ a → c a >>= k)

-- A strategy on a single arena: one dialogue per question Opponent may ask.
record Strategy (G : Arena) : Set where
  field
    respond : (q : OQ G) → Tree G (OA G q)

open Strategy public

infix 4 _≈ext_
_≈ext_ : ∀ {G} → Strategy G → Strategy G → Set
σ ≈ext τ = ∀ q ρ → run (respond σ q) ρ ≡ run (respond τ q) ρ

≈ext-refl : ∀ {G} {σ : Strategy G} → σ ≈ext σ
≈ext-refl q ρ = refl

≈ext-sym : ∀ {G} {σ τ : Strategy G} → σ ≈ext τ → τ ≈ext σ
≈ext-sym e q ρ = sym (e q ρ)

≈ext-trans : ∀ {G} {σ τ υ : Strategy G} → σ ≈ext τ → τ ≈ext υ → σ ≈ext υ
≈ext-trans e₁ e₂ q ρ = trans (e₁ q ρ) (e₂ q ρ)

-- Contexts. A context may decline to answer, which is what lets it observe the
-- order in which a strategy asks its questions; with total environments every
-- context is itself extensional and observes nothing beyond the induced function.
PEnv : Arena → Set
PEnv G = (q : PQ G) → Maybe (PA G q)

runP : ∀ {G X} → Tree G X → PEnv G → Maybe X
runP (return x) ρ = just x
runP (ask q k)  ρ = maybe (λ a → runP (k a) ρ) nothing (ρ q)

total : ∀ {G} → Env G → PEnv G
total ρ q = just (ρ q)

runP-total : ∀ {G X} (t : Tree G X) (ρ : Env G) → runP t (total {G} ρ) ≡ just (run t ρ)
runP-total (return x) ρ = refl
runP-total (ask q k)  ρ = runP-total (k (ρ q)) ρ

infix 4 _≈obs_
_≈obs_ : ∀ {G} → Strategy G → Strategy G → Set
σ ≈obs τ = ∀ q ρ → runP (respond σ q) ρ ≡ runP (respond τ q) ρ

≈obs-refl : ∀ {G} {σ : Strategy G} → σ ≈obs σ
≈obs-refl q ρ = refl

≈obs-sym : ∀ {G} {σ τ : Strategy G} → σ ≈obs τ → τ ≈obs σ
≈obs-sym e q ρ = sym (e q ρ)

≈obs-trans : ∀ {G} {σ τ υ : Strategy G} → σ ≈obs τ → τ ≈obs υ → σ ≈obs υ
≈obs-trans e₁ e₂ q ρ = trans (e₁ q ρ) (e₂ q ρ)

-- Contextual equivalence refines extensional equality: a total environment is
-- just a context that always answers.
≈obs⇒≈ext : ∀ {G} {σ τ : Strategy G} → σ ≈obs τ → σ ≈ext τ
≈obs⇒≈ext {G} {σ} {τ} e q ρ =
  just-injective
    (trans (sym (runP-total (respond σ q) ρ))
           (trans (e q (total {G} ρ)) (runP-total (respond τ q) ρ)))

-- _≈obs_ mentions only `respond σ`, so σ is not determined by the type; the
-- implicits are bound explicitly to keep the metas solvable.
≈obs-isEquivalence : ∀ {G} → IsEquivalence (_≈obs_ {G})
≈obs-isEquivalence {G} = record
  { refl  = λ {σ}         → ≈obs-refl  {G} {σ}
  ; sym   = λ {σ} {τ}     → ≈obs-sym   {G} {σ} {τ}
  ; trans = λ {σ} {τ} {υ} → ≈obs-trans {G} {σ} {τ} {υ}
  }

-- The hom-setoid is the contextual one.
StrategySetoid : Arena → Setoid 0ℓ 0ℓ
StrategySetoid G = record
  { Carrier       = Strategy G
  ; _≈_           = _≈obs_
  ; isEquivalence = ≈obs-isEquivalence
  }

-- Observation, for the first-order case where both sides are value arenas.
envOf : ∀ {A B : Game} → ⟦ A ⟧ → Env (val A ⊸ val B)
envOf ρ (inj₁ a) = ρ a
envOf ρ (inj₂ ())

apply : ∀ {A B : Game} → Strategy (val A ⊸ val B) → ⟦ A ⟧ → ⟦ B ⟧
apply {A} {B} σ ρ q = run (respond σ (inj₂ q)) (envOf {A} {B} ρ)
