module src.Category where

open import Level using (0ℓ)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import src.Game
open import src.Arena
open import src.Strategy
open import src.InteractionArrow
open import src.Extensional

-- A category whose hom-sets carry an equivalence, with composition required to
-- respect it. Objects are games, because composition needs a value arena in
-- the middle; the arenas either side may still be arbitrary.
record SetoidCategory (Obj : Set₁) : Set₂ where
  field
    Hom : Obj → Obj → Setoid 0ℓ 0ℓ

  hom : Obj → Obj → Set
  hom A B = Setoid.Carrier (Hom A B)

  infix 4 _≋_
  _≋_ : ∀ {A B} → hom A B → hom A B → Set
  _≋_ {A} {B} = Setoid._≈_ (Hom A B)

  field
    identity      : ∀ {A} → hom A A
    compose       : ∀ {A B C} → hom B C → hom A B → hom A C
    compose-cong  : ∀ {A B C} {g g′ : hom B C} {f f′ : hom A B} →
                    g ≋ g′ → f ≋ f′ → compose g f ≋ compose g′ f′
    unitˡ         : ∀ {A B} (f : hom A B) → compose identity f ≋ f
    unitʳ         : ∀ {A B} (f : hom A B) → compose f identity ≋ f
    associativity : ∀ {A B C D} (h : hom C D) (g : hom B C) (f : hom A B) →
                    compose (compose h g) f ≋ compose h (compose g f)

-- The first-order value-game category: strategies on `val A ⊸ val B`, up to
-- partial-environment observational equality.
interaction : SetoidCategory Game
interaction = record
  { Hom           = λ A B → StrategySetoid (val A ⊸ val B)
  ; identity      = id-i
  ; compose       = _∘i_
  ; compose-cong  = ∘i-cong
  ; unitˡ         = left-id
  ; unitʳ         = right-id
  ; associativity = assoc
  }

-- The observation homomorphism into ordinary functions, compared pointwise.
-- Its target operations are spelled out rather than bundled as a second
-- category; that is only a choice of scope.
record SetoidFunctor (C : SetoidCategory Game) : Set₁ where
  open SetoidCategory C
  field
    onHom         : ∀ {A B} → hom A B → ⟦ A ⟧ → ⟦ B ⟧
    onHom-cong    : ∀ {A B} {f g : hom A B} → f ≋ g →
                    ∀ ρ q → onHom f ρ q ≡ onHom g ρ q
    onHom-id      : ∀ {A} ρ q → onHom (identity {A}) ρ q ≡ ρ q
    onHom-compose : ∀ {A B D} (g : hom B D) (f : hom A B) →
                    ∀ ρ q → onHom (compose g f) ρ q ≡ onHom g (onHom f ρ) q

observation : SetoidFunctor interaction
observation = record
  { onHom         = λ {A} {B} σ → ext {A} {B} σ
  ; onHom-cong    = λ {A} {B} {f} {g} e ρ q →
                      ≈obs⇒≈ext {val A ⊸ val B} {f} {g} e (inj₂ q) (envOf {A} {B} ρ)
  ; onHom-id      = λ ρ q → refl
  ; onHom-compose = λ g f ρ q → ext-compose g f ρ q
  }
