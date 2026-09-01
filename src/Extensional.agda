module src.Extensional where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import src.Game
open import src.Arena
open import src.Strategy
open import src.InteractionArrow

infix 4 _≗_
_≗_ : ∀ {A B : Set} → (A → B) → (A → B) → Set
f ≗ g = ∀ x → f x ≡ g x

ext : ∀ {A B : Game} → val A -i> val B → ⟦ A ⟧ → ⟦ B ⟧
ext {A} {B} = apply {A} {B}

ext-id : ∀ {A : Game} → ext {A} {A} id-i ≗ (λ x → x)
ext-id ρ = refl

-- The environment a strategy hands to the one it feeds.
envOf-restrict : ∀ {A B C : Game} (ρ : ⟦ A ⟧) q →
  restrict (val A) B (val C) (envOf {A} {C} ρ) q ≡ envOf {A} {B} ρ q
envOf-restrict ρ (inj₁ a) = refl
envOf-restrict ρ (inj₂ ())

mid-envOf : ∀ {A B C : Game} (f : val A -i> val B) (ρ : ⟦ A ⟧) q →
  mid (val A) B (val C) f (envOf {A} {C} ρ) q ≡ envOf {B} {C} (ext {A} {B} f ρ) q
mid-envOf {A} {B} {C} f ρ (inj₁ b) =
  trans (run-shift (val A) B (val C) (respond f (inj₂ b)) (envOf {A} {C} ρ))
        (run-cong (respond f (inj₂ b)) (envOf-restrict {A} {B} {C} ρ))
mid-envOf f ρ (inj₂ ())

ext-compose : ∀ {A B C : Game} (g : val B -i> val C) (f : val A -i> val B) →
  ∀ ρ q → ext {A} {C} (g ∘i f) ρ q ≡ ext {B} {C} g (ext {A} {B} f ρ) q
ext-compose {A} {B} {C} g f ρ q =
  trans (run-interact (val A) B (val C) (respond g (inj₂ q)) f (envOf {A} {C} ρ))
        (run-cong (respond g (inj₂ q)) (mid-envOf {A} {B} {C} f ρ))

I : Game
Question I = ⊥
Answer I = ⊥-elim

unit-value : ⟦ I ⟧
unit-value = λ q → ⊥-elim q

quote-value : ∀ {A : Game} → ⟦ A ⟧ → val I -i> val A
respond (quote-value a) (inj₁ ())
respond (quote-value a) (inj₂ q) = return (a q)

observe : ∀ {B : Game} → val I -i> val B → ⟦ B ⟧
observe {B} σ = ext {I} {B} σ unit-value

ext-via-closure : ∀ {A B : Game} (f : val A -i> val B) (a : ⟦ A ⟧) →
  ∀ q → observe {B} (f ∘i quote-value a) q ≡ ext {A} {B} f a q
ext-via-closure {A} {B} f a q = ext-compose {I} {A} {B} f (quote-value a) unit-value q

-- Being a function is not enough to be a morphism, so realizability is a witness.
record ExtensionalArrow (A B : Game) : Set where
  field
    function   : ⟦ A ⟧ → ⟦ B ⟧
    witness    : val A -i> val B
    realizable : ext {A} {B} witness ≗ function
