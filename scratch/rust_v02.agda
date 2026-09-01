{-# OPTIONS --without-K --safe #-}

module scratch.rust_v02 where

open import Data.Nat using (ℕ)

-- Traits
record Start (Self Next : Set) : Set where
  field start₀ : Self → Next

record Writing (Self Next : Set) : Set where
  field write₀ : Self → Next

record Review (Self Back : Set) : Set where
  field
    review-back : Self → Back
    review-done : Self → ℕ

-- Trait functions
start : ∀ {Self Next} → ⦃ Start Self Next ⦄ → Self → Next
start ⦃ inst ⦄ = Start.start₀ inst

write : ∀ {Self Next} → ⦃ Writing Self Next ⦄ → Self → Next
write ⦃ inst ⦄ = Writing.write₀ inst

review-back : ∀ {Self Back} → ⦃ Review Self Back ⦄ → Self → Back
review-back ⦃ inst ⦄ = Review.review-back inst

review-done : ∀ {Self Back} → ⦃ Review Self Back ⦄ → Self → ℕ
review-done ⦃ inst ⦄ = Review.review-done inst

-- Define pipe operator
infixl 20 _>>_

_>>_ : ∀ {A B} → A → (A → B) → B
x >> f = f x

-- Program using >> chaining
prog1
  : ∀ {P W R}
  → (p : P)
  → ⦃ _ : Start P W ⦄
  → ⦃ _ : Writing W R ⦄
  → ⦃ _ : Review R W ⦄
  → ⦃ _ : Writing W R ⦄
  → ℕ
--prog1 p = p >> start >> write >> review-back >> write >> review-done
prog1 p = p >> start >> write >> review-done
-- prog1 p = do
--   p
--   start
--   write
--   review-back
--   write
--   review-done
