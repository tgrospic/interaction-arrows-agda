module scratch.rust_v01 where

open import Data.Nat using (ℕ)

-- Traits with both Self and explicit Next
record Start (Self Next : Set) : Set where
  field start : Self → Next

record Writing (Self Next : Set) : Set where
  field write : Self → Next

record Review (Self Back : Set) : Set where
  field
    review-back  : Self → Back
    review-done  : Self → ℕ

open Start {{...}} public
open Writing {{...}} public
open Review {{...}} public

-- Program
prog1
  : ∀ {P W R}
  → (p : P)
  → {{_ : Start P W}}
  → {{_ : Writing W R}}
  → {{_ : Review R W}}
  → ℕ

prog1 p =
  let
    w₀ = start p
    r₀ = write w₀
    w₁ = review-back r₀
    r₁ = write w₁
  in
    review-done r₁

-- Usage

data P : Set where p₀ : P
data W : Set where w₀ : W
data R : Set where r₀ : R

instance
  startP : Start P W
  startP .start p₀ = w₀

  writeW : Writing W R
  writeW .write w₀ = r₀

  reviewR : Review R W
  reviewR .review-back r₀ = w₀
  reviewR .review-done r₀ = 87

example : ℕ
example = prog1 p₀
-- result: 87
