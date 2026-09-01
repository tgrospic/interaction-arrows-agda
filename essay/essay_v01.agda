-- {-# OPTIONS --cubical-compatible --safe #-}

module essay.essay_v01 where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Data.Product

data Grade : Set where
  A B C D E : Grade

data EssayS : Set where
  unassigned assigned writing reviewing done : EssayS

private
  variable
    a b : Set
    s s₁ s₂ s₃ : EssayS

data EssayCmd : Set → EssayS → EssayS → Set where
  assign   : EssayCmd ⊤ unassigned assigned
  start    : EssayCmd ⊤ assigned writing
  consult  : EssayCmd ⊤ s s
  review   : EssayCmd ⊤ writing reviewing
  sendBack : EssayCmd ⊤ reviewing writing
  grade    : Grade → EssayCmd Grade reviewing done

  pure     : a → EssayCmd a s s
  _>>=_    : EssayCmd a s₁ s₂ → (a → EssayCmd b s₂ s₃) → EssayCmd b s₁ s₃

prog₁ : EssayCmd ⊤ unassigned assigned
prog₁ = do
  _ ← consult
  _ ← consult
  assign

prog₂ : EssayCmd ⊤ writing writing
prog₂ = do
  _ ← review
  sendBack

prog₃ : EssayCmd Grade reviewing done
prog₃ = do
  _ ← sendBack
  _ ← review
  grade C

essayTy : EssayCmd a s₁ s₂ → Set
essayTy (grade _) = String × Nat
essayTy consult   = ⊤
essayTy _         = String

-- Examples
r₁ : essayTy start
r₁ = "Essay is started"

r₂ : essayTy (grade A)
r₂ = ("Essay is done" , 100)

r₃ : essayTy consult
r₃ = tt
