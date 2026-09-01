module scratch.essay_v02b where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Primitive
open import Data.Product

data Grade : Set where
  A B C D E : Grade

data EssayS : Set where
  unassigned assigned writing reviewing done : EssayS

data EssayCmd : Set → EssayS → EssayS → Set where
  assign   : EssayCmd ⊤ unassigned assigned
  start    : EssayCmd ⊤ assigned writing
  consult  : {from to : EssayS} → EssayCmd ⊤ from to
  review   : EssayCmd ⊤ writing reviewing
  sendBack : EssayCmd ⊤ reviewing writing
  grade    : Grade → EssayCmd Grade reviewing done

_>>=_ : ∀ {a b s₁ s₂ s₃} → EssayCmd a s₁ s₂ → (a → EssayCmd b s₂ s₃) → EssayCmd b s₁ s₃
_>>=_ = _

essayProg1 : EssayCmd ⊤ unassigned assigned
essayProg1 = do
  _ ← consult
  assign

essayProg2 : EssayCmd ⊤ writing writing
essayProg2 = do
  _ ← review
  sendBack

essayProg3 : EssayCmd Grade reviewing done
essayProg3 = do
  _ ← sendBack
  _ ← review
  grade C

essayTy : ∀ {a s₁ s₂} → EssayCmd a s₁ s₂ → Set
essayTy (grade g) = String × Nat
essayTy consult = ⊤
essayTy _ = String

r1 : essayTy start
r1 = "Essay is started"

r2 : essayTy (grade A)
r2 = ("Essay is done", 1)

r3 : ∀ {from to} → essayTy (consult {from} {to})
r3 = tt
