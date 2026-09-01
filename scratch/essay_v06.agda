module scratch.essay_v06 where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Data.Product

-- Grade
data Grade' : Set where
  A B C D E : Grade'

-- Essay States
data EssayS : Set where
  unassigned assigned writing reviewing done : EssayS

-- Essay Instructions (one step)
data EssayInstr (s₁ s₂ : EssayS) (next : Set) : Set where
  Assign   : (⊤ → next) → EssayInstr unassigned assigned next
  Start    : (⊤ → next) → EssayInstr assigned writing next
  Consult  : (⊤ → next) → (s : EssayS) → EssayInstr s s next
  Review   : (⊤ → next) → EssayInstr writing reviewing next
  SendBack : (⊤ → next) → EssayInstr reviewing writing next
  Grade    : Grade' → (Grade' → next) → EssayInstr reviewing done next

-- Main Essay Program
data EssayCmd (s₁ s₂ : EssayS) (a : Set) : Set where
  pure : a → EssayCmd s₁ s₁ a
  impure : ∀ {sₘ} → EssayInstr s₁ sₘ (EssayCmd sₘ s₂ a) → EssayCmd s₁ s₂ a

-- Map inside an instruction
mapInstr : ∀ {s₁ s₂ a b}
         → EssayInstr s₁ s₂ a
         → (a → b)
         → EssayInstr s₁ s₂ b
mapInstr (Assign next)    f = Assign (λ x → f (next x))
mapInstr (Start next)     f = Start (λ x → f (next x))
mapInstr (Consult next s) f = Consult (λ x → f (next x)) s
mapInstr (Review next)    f = Review (λ x → f (next x))
mapInstr (SendBack next)  f = SendBack (λ x → f (next x))
mapInstr (Grade g next)   f = Grade g (λ x → f (next x))

-- Monad bind (>>=)
_>>=_ : ∀ {s₁ s₂ s₃ a b}
      → EssayCmd s₁ s₂ a
      → (a → EssayCmd s₂ s₃ b)
      → EssayCmd s₁ s₃ b
pure x >>= k = k x
impure instr >>= k = impure (mapInstr instr (λ next → next >>= k))

-- Smart constructors
assign : EssayCmd unassigned assigned ⊤
assign = impure (Assign pure)

start : EssayCmd assigned writing ⊤
start = impure (Start pure)

consult : ∀ {s} → EssayCmd s s ⊤
consult {s} = impure (Consult pure s)

review : EssayCmd writing reviewing ⊤
review = impure (Review pure)

sendBack : EssayCmd reviewing writing ⊤
sendBack = impure (SendBack pure)

grade : Grade → EssayCmd reviewing done Grade
grade g = impure (Grade g pure)

-- Example Programs

essay1 : EssayCmd unassigned assigned ⊤
essay1 = assign

essay2 : EssayCmd assigned writing ⊤
essay2 = do
  _ <- consult
  start

essay3 : EssayCmd writing reviewing ⊤
essay3 = review

essay4 : EssayCmd reviewing writing ⊤
essay4 = sendBack

essay5 : EssayCmd reviewing done Grade
essay5 = grade B

-- Invalid program (should not typecheck)
{-
bad : EssayCmd assigned done Grade
bad = do
  _ <- start
  grade A
-}
