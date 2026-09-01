module scratch.essay_v03 where

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

data Grade' : Set where
  A B C D E : Grade'

data EssayS : Set where
  Unassigned Assigned Writing Reviewing Done : EssayS

data EssayCmd : Set → EssayS → EssayS → Set where
  Assign   : EssayCmd ⊤ Unassigned Assigned
  Start    : EssayCmd ⊤ Assigned Writing
  Consult  : {state : EssayS} → EssayCmd ⊤ state state
  Review   : EssayCmd ⊤ Writing Reviewing
  SendBack : EssayCmd ⊤ Reviewing Writing
  Grade    : (g : Grade') → EssayCmd Grade' Reviewing Done

data EssayCmd' (A : Set) : EssayS → EssayS → Set where
  Pure : ∀ {s} → A → EssayCmd' A s s
  Step : ∀ {s₁ s₂} → EssayCmd A s₁ s₂ → EssayCmd' A s₁ s₂
  Bind : ∀ {s₁ s₂ s₃} → EssayCmd' A s₁ s₂ → (A → EssayCmd' A s₂ s₃) → EssayCmd' A s₁ s₃

record IMonad (M : Set → EssayS → EssayS → Set) : Set₁ where
  field
    return : ∀ {A s} → A → M A s s
    _>>=_  : ∀ {A s₁ s₂ s₃} → M A s₁ s₂ → (A → M A s₂ s₃) → M A s₁ s₃

instance
  EssayCmd'-IMonad : IMonad EssayCmd'
  EssayCmd'-IMonad .IMonad.return = λ x → Pure x
  EssayCmd'-IMonad .IMonad._>>=_ = λ m f → Bind m f

open IMonad {{...}} public

essayProg1 : EssayCmd' ⊤ Unassigned Assigned
essayProg1 = do
  _ <- Step Consult
  Step Assign

essayProg2 : EssayCmd' ⊤ Writing Writing
essayProg2 = do
  _ <- Step Review
  Step SendBack

-- essayProg3 : EssayCmd' Grade' Reviewing Done
-- essayProg3 = do
--   _ <- Step SendBack
--   _ <- Step Review
--   return (Grade C)
