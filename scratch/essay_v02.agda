module scratch.essay_v02 where

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

data Grade' : Set where
  A B C D E : Grade'

data EssayS : Set where
  Unassigned Assigned Writing Reviewing Done : EssayS

data EssayCmd : Set → EssayS → EssayS → Set where
  Assign   : EssayCmd ⊤ Unassigned Assigned
  Start    : EssayCmd ⊤ Assigned Writing
  Consult  : {s : EssayS} → EssayCmd ⊤ s s
  Review   : EssayCmd ⊤ Writing Reviewing
  SendBack : EssayCmd ⊤ Reviewing Writing
  Grade    : Grade' → EssayCmd Grade' Reviewing Done

-- return : ∀ {A} → A → EssayCmd
-- return = ∀ {s} → λ ty -> EssayCmd ty s s

_>>=_ : ∀ {a b s1 s2 s3} → EssayCmd a s1 s2 → (a → EssayCmd b s2 s3) → EssayCmd b s1 s3
_>>=_ = ∀ {a b s1 s2 s3} → EssayCmd a s1 s2 → (a → EssayCmd b s2 s3) → EssayCmd b s1 s3

essayProg1 : EssayCmd ⊤ Unassigned Assigned
essayProg1 = do
  _ <- Consult
  Assign

essayProg2 : EssayCmd ⊤ Writing Writing
essayProg2 = do
  _ <- Review
  SendBack

-- essayProg3 : EssayCmd Grade' Reviewing Done
-- essayProg3 =
--   Step SendBack >>= λ _ →
--   Step Review >>= λ _ →
--   Step (Grade C)
