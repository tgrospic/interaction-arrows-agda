module scratch.essay_v02a where

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Primitive using (Level; lzero; lsuc)

-- Define universe levels
GradeLevel : Level
GradeLevel = lzero

EssaySLevel : Level
EssaySLevel = lzero

data Grade : Set where
  A B C D E : Grade

data EssayS : Set where
  unassigned assigned writing reviewing done : EssayS

data EssayCmd (from to : EssayS) : Set where
  assign   : (from ≡ unassigned) → (to ≡ assigned) → ⊤ → EssayCmd from to
  start    : (from ≡ assigned) → (to ≡ writing) → ⊤ → EssayCmd from to
  consult  : ⊤ → EssayCmd from to
  review   : (from ≡ writing) → (to ≡ reviewing) → ⊤ → EssayCmd from to
  sendback : (from ≡ reviewing) → (to ≡ writing) → ⊤ → EssayCmd from to
  grade    : (from ≡ reviewing) → (to ≡ done) → (g : Grade) → EssayCmd from to

-- _>>=_ : ∀ {a b s1 s2 s3} → EssayCmd a s1 s2 → (a → EssayCmd b s2 s3) → EssayCmd b s1 s3
_>>=_ : ∀ {s1 s2 s3} {g1 g2 : Grade} → EssayCmd g1 s1 s2 → (⊤ → EssayCmd g2 s2 s3) →
  EssayCmd g2 s1 s3
_>>=_ = ?

return : ∀ {g : Grade} {s} → ⊤ → EssayCmd g s s
return = ?
--return = ∀ {s} → λ ty -> EssayCmd ty s s

essayProg1 : EssayCmd ⊤ unassigned assigned
essayProg1 = do
  _ <- consult
  return assign

essayProg2 : EssayCmd ⊤ writing writing
essayProg2 = do
  _ <- review
  return sendback

-- essayProg3 : EssayCmd Grade reviewing done
-- essayProg3 = do
--   -- _ <- sendback
--   -- _ <- review
--   return (grade C)



--_>>=_ : ∀ {A} -> EssayCmd → (A → EssayCmd) → EssayCmd
