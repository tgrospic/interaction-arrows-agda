module src.Audit where

open import Data.Bool using (Bool; false; true)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (¬_)
open import src.Game
open import src.Arena
open import src.Strategy
open import src.InteractionArrow
open import src.BoolExample

-- What each of the three relations of this development can see.
--
-- andLR and andRL query their inputs in opposite orders. Propositional
-- equality separates them as syntax. Extensional equality identifies them,
-- because they induce the same Boolean function. Contextual equivalence
-- separates them again, and it is the relation the category laws are proved
-- against, so the intensional content is inside the theory rather than beside it.

-- 1. Syntax separates them.
trees-differ : ¬ (andLR ≡ andRL)
trees-differ = andLR≢andRL

-- 2. Extensional equality does not.
env-eq : ∀ (ρ : Env (val Inputs ⊸ val Output)) q →
         envOf {Inputs} {Output}
               (environment (ρ (inj₁ left) , ρ (inj₁ right))) q ≡ ρ q
env-eq ρ (inj₁ left)  = refl
env-eq ρ (inj₁ right) = refl
env-eq ρ (inj₂ ())

andLR-i≈ext-andRL-i : andLR-i ≈ext andRL-i
andLR-i≈ext-andRL-i (inj₁ ()) ρ
andLR-i≈ext-andRL-i (inj₂ tt) ρ =
  trans (sym (run-cong andLR (env-eq ρ)))
        (trans (same-ext (ρ (inj₁ left) , ρ (inj₁ right)))
               (run-cong andRL (env-eq ρ)))

-- 3. Contextual equivalence does. This context answers the right input and
-- declines the left one, so it observes which question is asked first.
right-only : PEnv (val Inputs ⊸ val Output)
right-only = flat-context (nothing , just false)

andLR-blocks : runP andLR right-only ≡ nothing
andLR-blocks = refl

andRL-answers : runP andRL right-only ≡ just false
andRL-answers = refl

andLR-i≉andRL-i : ¬ (andLR-i ≈obs andRL-i)
andLR-i≉andRL-i e with e (inj₂ tt) right-only
... | ()
