module src.Arena where

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import src.Game

-- Arenas are built, not merely described: making the constructions
-- constructors is what lets Agda invert `A ⊸ B` during unification.
infix  30 _^⊥
infixr 25 _⊗_
data Arena : Set₁ where
  val : Game → Arena          -- only Opponent asks
  _^⊥ : Arena → Arena         -- role reversal
  _⊗_ : Arena → Arena → Arena -- disjoint parallel composition

-- Which questions each side may ask.
mutual
  OQ : Arena → Set
  OQ (val G) = Question G
  OQ (A ^⊥)  = PQ A
  OQ (A ⊗ B) = OQ A ⊎ OQ B

  PQ : Arena → Set
  PQ (val G) = ⊥
  PQ (A ^⊥)  = OQ A
  PQ (A ⊗ B) = PQ A ⊎ PQ B

-- What each question admits as an answer.
mutual
  OA : (A : Arena) → OQ A → Set
  OA (val G) q = Answer G q
  OA (A ^⊥)  q = PA A q
  OA (A ⊗ B) = [ OA A , OA B ]

  PA : (A : Arena) → PQ A → Set
  PA (val G) ()
  PA (A ^⊥)  q = OA A q
  PA (A ⊗ B) = [ PA A , PA B ]

-- Linear implication as A^⊥ ⊗ B. For `val A ⊸ B`, play opens in B because
-- `PQ (val A)` is empty. General arenas need enabling to force that property.
infixr 20 _⊸_
_⊸_ : Arena → Arena → Arena
A ⊸ B = (A ^⊥) ⊗ B

-- The values of an arena are complete answers to its O-questions.
⟪_⟫ : Arena → Set
⟪ G ⟫ = (q : OQ G) → OA G q

-- An environment answers everything Player may ask.
Env : Arena → Set
Env G = (q : PQ G) → PA G q
