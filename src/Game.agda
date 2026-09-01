module src.Game where

open import Agda.Builtin.Equality
open import Data.List using (List; []; _∷_)

data Polarity : Set where
  O P : Polarity

-- A small question/answer arena. A value is a complete way of answering
-- Opponent's questions; it is not part of an interaction morphism.
record Game : Set₁ where
  field
    Question : Set
    Answer   : Question → Set

open Game public

⟦_⟧ : Game → Set
⟦ G ⟧ = (q : Question G) → Answer G q

data Move (G : Game) : Set where
  ask    : (q : Question G) → Move G
  answer : (q : Question G) → Answer G q → Move G

polarity : ∀ {G} → Move G → Polarity
polarity (ask _)      = O
polarity (answer _ _) = P

-- The finite protocol fragment used by the toy strategies below.
data Legal {G : Game} : List (Move G) → Set where
  empty : Legal []
  round : ∀ q a {xs} → Legal xs →
          Legal (ask q ∷ answer q a ∷ xs)

