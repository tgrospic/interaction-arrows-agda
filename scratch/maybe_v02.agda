module scratch.maybe_v02 where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

data Maybe (A : Set) : Set where
  none : Maybe A
  some : A → Maybe A

_>>=_ : ∀ {a b : Set} → Maybe a → (a → Maybe b) → Maybe b
some a >>= f = f a
none >>= f = none
