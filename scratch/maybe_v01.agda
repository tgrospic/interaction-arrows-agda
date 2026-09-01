module scratch.maybe_v01 where

open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat

_>>=_ : ∀ {A B} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= f = nothing
just x  >>= f = f x

return : ∀ {A} → A → Maybe A
return = just

example : Maybe Nat
example =
  just 2 >>= λ x →
  just 5 >>= λ y →
  return (x + y)


example2 : Maybe Nat
example2 = do
  x <- just 2
  y <- just 5
  return (x + y)
