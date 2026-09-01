module src.BoolExample where

open import Agda.Builtin.Sigma
open import Data.Bool using (Bool; false; true; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import src.Game
open import src.Arena
open import src.Strategy
open import src.InteractionArrow

data Side : Set where left right : Side

Inputs : Game
Question Inputs = Side
Answer Inputs _ = Bool

Output : Game
Question Output = ⊤
Answer Output _ = Bool

-- A dialogue on the arena `Inputs ⊸ Output`: it may ask either input.
BoolStrategy : Set
BoolStrategy = Tree (val Inputs ⊸ val Output) Bool

askL askR : BoolStrategy → BoolStrategy → BoolStrategy
askL f t = ask (inj₁ left)  (λ { false → f ; true → t })
askR f t = ask (inj₁ right) (λ { false → f ; true → t })

andLR andRL : BoolStrategy
andLR = askL (return false) (askR (return false) (return true))
andRL = askR (return false) (askL (return false) (return true))

environment : Bool × Bool → ⟦ Inputs ⟧
environment p left  = proj₁ p
environment p right = proj₂ p

eval : BoolStrategy → Bool × Bool → Bool
eval s p = run s (envOf {Inputs} {Output} (environment p))

andLR≢andRL : ¬ (andLR ≡ andRL)
andLR≢andRL ()

same-ext : ∀ p → eval andLR p ≡ eval andRL p
same-ext (false , false) = refl
same-ext (false , true)  = refl
same-ext (true  , false) = refl
same-ext (true  , true)  = refl

and-function : ∀ p → eval andLR p ≡ (proj₁ p ∧ proj₂ p)
and-function (false , false) = refl
and-function (false , true)  = refl
and-function (true  , false) = refl
and-function (true  , true)  = refl

andLR-i andRL-i : val Inputs -i> val Output
respond andLR-i (inj₁ ())
respond andLR-i (inj₂ tt) = andLR
respond andRL-i (inj₁ ())
respond andRL-i (inj₂ tt) = andRL

-- Flat booleans are `Maybe Bool`: exactly the three strategies of the boolean
-- game, with `nothing` the one that never answers. Divergence is the context
-- declining, so it has the same meaning here as in `_≈obs_`.
Bool⊥ : Set
Bool⊥ = Maybe Bool

-- A pair of possibly-undefined inputs is a context on the same arena the AND
-- strategies live on.
flat-context : Bool⊥ × Bool⊥ → PEnv (val Inputs ⊸ val Output)
flat-context p (inj₁ left)  = proj₁ p
flat-context p (inj₁ right) = proj₂ p
flat-context p (inj₂ ())

evalP : BoolStrategy → Bool⊥ × Bool⊥ → Bool⊥
evalP s p = runP s (flat-context p)

por : Bool⊥ × Bool⊥ → Bool⊥
por (just true  , _)           = just true
por (_          , just true)   = just true
por (just false , just false)  = just false
por (_          , _)           = nothing

Realizes : BoolStrategy → (Bool⊥ × Bool⊥ → Bool⊥) → Set
Realizes s f = ∀ p → evalP s p ≡ f p

no-return-por : ∀ b → ¬ Realizes (return b) por
no-return-por false realizes with realizes (just true , just true)
... | ()
no-return-por true  realizes with realizes (just false , just false)
... | ()

-- Whichever input it inspects first, a context can decline exactly that one
-- while answering the other, so no dialogue tree realizes parallel-or.
no-sequential-por : ¬ (Σ BoolStrategy (λ s → Realizes s por))
no-sequential-por (return b , realizes) = no-return-por b realizes
no-sequential-por (ask (inj₁ left)  k , realizes) with realizes (nothing , just true)
... | ()
no-sequential-por (ask (inj₁ right) k , realizes) with realizes (just true , nothing)
... | ()
no-sequential-por (ask (inj₂ ()) k , realizes)
