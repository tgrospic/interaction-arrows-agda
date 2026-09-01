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
open import src.Extensional

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
flat-value : Bool⊥ × Bool⊥ → ⟦ Inputs ⟧P
flat-value p left  = proj₁ p
flat-value p right = proj₂ p

flat-context : Bool⊥ × Bool⊥ → PEnv (val Inputs ⊸ val Output)
flat-context p = envOfP {Inputs} {Output} (flat-value p)

evalP : BoolStrategy → Bool⊥ × Bool⊥ → Bool⊥
evalP s p = runP s (flat-context p)

por : Bool⊥ × Bool⊥ → Bool⊥
por (just true  , _)           = just true
por (_          , just true)   = just true
por (just false , just false)  = just false
por (_          , _)           = nothing

RealizesTree : BoolStrategy → (Bool⊥ × Bool⊥ → Bool⊥) → Set
RealizesTree s f = ∀ p → evalP s p ≡ f p

no-return-por : ∀ b → ¬ RealizesTree (return b) por
no-return-por false realizes with realizes (just true , just true)
... | ()
no-return-por true  realizes with realizes (just false , just false)
... | ()

-- Whichever input it inspects first, a context can decline exactly that one
-- while answering the other, so no finite BoolStrategy realizes parallel-or.
no-sequential-por-tree : ¬ (Σ BoolStrategy (λ s → RealizesTree s por))
no-sequential-por-tree (return b , realizes) = no-return-por b realizes
no-sequential-por-tree (ask (inj₁ left)  k , realizes) with realizes (nothing , just true)
... | ()
no-sequential-por-tree (ask (inj₁ right) k , realizes) with realizes (just true , nothing)
... | ()
no-sequential-por-tree (ask (inj₂ ()) k , realizes)

-- The theorem in the arrow: no morphism `val Inputs -i> val Output` has
-- parallel-or as its partial extensional collapse.
Realizes : (val Inputs -i> val Output) → (Bool⊥ × Bool⊥ → Bool⊥) → Set
Realizes σ f = ∀ p → extP {Inputs} {Output} σ (flat-value p) tt ≡ f p

no-sequential-por : ¬ (Σ (val Inputs -i> val Output) (λ σ → Realizes σ por))
no-sequential-por (σ , realizes) =
  no-sequential-por-tree (respond σ (inj₂ tt) , realizes)
