module src.Concurrent where

open import Level using (0ℓ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Structures using (IsPartialOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; isEquivalence)
open import Relation.Nullary using (¬_)

data Event₃ : Set where a b c : Event₃

-- a and b are independent causes of c.
data _≼_ : Event₃ → Event₃ → Set where
  aa : a ≼ a
  bb : b ≼ b
  cc : c ≼ c
  ac : a ≼ c
  bc : b ≼ c

≼-refl : ∀ {x} → x ≼ x
≼-refl {a} = aa
≼-refl {b} = bb
≼-refl {c} = cc

≼-trans : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z
≼-trans aa q = q
≼-trans bb q = q
≼-trans cc cc = cc
≼-trans ac cc = ac
≼-trans bc cc = bc

≼-antisym : ∀ {x y} → x ≼ y → y ≼ x → x ≡ y
≼-antisym aa aa = refl
≼-antisym bb bb = refl
≼-antisym cc cc = refl

≼-isPartialOrder : IsPartialOrder _≡_ _≼_
≼-isPartialOrder = record
  { isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = λ { refl → ≼-refl }
      ; trans         = ≼-trans
      }
  ; antisym = ≼-antisym
  }

concurrent-position : Poset 0ℓ 0ℓ 0ℓ
concurrent-position = record
  { Carrier        = Event₃
  ; _≈_            = _≡_
  ; _≤_            = _≼_
  ; isPartialOrder = ≼-isPartialOrder
  }

infix 4 _∥_
_∥_ : Event₃ → Event₃ → Set
x ∥ y = (¬ x ≼ y) × (¬ y ≼ x)

a∥b : a ∥ b
a∥b = (λ ()) , (λ ())

causes-c : (a ≼ c) × (b ≼ c)
causes-c = ac , bc

-- A list-like schedule must choose an order that causality did not require.
data _≼s_ : Event₃ → Event₃ → Set where
  sa : a ≼s a
  sb : b ≼s b
  sc : c ≼s c
  sab : a ≼s b
  sac : a ≼s c
  sbc : b ≼s c

schedule-orders-independent-events : a ≼s b
schedule-orders-independent-events = sab
