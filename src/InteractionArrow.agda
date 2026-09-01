module src.InteractionArrow where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import src.Game
open import src.Arena
open import src.Strategy

infixr 20 _-i>_
_-i>_ : Arena → Arena → Set
A -i> B = Strategy (A ⊸ B)

-- Copycat, two-sided: whichever side is asked, copy the question across and
-- hand back the answer unchanged.
id-i : ∀ {A} → A -i> A
respond id-i (inj₁ p) = ask (inj₂ p) return
respond id-i (inj₂ o) = ask (inj₁ o) return

-- A value arena has no P-questions, so a dialogue over `A ⊸ val B` is already
-- a dialogue over `A ⊸ C`. The arenas are explicit: `Env` and `Tree` reduce
-- past them, so they are not inferable from the types.
shift : ∀ (A : Arena) (B : Game) (C : Arena) {X} →
        Tree (A ⊸ val B) X → Tree (A ⊸ C) X
shift A B C (return x)        = return x
shift A B C (ask (inj₁ a) k)  = ask (inj₁ a) (λ r → shift A B C (k r))
shift A B C (ask (inj₂ ()) k)

restrict : ∀ (A : Arena) (B : Game) (C : Arena) →
           Env (A ⊸ C) → Env (A ⊸ val B)
restrict A B C ρ (inj₁ a) = ρ (inj₁ a)
restrict A B C ρ (inj₂ ())

restrict-id : ∀ (A : Arena) (B : Game) (ρ : Env (A ⊸ val B)) q →
              restrict A B (val B) ρ q ≡ ρ q
restrict-id A B ρ (inj₁ a) = refl
restrict-id A B ρ (inj₂ ())

run-shift : ∀ (A : Arena) (B : Game) (C : Arena) {X}
            (t : Tree (A ⊸ val B) X) (ρ : Env (A ⊸ C)) →
            run (shift A B C t) ρ ≡ run t (restrict A B C ρ)
run-shift A B C (return x)       ρ = refl
run-shift A B C (ask (inj₁ a) k) ρ = run-shift A B C (k (ρ (inj₁ a))) ρ
run-shift A B C (ask (inj₂ ()) k) ρ

-- Interaction plus hiding: the middle arena's moves do not appear in the result.
interact : ∀ (A : Arena) (B : Game) (C : Arena) {X} →
           Tree (val B ⊸ C) X → (A -i> val B) → Tree (A ⊸ C) X
interact A B C (return x)       σ = return x
interact A B C (ask (inj₁ b) k) σ =
  shift A B C (respond σ (inj₂ b)) >>= λ r → interact A B C (k r) σ
interact A B C (ask (inj₂ c) k) σ = ask (inj₂ c) (λ r → interact A B C (k r) σ)

hide : ∀ (A : Arena) (B : Game) (C : Arena) {X} →
       Tree (val B ⊸ C) X → (A -i> val B) → Tree (A ⊸ C) X
hide = interact

-- Composition, with a value arena in the middle.
--
-- The outer arenas A and C stay fully general, so higher-order arenas compose
-- on the outside. The middle is restricted to `val B` deliberately. With a
-- general arena there, the two strategies can question each other back and
-- forth across it: a P-question of the middle raised by σ has to be answered
-- by τ, whose answer may raise another, and the recursion stops being
-- structural. That is the infinite chattering problem, and showing σ;τ total
-- in its presence is a development of its own (Abramsky, Semantics of
-- Interaction §2). Restricting the middle states that limit in the type
-- rather than postulating past it: `PQ (val B)` is empty, so the chatter
-- cannot start and every recursion below is on a subtree.
infixr 30 _∘i_
_∘i_ : ∀ {A C} {B : Game} → (val B -i> C) → (A -i> val B) → (A -i> C)
respond (_∘i_ {A} {C} {B} τ σ) (inj₁ a) = shift A B C (respond σ (inj₁ a))
respond (_∘i_ {A} {C} {B} τ σ) (inj₂ c) = hide A B C (respond τ (inj₂ c)) σ

InteractionHom : Arena → Arena → Setoid 0ℓ 0ℓ
InteractionHom A B = StrategySetoid (A ⊸ B)

run-bind : ∀ {G X Y} (t : Tree G X) (k : X → Tree G Y) ρ →
           run (t >>= k) ρ ≡ run (k (run t ρ)) ρ
run-bind (return x) k ρ = refl
run-bind (ask q c)  k ρ = run-bind (c (ρ q)) k ρ

run-cong : ∀ {G X} (t : Tree G X) {ρ τ : Env G} →
           (∀ q → ρ q ≡ τ q) → run t ρ ≡ run t τ
run-cong (return x) e = refl
run-cong (ask q k) {ρ} {τ} e rewrite e q = run-cong (k (τ q)) e

-- The environment the middle strategy is run against.
mid : ∀ (A : Arena) (B : Game) (C : Arena) →
      (A -i> val B) → Env (A ⊸ C) → Env (val B ⊸ C)
mid A B C σ ρ (inj₁ b) = run (shift A B C (respond σ (inj₂ b))) ρ
mid A B C σ ρ (inj₂ c) = ρ (inj₂ c)

run-interact : ∀ (A : Arena) (B : Game) (C : Arena) {X}
               (t : Tree (val B ⊸ C) X) (σ : A -i> val B) (ρ : Env (A ⊸ C)) →
               run (interact A B C t σ) ρ ≡ run t (mid A B C σ ρ)
run-interact A B C (return x) σ ρ = refl
run-interact A B C (ask (inj₁ b) k) σ ρ
  rewrite run-bind (shift A B C (respond σ (inj₂ b)))
                   (λ r → interact A B C (k r) σ) ρ =
  run-interact A B C (k (run (shift A B C (respond σ (inj₂ b))) ρ)) σ ρ
run-interact A B C (ask (inj₂ c) k) σ ρ = run-interact A B C (k (ρ (inj₂ c))) σ ρ

-- The partial counterparts of the run lemmas. A context may decline, so each
-- step carries a Maybe and the inductions split on it.

restrictP : ∀ (A : Arena) (B : Game) (C : Arena) →
            PEnv (A ⊸ C) → PEnv (A ⊸ val B)
restrictP A B C ρ (inj₁ a) = ρ (inj₁ a)
restrictP A B C ρ (inj₂ ())

restrictP-id : ∀ (A : Arena) (B : Game) (ρ : PEnv (A ⊸ val B)) q →
               restrictP A B (val B) ρ q ≡ ρ q
restrictP-id A B ρ (inj₁ a) = refl
restrictP-id A B ρ (inj₂ ())

runP-shift : ∀ (A : Arena) (B : Game) (C : Arena) {X}
             (t : Tree (A ⊸ val B) X) (ρ : PEnv (A ⊸ C)) →
             runP (shift A B C t) ρ ≡ runP t (restrictP A B C ρ)
runP-shift A B C (return x)       ρ = refl
runP-shift A B C (ask (inj₁ a) k) ρ with ρ (inj₁ a)
... | nothing = refl
... | just r  = runP-shift A B C (k r) ρ
runP-shift A B C (ask (inj₂ ()) k) ρ

runP-bind : ∀ {G X Y} (t : Tree G X) (k : X → Tree G Y) (ρ : PEnv G) →
            runP (t >>= k) ρ ≡ maybe (λ x → runP (k x) ρ) nothing (runP t ρ)
runP-bind (return x) k ρ = refl
runP-bind (ask q c)  k ρ with ρ q
... | nothing = refl
... | just a  = runP-bind (c a) k ρ

runP-cong : ∀ {G X} (t : Tree G X) {ρ τ : PEnv G} →
            (∀ q → ρ q ≡ τ q) → runP t ρ ≡ runP t τ
runP-cong (return x) e = refl
runP-cong (ask q k) {ρ} {τ} e rewrite e q with τ q
... | nothing = refl
... | just a  = runP-cong (k a) e

midP : ∀ (A : Arena) (B : Game) (C : Arena) →
       (A -i> val B) → PEnv (A ⊸ C) → PEnv (val B ⊸ C)
midP A B C σ ρ (inj₁ b) = runP (shift A B C (respond σ (inj₂ b))) ρ
midP A B C σ ρ (inj₂ c) = ρ (inj₂ c)

runP-interact : ∀ (A : Arena) (B : Game) (C : Arena) {X}
                (t : Tree (val B ⊸ C) X) (σ : A -i> val B) (ρ : PEnv (A ⊸ C)) →
                runP (interact A B C t σ) ρ ≡ runP t (midP A B C σ ρ)
runP-interact A B C (return x) σ ρ = refl
runP-interact A B C (ask (inj₁ b) k) σ ρ
  rewrite runP-bind (shift A B C (respond σ (inj₂ b)))
                    (λ r → interact A B C (k r) σ) ρ
  with runP (shift A B C (respond σ (inj₂ b))) ρ
... | nothing = refl
... | just r  = runP-interact A B C (k r) σ ρ
runP-interact A B C (ask (inj₂ c) k) σ ρ with ρ (inj₂ c)
... | nothing = refl
... | just r  = runP-interact A B C (k r) σ ρ

-- Copycat is transparent to the context.
midP-id : ∀ (B : Game) (C : Arena) (ρ : PEnv (val B ⊸ C)) q →
          midP (val B) B C id-i ρ q ≡ ρ q
midP-id B C ρ (inj₁ b) with ρ (inj₁ b)
... | nothing = refl
... | just r  = refl
midP-id B C ρ (inj₂ c) = refl

-- The category laws, at the contextual relation.
left-id : ∀ {A} {B : Game} (f : A -i> val B) → id-i ∘i f ≈obs f
left-id {A} {B} f (inj₁ a) ρ =
  trans (runP-shift A B (val B) (respond f (inj₁ a)) ρ)
        (runP-cong (respond f (inj₁ a)) (restrictP-id A B ρ))
left-id {A} {B} f (inj₂ b) ρ =
  trans (runP-bind (shift A B (val B) (respond f (inj₂ b))) return ρ)
        (trans (helper (runP (shift A B (val B) (respond f (inj₂ b))) ρ))
               (trans (runP-shift A B (val B) (respond f (inj₂ b)) ρ)
                      (runP-cong (respond f (inj₂ b)) (restrictP-id A B ρ))))
  where
    helper : ∀ (m : Maybe (Answer B b)) → maybe (λ x → just x) nothing m ≡ m
    helper nothing  = refl
    helper (just x) = refl

right-id : ∀ {B : Game} {C} (f : val B -i> C) → f ∘i id-i ≈obs f
right-id {B} {C} f (inj₁ ()) ρ
right-id {B} {C} f (inj₂ c) ρ =
  trans (runP-interact (val B) B C (respond f (inj₂ c)) id-i ρ)
        (runP-cong (respond f (inj₂ c)) (midP-id B C ρ))

restrictP-restrictP : ∀ (A : Arena) (B C′ : Game) (D : Arena)
                      (ρ : PEnv (A ⊸ D)) q →
  restrictP A B (val C′) (restrictP A C′ D ρ) q ≡ restrictP A B D ρ q
restrictP-restrictP A B C′ D ρ (inj₁ a) = refl
restrictP-restrictP A B C′ D ρ (inj₂ ())

midP-shift : ∀ (A : Arena) (B C′ : Game) (D : Arena)
             (f : A -i> val B) (ρ : PEnv (A ⊸ D)) q →
  restrictP (val B) C′ D (midP A B D f ρ) q ≡ midP A B (val C′) f (restrictP A C′ D ρ) q
midP-shift A B C′ D f ρ (inj₁ b) =
  trans (runP-shift A B D (respond f (inj₂ b)) ρ)
        (sym (trans (runP-shift A B (val C′) (respond f (inj₂ b)) (restrictP A C′ D ρ))
                    (runP-cong (respond f (inj₂ b)) (restrictP-restrictP A B C′ D ρ))))
midP-shift A B C′ D f ρ (inj₂ ())

midP-comp : ∀ (A : Arena) (B C′ : Game) (D : Arena)
            (g : val B -i> val C′) (f : A -i> val B) (ρ : PEnv (A ⊸ D)) q →
  midP (val B) C′ D g (midP A B D f ρ) q ≡ midP A C′ D (g ∘i f) ρ q
midP-comp A B C′ D g f ρ (inj₁ c) =
  trans (runP-shift (val B) C′ D (respond g (inj₂ c)) (midP A B D f ρ))
        (trans (runP-cong (respond g (inj₂ c)) (midP-shift A B C′ D f ρ))
               (sym (trans (runP-shift A C′ D (respond (g ∘i f) (inj₂ c)) ρ)
                           (runP-interact A B (val C′) (respond g (inj₂ c)) f
                                          (restrictP A C′ D ρ)))))
midP-comp A B C′ D g f ρ (inj₂ c) = refl

assoc : ∀ {A D} {B C′ : Game}
        (h : val C′ -i> D) (g : val B -i> val C′) (f : A -i> val B) →
        (h ∘i g) ∘i f ≈obs h ∘i (g ∘i f)
assoc {A} {D} {B} {C′} h g f (inj₁ a) ρ =
  trans (runP-shift A B D (respond f (inj₁ a)) ρ)
        (sym (trans (runP-shift A C′ D (shift A B (val C′) (respond f (inj₁ a))) ρ)
                    (trans (runP-shift A B (val C′) (respond f (inj₁ a))
                                       (restrictP A C′ D ρ))
                           (runP-cong (respond f (inj₁ a))
                                      (restrictP-restrictP A B C′ D ρ)))))
assoc {A} {D} {B} {C′} h g f (inj₂ d) ρ =
  trans (runP-interact A B D (interact (val B) C′ D (respond h (inj₂ d)) g) f ρ)
        (trans (runP-interact (val B) C′ D (respond h (inj₂ d)) g (midP A B D f ρ))
               (trans (runP-cong (respond h (inj₂ d)) (midP-comp A B C′ D g f ρ))
                      (sym (runP-interact A C′ D (respond h (inj₂ d)) (g ∘i f) ρ))))

-- The laws at the coarser extensional relation follow.
left-id-ext : ∀ {A} {B : Game} (f : A -i> val B) → id-i ∘i f ≈ext f
left-id-ext {A} {B} f = ≈obs⇒≈ext {A ⊸ val B} {id-i ∘i f} {f} (left-id f)

right-id-ext : ∀ {B : Game} {C} (f : val B -i> C) → f ∘i id-i ≈ext f
right-id-ext {B} {C} f = ≈obs⇒≈ext {val B ⊸ C} {f ∘i id-i} {f} (right-id f)

assoc-ext : ∀ {A D} {B C′ : Game}
            (h : val C′ -i> D) (g : val B -i> val C′) (f : A -i> val B) →
            (h ∘i g) ∘i f ≈ext h ∘i (g ∘i f)
assoc-ext {A} {D} {B} {C′} h g f =
  ≈obs⇒≈ext {A ⊸ D} {(h ∘i g) ∘i f} {h ∘i (g ∘i f)} (assoc h g f)

-- Composition respects contextual equivalence.
midP-cong : ∀ (A : Arena) (B : Game) (C : Arena) {f f′ : A -i> val B} →
            f ≈obs f′ → (ρ : PEnv (A ⊸ C)) → ∀ q →
            midP A B C f ρ q ≡ midP A B C f′ ρ q
midP-cong A B C {f} {f′} ef ρ (inj₁ b) =
  trans (runP-shift A B C (respond f (inj₂ b)) ρ)
        (trans (ef (inj₂ b) (restrictP A B C ρ))
               (sym (runP-shift A B C (respond f′ (inj₂ b)) ρ)))
midP-cong A B C ef ρ (inj₂ c) = refl

∘i-cong : ∀ {A C} {B : Game} {g g′ : val B -i> C} {f f′ : A -i> val B} →
          g ≈obs g′ → f ≈obs f′ → g ∘i f ≈obs g′ ∘i f′
∘i-cong {A} {C} {B} {g} {g′} {f} {f′} eg ef (inj₁ a) ρ =
  trans (runP-shift A B C (respond f (inj₁ a)) ρ)
        (trans (ef (inj₁ a) (restrictP A B C ρ))
               (sym (runP-shift A B C (respond f′ (inj₁ a)) ρ)))
∘i-cong {A} {C} {B} {g} {g′} {f} {f′} eg ef (inj₂ c) ρ =
  trans (runP-interact A B C (respond g (inj₂ c)) f ρ)
        (trans (eg (inj₂ c) (midP A B C f ρ))
               (trans (runP-cong (respond g′ (inj₂ c)) (midP-cong A B C ef ρ))
                      (sym (runP-interact A B C (respond g′ (inj₂ c)) f′ ρ))))
