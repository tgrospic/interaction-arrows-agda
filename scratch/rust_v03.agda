module scratch.rust_v03 where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Data.List
open import Data.Unit
open import Function using (_∘_)
open import Function

-- Interfaces

record Start (P W : Set) : Set where
  field start : P → W

record Writing (W R : Set) : Set where
  field write : W → R

record Review (R W : Set) : Set where
  field
    reviewBack : R → W
    reviewDone : R → Nat

-- A compositional program

prog2
  : ∀ {P W R : Set}
  → Start P W
  → Writing W R
  → Review R W
  → P → Nat

prog2 startInst writingInst reviewInst p =
  let open Start startInst
      open Writing writingInst
      open Review reviewInst
      w₁ = start p
      r₁ = write w₁
      w₂ = reviewBack r₁
      r₂ = write w₂
  in reviewDone r₂

-- Implementation

-- Define the context state
record Context : Set where
  field
    logs : List String

-- Create an initial default context
emptyCtx : Context
emptyCtx = record { logs = [] }

-- Logging helper
log : String → Context → Context
log msg ctx = record { logs = msg ∷ Context.logs ctx }

-- Implement Start, Writing, Review for Context

startImpl : Start Context Context
startImpl = record
  { start = λ ctx → log "Start" ctx }

writingImpl : Writing Context Context
writingImpl = record
  { write = λ ctx → log "Write >>>" ctx }

reviewImpl : Review Context Context
reviewImpl = record
  { reviewBack = λ ctx → log "Review back <<<" ctx
  ; reviewDone = λ ctx → length (Context.logs (log "Review DONE" ctx))
  }
