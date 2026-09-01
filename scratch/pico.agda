-- Gramatika definiranja - Meta Level
-- ----------------------------------

-- Komentari u Agdi koriste "--"

module scratch.pico where

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Data.Sum

-- Definicija sintakse Pico jezika

data PicoSyntax : Set where
  zero one three four five plus minus : PicoSyntax

-- Definicija semantike

-- PICO predstavlja sve moguće statuse
data PICO : Set where
  MkPico : PicoSyntax → PICO

-- Tipovi stanja uređaja

UGAŠEN UPALJEN TCR_WATT : Set
UGAŠEN   = PICO
UPALJEN  = PICO
TCR_WATT = PICO

-- Funkcije

-- Funkcija `ok` radi samo na UPALJEN ili TCR_WATT
ok : {a : Set} → (a ≡ UPALJEN ⊎ a ≡ TCR_WATT) → a → a
ok _ pico = pico -- Semantika: pico 1, implicitno se podrazumijeva

-- -- Prelaz iz ugašenog u upaljeno stanje
-- pali : UGAŠEN → UPALJEN
-- pali (MkPico _) = MkPico five

-- -- Prelaz iz upaljenog u ugašeno
-- gasi : UPALJEN → UGAŠEN
-- gasi (MkPico _) = MkPico five

-- -- Prelaz u TCR_WATT režim
-- tcrWatt : UPALJEN → TCR_WATT
-- tcrWatt (MkPico _) = MkPico four

-- -- Funkcija za povećanje
-- up : {a : Set} → a → a
-- up x = x -- efekt bi bio MkPico plus

-- -- Funkcija za smanjenje
-- down : {a : Set} → a → a
-- down x = x -- efekt bi bio MkPico minus

-- -- Kompozicija funkcija
-- infixr 40 _>>_
-- _>>_ : ∀ {a b c : Set} → (a → b) → (b → c) → a → c
-- f >> g = λ x → g (f x)

-- -- Strukturalna jednakost (izražena kao deklarativna jednakost)

-- -- Ove jednakosti nisu izračunljive u Agdi osim ako eksplicitno dokažemo ih
-- -- pa ih deklariramo kao aksiome

-- -- postulat
-- --   eq1 : pali >> gasi >> pali ≡ pali
-- --   eq2 : gasi >> pali >> gasi ≡ gasi
-- --   eq3 : up >> down ≡ down >> up

-- -- -- Program: Povećavanje snage TCR režima za 2 klika, pa gašenje
-- -- tcrSnagaPlus2 : UGAŠEN → UGAŠEN
-- -- tcrSnagaPlus2 = pali >> tcrWatt >> up >> up >> gasi
