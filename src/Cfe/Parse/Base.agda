{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (REL; Setoid)

module Cfe.Parse.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over renaming (Carrier to C)

open import Cfe.Language over
open import Data.Empty
open import Data.List hiding (null)
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Maybe
open import Data.Product
open import Level

Parser : Set _
Parser = List C → Maybe (List C)

_▹_ : ∀ {a} → REL Parser (Language a) (c ⊔ ℓ ⊔ a)
p ▹ L = ∀ w → (w′′ : Is-just (p w)) → ∃[ w′ ] (w′ ∈ L × w′ ++ to-witness w′′ ≋ w)

_▸_ : ∀ {a} → REL Parser (Language a) (c ⊔ ℓ ⊔ a)
p ▸ L =
  ∀ {w c w′′} → w ∈ L → (flast L c → ⊥) → (null L → first L c → ⊥) →
  Σ (Is-just (p (w ++ c ∷ w′′))) (λ w′ → to-witness w′ ≋ c ∷ w′′)
