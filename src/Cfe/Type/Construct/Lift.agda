{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Type.Construct.Lift
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Type over
open import Level as L hiding (Lift)
open import Function

Lift : ∀ {fℓ₁ lℓ₁} fℓ₂ lℓ₂ → Type fℓ₁ lℓ₁ → Type (fℓ₁ ⊔ fℓ₂) (lℓ₁ ⊔ lℓ₂)
Lift fℓ₂ lℓ₂ τ = record
  { Null = τ.Null
  ; First = L.Lift fℓ₂ ∘ τ.First
  ; Flast = L.Lift lℓ₂ ∘ τ.Flast
  }
  where
  module τ = Type τ
