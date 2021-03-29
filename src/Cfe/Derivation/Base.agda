{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Derivation.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over renaming (Carrier to C; _≈_ to _∼_)

open import Cfe.Expression over hiding (_≋_)
open import Data.Fin
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid over
open import Level using (_⊔_)

infix 4 _⤇_

data _⤇_ : Expression 0 → List C → Set (c ⊔ ℓ) where
  Eps : ε ⤇ []
  Char : ∀ {c y} → c ∼ y → Char c ⤇ [ y ]
  Cat : ∀ {e₁ e₂ l₁ l₂ l} → e₁ ⤇ l₁ → e₂ ⤇ l₂ → l₁ ++ l₂ ≋ l → e₁ ∙ e₂ ⤇ l
  Veeˡ : ∀ {e₁ e₂ l} → e₁ ⤇ l → e₁ ∨ e₂ ⤇ l
  Veeʳ : ∀ {e₁ e₂ l} → e₂ ⤇ l → e₁ ∨ e₂ ⤇ l
  Fix : ∀ {e l} → e [ μ e / zero ] ⤇ l → μ e ⤇ l
