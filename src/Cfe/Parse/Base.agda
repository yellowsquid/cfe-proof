{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Parse.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over renaming (Carrier to C)

open import Cfe.Expression over
open import Data.Fin
open import Data.List

infix 4 _⤇_

data _⤇_ : Expression 0 → List C → Set c where
  Eps : ε ⤇ []
  Char : ∀ {c} → Char c ⤇ [ c ]
  Cat : ∀ {e₁ e₂ l₁ l₂} → e₁ ⤇ l₁ → e₂ ⤇ l₂ → e₁ ∙ e₂ ⤇ l₁ ++ l₂
  Veeˡ : ∀ {e₁ e₂ l} → e₁ ⤇ l → e₁ ∨ e₂ ⤇ l
  Veeʳ : ∀ {e₁ e₂ l} → e₂ ⤇ l → e₁ ∨ e₂ ⤇ l
  Fix : ∀ {e l} → e [ μ e / zero ] ⤇ l → μ e ⤇ l
