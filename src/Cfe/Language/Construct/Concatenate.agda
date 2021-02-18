{-# OPTIONS --without-K --safe #-}

open import Relation.Binary
import Cfe.Language

module Cfe.Language.Construct.Concatenate
  {c ℓ a aℓ b bℓ} (over : Setoid c ℓ)
  (A : Cfe.Language.Language over a aℓ)
  (B : Cfe.Language.Language over b bℓ)
  where

open import Data.Empty
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Product as Product
open import Function
open import Level
open import Cfe.Language over

open Setoid over renaming (Carrier to C)

infix 4 _≈ᶜ_
infix 4 _∙_

Concat : List C → Set (c ⊔ ℓ ⊔ a ⊔ b)
Concat l = ∃[ l₁ ] l₁ ∈ A × ∃[ l₂ ] l₂ ∈ B ×  l₁ ++ l₂ ≋ l

_≈ᶜ_ : {l₁ l₂ : List C} → REL (Concat l₁) (Concat l₂) (aℓ ⊔ bℓ)
(_ , l₁∈A , _ , l₂∈B , _) ≈ᶜ (_ , l₁′∈A , _ , l₂′∈B , _) = (≈ᴸ A l₁∈A l₁′∈A) × (≈ᴸ B l₂∈B l₂′∈B)

_∙_ : Language (c ⊔ ℓ ⊔ a ⊔ b) (aℓ ⊔ bℓ)
_∙_ = record
  { Carrier = Concat
  ; _≈_ = _≈ᶜ_
  ; isEquivalence = record
    { refl = ≈ᴸ-refl A , ≈ᴸ-refl B
    ; sym = Product.map (≈ᴸ-sym A) (≈ᴸ-sym B)
    ; trans = Product.zip (≈ᴸ-trans A) (≈ᴸ-trans B)
    }
  }
