{-# OPTIONS --without-K --safe #-}

open import Function
open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡

module Cfe.Language.Construct.Single
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over renaming (Carrier to C)

open import Cfe.Language over hiding (_≈_)
open import Data.List
open import Data.Product as Product
open import Data.Unit
open import Level

｛_｝ : C → Language (c ⊔ ℓ) 0ℓ
｛ c ｝ = record
  { Carrier = λ l → ∃[ a ] (l ≡.≡ [ a ] × a ≈ c)
  ; _≈_ = λ _ _ → ⊤
  ; isEquivalence = record
    { refl = tt
    ; sym = λ _ → tt
    ; trans = λ _ _ → tt
    }
  }
