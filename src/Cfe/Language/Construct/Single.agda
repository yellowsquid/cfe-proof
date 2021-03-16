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
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Product as Product
open import Data.Unit
open import Level

｛_｝ : C → Language (c ⊔ ℓ)
｛ c ｝ = record
  { 𝕃 = [ c ] ≋_
  ; ∈-resp-≋ = λ l₁≋l₂ l₁∈｛c｝ → ≋-trans l₁∈｛c｝ l₁≋l₂
  }

xy∉｛c｝ : ∀ c x y l → x ∷ y ∷ l ∉ ｛ c ｝
xy∉｛c｝ c x y l (_ ∷ ())
