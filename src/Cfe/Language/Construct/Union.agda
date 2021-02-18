{-# OPTIONS --without-K --safe #-}

open import Relation.Binary
import Cfe.Language

module Cfe.Language.Construct.Union
  {c ℓ a aℓ b bℓ} (over : Setoid c ℓ)
  (A : Cfe.Language.Language over a aℓ)
  (B : Cfe.Language.Language over b bℓ)
  where

open import Data.Empty
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Product as Product
open import Data.Sum as Sum
open import Function
open import Level
open import Cfe.Language over hiding (Lift)

open Setoid over renaming (Carrier to C)

infix 4 _≈ᵁ_
infix 4 _∪_

Union : List C → Set (a ⊔ b)
Union l = l ∈ A ⊎ l ∈ B

_≈ᵁ_ : {l₁ l₂ : List C} → REL (Union l₁) (Union l₂) (aℓ ⊔ bℓ)
(inj₁ x) ≈ᵁ (inj₁ y) = Lift bℓ (≈ᴸ A x y)
(inj₁ _) ≈ᵁ (inj₂ _) = Lift (aℓ ⊔ bℓ) ⊥
(inj₂ _) ≈ᵁ (inj₁ _) = Lift (aℓ ⊔ bℓ) ⊥
(inj₂ x) ≈ᵁ (inj₂ y) = Lift aℓ (≈ᴸ B x y)

_∪_ : Language (a ⊔ b) (aℓ ⊔ bℓ)
_∪_ = record
  { Carrier = Union
  ; _≈_ = _≈ᵁ_
  ; isEquivalence = record
    { refl = λ {_} {x} → case x return (λ x → x ≈ᵁ x) of λ
      { (inj₁ x) → lift (≈ᴸ-refl A)
      ; (inj₂ y) → lift (≈ᴸ-refl B)
      }
    ; sym = λ {_} {_} {x} {y} x≈ᵁy →
      case (∃[ x ] ∃[ y ] x ≈ᵁ y ∋ x , y , x≈ᵁy)
      return (λ (x , y , _) → y ≈ᵁ x) of λ
        { (inj₁ x , inj₁ y , lift x≈ᵁy) → lift (≈ᴸ-sym A x≈ᵁy)
        ; (inj₂ y₁ , inj₂ y , lift x≈ᵁy) → lift (≈ᴸ-sym B x≈ᵁy)
        }
    ; trans = λ {_} {_} {_} {x} {y} {z} x≈ᵁy y≈ᵁz →
      case ∃[ x ] ∃[ y ] ∃[ z ] x ≈ᵁ y × y ≈ᵁ z ∋ x , y , z , x≈ᵁy , y≈ᵁz
      return (λ (x , _ , z , _) → x ≈ᵁ z) of λ
        { (inj₁ _ , inj₁ _ , inj₁ _ , lift x≈ᵁy , lift y≈ᵁz) →
          lift (≈ᴸ-trans A x≈ᵁy y≈ᵁz)
        ; (inj₂ _ , inj₂ _ , inj₂ _ , lift x≈ᵁy , lift y≈ᵁz) →
          lift (≈ᴸ-trans B x≈ᵁy y≈ᵁz)
        }
    }
  }
