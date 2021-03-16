{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Language.Construct.Concatenate
  {c ℓ} (over : Setoid c ℓ)
  where

open import Algebra
open import Cfe.Language over as 𝕃
open import Data.Empty
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.List.Properties
open import Data.Product as Product
open import Function
open import Level
open import Relation.Binary.PropositionalEquality as ≡
import Relation.Binary.Indexed.Heterogeneous as I

open Setoid over using () renaming (Carrier to C)

module _
  {a b}
  (A : Language a)
  (B : Language b)
  where

  module A = Language A
  module B = Language B

  infix 4 _∙_

  Concat : List C → Set (c ⊔ ℓ ⊔ a ⊔ b)
  Concat l = ∃[ l₁ ] l₁ ∈ A × ∃[ l₂ ] l₂ ∈ B × l₁ ++ l₂ ≋ l

  _∙_ : Language (c ⊔ ℓ ⊔ a ⊔ b)
  _∙_ = record
    { 𝕃 = Concat
    ; ∈-resp-≋ = λ { l≋l′ (_ , l₁∈A , _ , l₂∈B , eq) → -, l₁∈A , -, l₂∈B , ≋-trans eq l≋l′
      }
    }

isMonoid : ∀ {a} → IsMonoid 𝕃._≈_ _∙_ (𝕃.Lift (ℓ ⊔ a) ｛ε｝)
isMonoid {a} = record
  { isSemigroup = record
    { isMagma = record
      { isEquivalence = ≈-isEquivalence
      ; ∙-cong = λ X≈Y U≈V → record
        { f = λ { (_ , l₁∈X , _ , l₂∈U , eq) → -, _≈_.f X≈Y l₁∈X , -, _≈_.f U≈V l₂∈U , eq }
        ; f⁻¹ = λ { (_ , l₁∈Y , _ , l₂∈V , eq) → -, _≈_.f⁻¹ X≈Y l₁∈Y , -, _≈_.f⁻¹ U≈V l₂∈V , eq }
        }
      }
    ; assoc = λ X Y Z → record
      { f = λ {l} → λ { (l₁₂ , (l₁ , l₁∈X , l₂ , l₂∈Y , eq₁) , l₃ , l₃∈Z , eq₂) →
        -, l₁∈X , -, (-, l₂∈Y , -, l₃∈Z , ≋-refl) , (begin
          l₁ ++ l₂ ++ l₃ ≡˘⟨ ++-assoc l₁ l₂ l₃ ⟩
          (l₁ ++ l₂) ++ l₃ ≈⟨ ++⁺ eq₁ ≋-refl ⟩
          l₁₂ ++ l₃ ≈⟨ eq₂ ⟩
          l ∎) }
      ; f⁻¹ = λ {l} → λ { (l₁ , l₁∈X , l₂₃ , (l₂ , l₂∈Y , l₃ , l₃∈Z , eq₁) , eq₂) →
        -, (-, l₁∈X , -, l₂∈Y , ≋-refl) , -, l₃∈Z , (begin
          (l₁ ++ l₂) ++ l₃ ≡⟨ ++-assoc l₁ l₂ l₃ ⟩
          l₁ ++ l₂ ++ l₃ ≈⟨ ++⁺ ≋-refl eq₁ ⟩
          l₁ ++ l₂₃ ≈⟨ eq₂ ⟩
          l ∎) }
      }
    }
  ; identity = (λ X → record
    { f = λ { ([] , _ , _ , l₂∈X , eq) → Language.∈-resp-≋ X eq l₂∈X }
    ; f⁻¹ = λ l∈X → -, lift refl , -, l∈X , ≋-refl
    }) , (λ X → record
    { f = λ { (l₁ , l₁∈X , [] , _ , eq) → Language.∈-resp-≋ X (≋-trans (≋-reflexive (sym (++-identityʳ l₁))) eq) l₁∈X }
    ; f⁻¹ = λ {l} l∈X → -, l∈X , -, lift refl , ≋-reflexive (++-identityʳ l)
    })
  }
  where
  open import Relation.Binary.Reasoning.Setoid ≋-setoid

∙-mono : ∀ {a b} → _∙_ Preserves₂ _≤_ {a} ⟶ _≤_ {b} ⟶ _≤_
∙-mono X≤Y U≤V = record
  { f = λ {(_ , l₁∈X , _ , l₂∈U , eq) → -, X≤Y.f l₁∈X , -, U≤V.f l₂∈U , eq}
  }
  where
  module X≤Y = _≤_ X≤Y
  module U≤V = _≤_ U≤V
