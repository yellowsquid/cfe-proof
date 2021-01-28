{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Construct.InducedPoset
  {a ℓ} {A : Set a}
  (_≤_ : Rel A ℓ)
  where

open import Algebra
open import Data.Product
open import Function
open import Level

_≈_ : Rel A ℓ
_≈_ = _≤_ -×- flip _≤_

AntiCongruent₁ : Op₁ A → Set (a ⊔ ℓ)
AntiCongruent₁ f = f Preserves _≤_ ⟶ flip _≤_

AntiCongruent₂ : Op₂ A → Set (a ⊔ ℓ)
AntiCongruent₂ ∙ = ∙ Preserves₂ _≤_ ⟶ _≤_ ⟶ flip _≤_

LeftAntiCongruent : Op₂ A → Set (a ⊔ ℓ)
LeftAntiCongruent _∙_ = ∀ {x} → (x ∙_) Preserves _≤_ ⟶ flip _≤_

RightAntiCongruent : Op₂ A → Set (a ⊔ ℓ)
RightAntiCongruent _∙_ = ∀ {x} → (_∙ x) Preserves _≤_ ⟶ flip _≤_

InducedPoset : Reflexive _≤_ → Transitive _≤_ → Poset a ℓ ℓ
InducedPoset ≤-refl ≤-trans = record
  { _≈_ = _≈_
  ; _≤_ = _≤_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = record
        { refl = ≤-refl , ≤-refl
        ; sym = swap
        ; trans = zip ≤-trans (flip ≤-trans)
        }
      ; reflexive = proj₁
      ; trans = ≤-trans
      }
    ; antisym = _,_
    }
  }

≤-cong→≈-cong : {f : Op₁ A} → Congruent₁ _≤_ f → Congruent₁ _≈_ f
≤-cong→≈-cong ≤-cong = map ≤-cong ≤-cong

≤-anticong→≈-cong : {f : Op₁ A} → AntiCongruent₁ f → Congruent₁ _≈_ f
≤-anticong→≈-cong ≤-anticong = swap ∘ map ≤-anticong ≤-anticong

≤-cong₂→≈-cong₂ : {∙ : Op₂ A} → Congruent₂ _≤_ ∙ → Congruent₂ _≈_ ∙
≤-cong₂→≈-cong₂ ≤-cong₂ = zip ≤-cong₂ ≤-cong₂

≤-anticong₂→≈-cong₂ : {∙ : Op₂ A} → AntiCongruent₂ ∙ → Congruent₂ _≈_ ∙
≤-anticong₂→≈-cong₂ ≤-anticong₂ = swap ∘₂ zip ≤-anticong₂ ≤-anticong₂

≤-congₗ→≈-congₗ : {∙ : Op₂ A} → LeftCongruent _≤_ ∙ → LeftCongruent _≈_ ∙
≤-congₗ→≈-congₗ ≤-congₗ = map ≤-congₗ ≤-congₗ

≤-anticongₗ→≈-congₗ : {∙ : Op₂ A} → LeftAntiCongruent ∙ → LeftCongruent _≈_ ∙
≤-anticongₗ→≈-congₗ ≤-anticongₗ = swap ∘ map ≤-anticongₗ ≤-anticongₗ

≤-congᵣ→≈-congᵣ : {∙ : Op₂ A} → RightCongruent _≤_ ∙ → RightCongruent _≈_ ∙
≤-congᵣ→≈-congᵣ ≤-congᵣ = map ≤-congᵣ ≤-congᵣ

≤-anticongᵣ→≈-congᵣ : {∙ : Op₂ A} → RightAntiCongruent ∙ → RightCongruent _≈_ ∙
≤-anticongᵣ→≈-congᵣ ≤-anticongᵣ = swap ∘ map ≤-anticongᵣ ≤-anticongᵣ
