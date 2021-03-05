{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Language.Construct.Union
  {c ℓ} (over : Setoid c ℓ)
  where

open import Algebra
open import Data.Empty
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Product as Product
open import Data.Sum as Sum
open import Function
open import Level
open import Cfe.Language over as 𝕃 hiding (Lift)

open Setoid over renaming (Carrier to C)

module _
  {a aℓ b bℓ}
  (A : Language a aℓ)
  (B : Language b bℓ)
  where

  infix 4 _≈ᵁ_
  infix 4 _∪_

  Union : List C → Set (a ⊔ b)
  Union l = l ∈ A ⊎ l ∈ B

  data _≈ᵁ_ : {l₁ l₂ : List C} → REL (Union l₁) (Union l₂) (c ⊔ a ⊔ aℓ ⊔ b ⊔ bℓ) where
    A≈A : ∀ {l₁ l₂ x y} → ≈ᴸ A {l₁} {l₂} x y → (inj₁ x) ≈ᵁ (inj₁ y)
    B≈B : ∀ {l₁ l₂ x y} → ≈ᴸ B {l₁} {l₂} x y → (inj₂ x) ≈ᵁ (inj₂ y)

  _∪_ : Language (a ⊔ b) (c ⊔ a ⊔ aℓ ⊔ b ⊔ bℓ)
  _∪_ = record
    { Carrier = Union
    ; _≈_ = _≈ᵁ_
    ; isEquivalence = record
      { refl = λ {_} {x} → case x return (λ x → x ≈ᵁ x) of λ { (inj₁ x) → A≈A (≈ᴸ-refl A) ; (inj₂ y) → B≈B (≈ᴸ-refl B)}
      ; sym = λ { (A≈A x) → A≈A (≈ᴸ-sym A x) ; (B≈B x) → B≈B (≈ᴸ-sym B x)}
      ; trans = λ { (A≈A x) (A≈A y) → A≈A (≈ᴸ-trans A x y) ; (B≈B x) (B≈B y) → B≈B (≈ᴸ-trans B x y) }
      }
    }

isCommutativeMonoid : ∀ {a aℓ} → IsCommutativeMonoid 𝕃._≈_ _∪_ (𝕃.Lift a (c ⊔ a ⊔ aℓ) ∅)
isCommutativeMonoid = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = ≈-isEquivalence
        ; ∙-cong = λ X≈Y U≈V → record
          { f = Sum.map (_≈_.f X≈Y) (_≈_.f U≈V)
          ; f⁻¹ = Sum.map (_≈_.f⁻¹ X≈Y) (_≈_.f⁻¹ U≈V)
          ; cong₁ = λ { (A≈A x) → A≈A (_≈_.cong₁ X≈Y x) ; (B≈B x) → B≈B (_≈_.cong₁ U≈V x) }
          ; cong₂ = λ { (A≈A x) → A≈A (_≈_.cong₂ X≈Y x) ; (B≈B x) → B≈B (_≈_.cong₂ U≈V x) }
          }
        }
      ; assoc = λ A B C → record
        { f = Sum.assocʳ
        ; f⁻¹ = Sum.assocˡ
        ; cong₁ = λ { (A≈A (A≈A x)) → A≈A x ; (A≈A (B≈B x)) → B≈B (A≈A x) ; (B≈B x) → B≈B (B≈B x) }
        ; cong₂ = λ { (A≈A x) → A≈A (A≈A x) ; (B≈B (A≈A x)) → A≈A (B≈B x) ; (B≈B (B≈B x)) → B≈B x }
        }
      }
    ; identity = (λ A → record
      { f = λ { (inj₂ x) → x }
      ; f⁻¹ = inj₂
      ; cong₁ = λ { (B≈B x) → x }
      ; cong₂ = B≈B
      }) , (λ A → record
      { f = λ { (inj₁ x) → x }
      ; f⁻¹ = inj₁
      ; cong₁ = λ { (A≈A x) → x }
      ; cong₂ = A≈A
      })
    }
  ; comm = λ A B → record
    { f = Sum.swap
    ; f⁻¹ = Sum.swap
    ; cong₁ = λ { (A≈A x) → B≈B x ; (B≈B x) → A≈A x }
    ; cong₂ = λ { (A≈A x) → B≈B x ; (B≈B x) → A≈A x }
    }
  }

∪-monotone : ∀ {a aℓ b bℓ} → _∪_ Preserves₂ _≤_ {a} {aℓ} ⟶ _≤_ {b} {bℓ} ⟶ _≤_
∪-monotone X≤Y U≤V = record
  { f = Sum.map X≤Y.f U≤V.f
  ; cong = λ { (A≈A l₁≈l₂) → A≈A (X≤Y.cong l₁≈l₂) ; (B≈B l₁≈l₂) → B≈B (U≤V.cong l₁≈l₂)}
  }
  where
  module X≤Y = _≤_ X≤Y
  module U≤V = _≤_ U≤V
