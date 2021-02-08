{-# OPTIONS --without-K --safe #-}

open import Relation.Binary
import Cfe.Language

module Cfe.Language.Construct.Union
  {c ℓ a aℓ b bℓ} (setoid : Setoid c ℓ)
  (A : Cfe.Language.Language setoid a aℓ)
  (B : Cfe.Language.Language setoid b bℓ)
  where

open import Data.Empty
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid setoid
open import Data.Product as Product
open import Data.Sum as Sum
open import Function
open import Level
open import Cfe.Language setoid
open Language

open Setoid setoid renaming (Carrier to C)

infix 4 _≈ᵁ_
infix 4 _∪_

Union : List C → Set (a ⊔ b)
Union l = 𝕃 A l ⊎ 𝕃 B l

_≈ᵁ_ : {l : List C} → Rel (Union l) (aℓ ⊔ bℓ)
(inj₁ x) ≈ᵁ (inj₁ y) = Lift bℓ (_≈ᴸ_ A x y)
(inj₁ _) ≈ᵁ (inj₂ _) = Lift (aℓ ⊔ bℓ) ⊥
(inj₂ _) ≈ᵁ (inj₁ _) = Lift (aℓ ⊔ bℓ) ⊥
(inj₂ x) ≈ᵁ (inj₂ y) = Lift aℓ (_≈ᴸ_ B x y)

⤖ᵁ : {l₁ l₂ : List C} → l₁ ≋ l₂ → Union l₁ → Union l₂
⤖ᵁ l₁≋l₂ = Sum.map (⤖ A l₁≋l₂) (⤖ B l₁≋l₂)

_∪_ : Language (a ⊔ b) (aℓ ⊔ bℓ)
_∪_ = record
  { 𝕃 = Union
  ; _≈ᴸ_ = _≈ᵁ_
  ; ⤖ = ⤖ᵁ
  ; isLanguage = record
    { ≈ᴸ-isEquivalence = record
      { refl = λ {x} → case x return (λ x → _≈ᵁ_ x x) of λ
        { (inj₁ x) → lift (≈ᴸ-refl A)
        ; (inj₂ y) → lift (≈ᴸ-refl B)
        }
      ; sym = λ {x} {y} x≈ᵁy →
        case (∃[ x ](∃[ y ](x ≈ᵁ y)) ∋ x , y , x≈ᵁy)
        return (λ (x , y , _) → y ≈ᵁ x) of λ
          { (inj₁ x , inj₁ y , lift x≈ᵁy) → lift (≈ᴸ-sym A x≈ᵁy)
          ; (inj₂ y₁ , inj₂ y , lift x≈ᵁy) → lift (≈ᴸ-sym B x≈ᵁy)
          }
      ; trans = λ {i} {j} {k} i≈ᵁj j≈ᵁk →
        case ∃[ i ](∃[ j ](∃[ k ](i ≈ᵁ j × j ≈ᵁ k))) ∋ i , j , k , i≈ᵁj , j≈ᵁk
        return (λ (i , _ , k , _) → i ≈ᵁ k) of λ
          { (inj₁ _ , inj₁ _ , inj₁ _ , lift x≈ᵁy , lift y≈ᵁz) →
            lift (≈ᴸ-trans A x≈ᵁy y≈ᵁz)
          ; (inj₂ _ , inj₂ _ , inj₂ _ , lift x≈ᵁy , lift y≈ᵁz) →
            lift (≈ᴸ-trans B x≈ᵁy y≈ᵁz)
          }
      }
    ; ⤖-cong = λ {_} {_} {l₁≋l₂} {x} {y} x≈ᵁy →
      case ∃[ x ](∃[ y ](x ≈ᵁ y)) ∋ x , y , x≈ᵁy
      return (λ (x , y , _) → (_≈ᵁ_ on ⤖ᵁ l₁≋l₂) x y) of λ
        { (inj₁ x , inj₁ y , lift x≈ᵁy) → lift (⤖-cong A x≈ᵁy)
        ; (inj₂ x , inj₂ y , lift x≈ᵁy) → lift (⤖-cong B x≈ᵁy)
        }
    ; ⤖-bijective = λ {_} {_} {l₁≋l₂} →
      ( λ {x} {y} x≈ᵁy →
        case ∃[ x ](∃[ y ]((_≈ᵁ_ on ⤖ᵁ l₁≋l₂) x y)) ∋ x , y , x≈ᵁy
        return (λ (x , y , _) → x ≈ᵁ y) of λ
          { (inj₁ x , inj₁ y , lift x≈ᵁy) → lift (⤖-injective A x≈ᵁy)
          ; (inj₂ x , inj₂ y , lift x≈ᵁy) → lift (⤖-injective B x≈ᵁy)
          })
    , ( λ
        { (inj₁ x) → Product.map inj₁ lift (⤖-surjective A x)
        ; (inj₂ x) → Product.map inj₂ lift (⤖-surjective B x)
        })
    ; ⤖-refl = λ {_} {x} → case x return (λ x → ⤖ᵁ ≋-refl x ≈ᵁ x) of λ
      { (inj₁ x) → lift (⤖-refl A)
      ; (inj₂ y) → lift (⤖-refl B)
      }
    ; ⤖-sym = λ {_} {_} {x} {y} {l₁≋l₂} x≈ᵁy →
      case ∃[ x ](∃[ y ](⤖ᵁ l₁≋l₂ x ≈ᵁ y)) ∋ x , y , x≈ᵁy
      return (λ (x , y , _) → ⤖ᵁ (≋-sym l₁≋l₂) y ≈ᵁ x) of λ
        { (inj₁ x , inj₁ y , lift x≈ᵁy) → lift (⤖-sym A x≈ᵁy)
        ; (inj₂ x , inj₂ y , lift x≈ᵁy) → lift (⤖-sym B x≈ᵁy)
        }
    ; ⤖-trans = λ {_} {_} {_} {x} {y} {z} {l₁≋l₂} {l₂≋l₃} x≈ᵁy y≈ᵁz →
      case (∃[ x ](∃[ y ](∃[ z ]((⤖ᵁ l₁≋l₂ x ≈ᵁ y) × (⤖ᵁ l₂≋l₃ y ≈ᵁ z))))) ∋
           x , y , z , x≈ᵁy , y≈ᵁz
      return (λ (x , _ , z , _ , _) → ⤖ᵁ (≋-trans l₁≋l₂ l₂≋l₃) x ≈ᵁ z) of λ
        { (inj₁ x , inj₁ y , inj₁ z , lift x≈ᵁy , lift y≈ᵁz) →
          lift (⤖-trans A x≈ᵁy y≈ᵁz)
        ; (inj₂ x , inj₂ y , inj₂ z , lift x≈ᵁy , lift y≈ᵁz) →
          lift (⤖-trans B x≈ᵁy y≈ᵁz)
        }
    }
  }
