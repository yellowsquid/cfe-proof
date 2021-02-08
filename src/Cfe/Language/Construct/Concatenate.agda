{-# OPTIONS --without-K --safe #-}

open import Relation.Binary
import Cfe.Language

module Cfe.Language.Construct.Concatenate
  {c ℓ a aℓ b bℓ} (setoid : Setoid c ℓ)
  (A : Cfe.Language.Language setoid a aℓ)
  (B : Cfe.Language.Language setoid b bℓ)
  where

open import Data.Empty
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid setoid
open import Data.Product as Product
open import Function
open import Level
open import Cfe.Language setoid
open Language

open Setoid setoid renaming (Carrier to C)

infix 4 _≈ᶜ_
infix 4 _∙_

Concat : List C → Set (c ⊔ ℓ ⊔ a ⊔ b)
Concat l = ∃[ l₁ ](l₁ ∈ A × ∃[ l₂ ](l₂ ∈ B × (l₁ ++ l₂ ≋ l)))

_≈ᶜ_ : {l : List C} → Rel (Concat l) (c ⊔ ℓ ⊔ aℓ ⊔ bℓ)
(l₁ , l₁∈A , l₂ , l₂∈B , l₁++l₂) ≈ᶜ (l₁′ , l₁′∈A , l₂′ , l₂′∈B , l₁′++l₂′) =
    ∃[ l₁≋l₁′ ](_≈ᴸ_ A (⤖ A l₁≋l₁′ l₁∈A) l₁′∈A)
  × ∃[ l₂≋l₂′ ](_≈ᴸ_ B (⤖ B l₂≋l₂′ l₂∈B) l₂′∈B)

⤖ᶜ : {l₁ l₂ : List C} → l₁ ≋ l₂ → Concat l₁ → Concat l₂
⤖ᶜ l₁≋l₂ = map₂ (map₂ (map₂ (map₂ (flip ≋-trans l₁≋l₂))))

_∙_ : Language (c ⊔ ℓ ⊔ a ⊔ b) (c ⊔ ℓ ⊔ aℓ ⊔ bℓ)
_∙_ = record
  { 𝕃 = Concat
  ; _≈ᴸ_ = _≈ᶜ_
  ; ⤖ = ⤖ᶜ
  ; isLanguage = record
    { ≈ᴸ-isEquivalence = record
      { refl = (≋-refl , ⤖-refl A) , (≋-refl , ⤖-refl B)
      ; sym = Product.map (Product.map ≋-sym (⤖-sym A))
                          (Product.map ≋-sym (⤖-sym B))
      ; trans = Product.zip (Product.zip ≋-trans (⤖-trans A))
                            (Product.zip ≋-trans (⤖-trans B))
      }
    ; ⤖-cong = id
    ; ⤖-bijective = λ {_} {_} {l₁≋l₂} → id , λ l₂∈𝕃 →
        ⤖ᶜ (≋-sym l₁≋l₂) l₂∈𝕃 , (≋-refl , ⤖-refl A) , (≋-refl , ⤖-refl B)
    ; ⤖-refl = (≋-refl , ⤖-refl A) , (≋-refl , ⤖-refl B)
    ; ⤖-sym = Product.map (Product.map ≋-sym (⤖-sym A))
                          (Product.map ≋-sym (⤖-sym B))
    ; ⤖-trans = Product.zip (Product.zip ≋-trans (⤖-trans A))
                            (Product.zip ≋-trans (⤖-trans B))
    }
  }
