{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Language.Construct.Concatenate
  {c ℓ} (over : Setoid c ℓ)
  where

open import Algebra
open import Cfe.Language over as 𝕃
open import Data.Empty
open import Data.List
open import Data.List.Properties
open import Data.Product as Product
open import Function
open import Level
open import Relation.Binary.PropositionalEquality as ≡
import Relation.Binary.Indexed.Heterogeneous as I

open Setoid over using () renaming (Carrier to C)

module _
  {a aℓ b bℓ}
  (A : Language a aℓ)
  (B : Language b bℓ)
  where

  infix 4 _≈ᶜ_
  infix 4 _∙_

  Concat : List C → Set (c ⊔ a ⊔ b)
  Concat l = ∃[ l₁ ] l₁ ∈ A × ∃[ l₂ ] l₂ ∈ B ×  l₁ ++ l₂ ≡ l

  _≈ᶜ_ : {l₁ l₂ : List C} → REL (Concat l₁) (Concat l₂) (aℓ ⊔ bℓ)
  (_ , l₁∈A , _ , l₂∈B , _) ≈ᶜ (_ , l₁′∈A , _ , l₂′∈B , _) = (≈ᴸ A l₁∈A l₁′∈A) × (≈ᴸ B l₂∈B l₂′∈B)

  _∙_ : Language (c ⊔ a ⊔ b) (aℓ ⊔ bℓ)
  _∙_ = record
    { Carrier = Concat
    ; _≈_ = _≈ᶜ_
    ; isEquivalence = record
      { refl = ≈ᴸ-refl A , ≈ᴸ-refl B
      ; sym = Product.map (≈ᴸ-sym A) (≈ᴸ-sym B)
      ; trans = Product.zip (≈ᴸ-trans A) (≈ᴸ-trans B)
      }
    }

isMonoid : ∀ {a aℓ} → IsMonoid 𝕃._≈_ _∙_ (𝕃.Lift (ℓ ⊔ a) aℓ ｛ε｝)
isMonoid {a} = record
  { isSemigroup = record
    { isMagma = record
      { isEquivalence = ≈-isEquivalence
      ; ∙-cong = λ X≈Y U≈V → record
        { f = λ { (l₁ , l₁∈X , l₂ , l₂∈U , l₁++l₂≡l) → l₁ , _≈_.f X≈Y l₁∈X , l₂ , _≈_.f U≈V l₂∈U , l₁++l₂≡l}
        ; f⁻¹ = λ { (l₁ , l₁∈Y , l₂ , l₂∈V , l₁++l₂≡l) → l₁ , _≈_.f⁻¹ X≈Y l₁∈Y , l₂ , _≈_.f⁻¹ U≈V l₂∈V , l₁++l₂≡l}
        ; cong₁ = λ { (x , y) → _≈_.cong₁ X≈Y x ,  _≈_.cong₁ U≈V y}
        ; cong₂ = λ { (x , y) → _≈_.cong₂ X≈Y x ,  _≈_.cong₂ U≈V y}
        }
      }
    ; assoc = λ X Y Z → record
      { f = λ {l} → (λ { (l₁ , (l₁′ , l₁′∈X , l₂′ , l₂′∈Y , l₁′++l₂′≡l₁) , l₂ , l₂∈Z , l₁++l₂≡l) →
        l₁′ , l₁′∈X , l₂′ ++ l₂ , (l₂′ , l₂′∈Y , l₂ , l₂∈Z , refl) , (begin
          l₁′ ++ l₂′ ++ l₂   ≡˘⟨ ++-assoc l₁′ l₂′ l₂ ⟩
          (l₁′ ++ l₂′) ++ l₂ ≡⟨ cong (_++ l₂) l₁′++l₂′≡l₁ ⟩
          l₁ ++ l₂          ≡⟨ l₁++l₂≡l ⟩
          l                 ∎)})
      ; f⁻¹ = λ {l} → λ { (l₁ , l₁∈X , l₂ , (l₁′ , l₁′∈Y , l₂′ , l₂′∈Z , l₁′++l₂′≡l₂), l₁++l₂≡l) →
        l₁ ++ l₁′ , ( l₁ , l₁∈X , l₁′ , l₁′∈Y , refl) , l₂′ , l₂′∈Z , (begin
          (l₁ ++ l₁′) ++ l₂′ ≡⟨ ++-assoc l₁ l₁′ l₂′ ⟩
          l₁ ++ (l₁′ ++ l₂′) ≡⟨ cong (l₁ ++_) l₁′++l₂′≡l₂ ⟩
          l₁ ++ l₂          ≡⟨ l₁++l₂≡l ⟩
          l                 ∎)}
      ; cong₁ = Product.assocʳ
      ; cong₂ = Product.assocˡ
      }
    }
  ; identity = (λ A → record
    { f = idˡ {a} A
    ; f⁻¹ = λ {l} l∈A → [] , lift refl , l , l∈A , refl
    ; cong₁ = λ {l₁} {l₂} {l₁∈A} {l₂∈A} → idˡ-cong {a} A {l₁} {l₂} {l₁∈A} {l₂∈A}
    ; cong₂ = λ l₁≈l₂ → lift _ , l₁≈l₂
    }) , (λ A → record
    { f = idʳ {a} A
    ; f⁻¹ = λ {l} l∈A → l , l∈A , [] , lift refl , ++-identityʳ l
    ; cong₁ = λ {l₁} {l₂} {l₁∈A} {l₂∈A} → idʳ-cong {a} A {l₁} {l₂} {l₁∈A} {l₂∈A}
    ; cong₂ = λ l₁≈l₂ → l₁≈l₂ , lift _
    })
  }
  where
  open ≡.≡-Reasoning

  idˡ : ∀ {a aℓ} →
        (A : Language (c ⊔ ℓ ⊔ a) aℓ) →
        ∀ {l} →
        l ∈ ((𝕃.Lift (ℓ ⊔ a) aℓ ｛ε｝) ∙ A) →
        l ∈ A
  idˡ _ ([] , _ , l , l∈A , refl) = l∈A

  idˡ-cong : ∀ {a aℓ} →
             (A : Language (c ⊔ ℓ ⊔ a) aℓ) →
             ∀ {l₁ l₂ l₁∈A l₂∈A} →
             ≈ᴸ ((𝕃.Lift (ℓ ⊔ a) aℓ ｛ε｝) ∙ A) {l₁} {l₂} l₁∈A l₂∈A →
             ≈ᴸ A (idˡ {a} A l₁∈A) (idˡ {a} A l₂∈A)
  idˡ-cong _ {l₁∈A = [] , _ , l₁ , l₁∈A , refl} {[] , _ , l₂ , l₂∈A , refl} (_ , l₁≈l₂) = l₁≈l₂

  idʳ : ∀ {a aℓ} →
        (A : Language (c ⊔ ℓ ⊔ a) aℓ) →
        ∀ {l} →
        l ∈ (A ∙ (𝕃.Lift (ℓ ⊔ a) aℓ ｛ε｝)) →
        l ∈ A
  idʳ A (l , l∈A , [] , _ , refl) = ∈-cong A (sym (++-identityʳ l)) l∈A

  idʳ-cong : ∀ {a aℓ} →
             (A : Language (c ⊔ ℓ ⊔ a) aℓ) →
             ∀ {l₁ l₂ l₁∈A l₂∈A} →
             ≈ᴸ (A ∙ (𝕃.Lift (ℓ ⊔ a) aℓ ｛ε｝)) {l₁} {l₂} l₁∈A l₂∈A →
             ≈ᴸ A (idʳ {a} A l₁∈A) (idʳ {a} A l₂∈A)
  idʳ-cong A {l₁∈A = l₁ , l₁∈A , [] , _ , refl} {l₂ , l₂∈A , [] , _ , refl} (l₁≈l₂ , _) =
    ≈ᴸ-cong A (sym (++-identityʳ l₁)) (sym (++-identityʳ l₂)) l₁∈A l₂∈A l₁≈l₂

∙-monotone : ∀ {a aℓ b bℓ} → _∙_ Preserves₂ _≤_ {a} {aℓ} ⟶ _≤_ {b} {bℓ} ⟶ _≤_
∙-monotone X≤Y U≤V = record
  { f = λ {(_ , l₁∈X , _ , l₂∈U , l₁++l₂≡l) → -, X≤Y.f l₁∈X , -, U≤V.f l₂∈U , l₁++l₂≡l}
  ; cong = Product.map X≤Y.cong U≤V.cong
  }
  where
  module X≤Y = _≤_ X≤Y
  module U≤V = _≤_ U≤V
