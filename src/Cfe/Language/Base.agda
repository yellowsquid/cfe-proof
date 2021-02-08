{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Language.Base
  {c ℓ} (setoid : Setoid c ℓ)
  where

open Setoid setoid renaming (Carrier to A)

open import Data.Empty
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid setoid
open import Data.Product as Product
open import Function
open import Level
import Relation.Binary.PropositionalEquality as ≡
import Relation.Binary.Indexed.Heterogeneous as I

record IsLanguage {a aℓ} (𝕃 : List A → Set a) (_≈ᴸ_ : ∀ {l} → Rel (𝕃 l) aℓ) (⤖ : ∀ {l₁ l₂} → l₁ ≋ l₂ → 𝕃 l₁ → 𝕃 l₂) : Set (c ⊔ ℓ ⊔ a ⊔ aℓ) where
  field
    ≈ᴸ-isEquivalence : ∀ {l} → IsEquivalence (_≈ᴸ_ {l})
    ⤖-cong : ∀ {l₁ l₂ l₁≋l₂} → (⤖ l₁≋l₂) Preserves _≈ᴸ_ {l₁} ⟶ _≈ᴸ_ {l₂}
    ⤖-bijective : ∀ {l₁ l₂ l₁≋l₂} → Bijective (_≈ᴸ_ {l₁}) (_≈ᴸ_ {l₂}) (⤖ l₁≋l₂)
    ⤖-refl : ∀ {l l∈𝕃} → (⤖ {l} ≋-refl l∈𝕃) ≈ᴸ l∈𝕃
    ⤖-sym : ∀ {l₁ l₂ l₁∈𝕃 l₂∈𝕃 l₁≋l₂}
          → (⤖ {l₁} l₁≋l₂ l₁∈𝕃) ≈ᴸ l₂∈𝕃
          → (⤖ {l₂} (≋-sym l₁≋l₂) l₂∈𝕃) ≈ᴸ l₁∈𝕃
    ⤖-trans : ∀ {l₁ l₂ l₃ l₁∈𝕃 l₂∈𝕃 l₃∈𝕃 l₁≋l₂ l₂≋l₃}
            → (⤖ {l₁} l₁≋l₂ l₁∈𝕃) ≈ᴸ l₂∈𝕃
            → (⤖ {l₂} l₂≋l₃ l₂∈𝕃) ≈ᴸ l₃∈𝕃
            → (⤖ {_} {l₃} (≋-trans l₁≋l₂ l₂≋l₃) l₁∈𝕃) ≈ᴸ l₃∈𝕃

  ≈ᴸ-refl : ∀ {l} → Reflexive (_≈ᴸ_ {l})
  ≈ᴸ-refl = IsEquivalence.refl ≈ᴸ-isEquivalence

  ≈ᴸ-sym : ∀ {l} → Symmetric (_≈ᴸ_ {l})
  ≈ᴸ-sym = IsEquivalence.sym ≈ᴸ-isEquivalence

  ≈ᴸ-trans : ∀ {l} → Transitive (_≈ᴸ_ {l})
  ≈ᴸ-trans = IsEquivalence.trans ≈ᴸ-isEquivalence

  ≈ᴸ-reflexive : ∀ {l} → ≡._≡_ ⇒ (_≈ᴸ_ {l})
  ≈ᴸ-reflexive = IsEquivalence.reflexive ≈ᴸ-isEquivalence

  ⤖-injective : ∀ {l₁ l₂ l₁≋l₂} → Injective (_≈ᴸ_ {l₁}) (_≈ᴸ_ {l₂}) (⤖ l₁≋l₂)
  ⤖-injective = proj₁ ⤖-bijective

  ⤖-surjective : ∀ {l₁ l₂ l₁≋l₂} → Surjective (_≈ᴸ_ {l₁}) (_≈ᴸ_ {l₂}) (⤖ {l₁} l₁≋l₂)
  ⤖-surjective = proj₂ ⤖-bijective

  ⤖-isIndexedEquivalence : I.IsIndexedEquivalence 𝕃 (λ l₁∈𝕃 l₂∈𝕃 → ∃[ l₁≋l₂ ] ((⤖ l₁≋l₂ l₁∈𝕃) ≈ᴸ l₂∈𝕃))
  ⤖-isIndexedEquivalence = record
    { refl = ≋-refl , ⤖-refl
    ; sym = Product.map ≋-sym ⤖-sym
    ; trans = Product.zip ≋-trans ⤖-trans
    }

  ⤖-reflexive : ∀ {l l∈𝕃 l∈𝕃′} → l∈𝕃 ≡.≡ l∈𝕃′ → ∃[ l≋l ]((⤖ {l} l≋l l∈𝕃) ≈ᴸ l∈𝕃′)
  ⤖-reflexive = I.IsIndexedEquivalence.reflexive ⤖-isIndexedEquivalence

record Language a aℓ : Set (c ⊔ ℓ ⊔ suc (a ⊔ aℓ)) where
  infix 4 _≈ᴸ_
  field
    𝕃 : List A → Set a
    _≈ᴸ_ : ∀ {l} → Rel (𝕃 l) aℓ
    ⤖ : ∀ {l₁ l₂} → l₁ ≋ l₂ → 𝕃 l₁ → 𝕃 l₂
    isLanguage : IsLanguage 𝕃 _≈ᴸ_ ⤖

  open IsLanguage isLanguage public

open Language

infix 4 _∈_

_∈_ : ∀ {a aℓ} → List A → Language a aℓ → Set a
l ∈ A = 𝕃 A l

∅ : Language 0ℓ 0ℓ
∅ = record
  { 𝕃 = const ⊥
  ; _≈ᴸ_ = ≡._≡_
  ; ⤖ = const id
  ; isLanguage = record
    { ≈ᴸ-isEquivalence = ≡.isEquivalence
    ; ⤖-cong = ≡.cong id
    ; ⤖-bijective = (λ {x} → ⊥-elim x) , (λ ())
    ; ⤖-refl = λ {_} {l∈𝕃} → ⊥-elim l∈𝕃
    ; ⤖-sym = λ {_} {_} {l₁∈𝕃} → ⊥-elim l₁∈𝕃
    ; ⤖-trans = λ {_} {_} {_} {l₁∈𝕃} → ⊥-elim l₁∈𝕃
    }
  }

⦃ε⦄ : Language (c ⊔ ℓ) (c ⊔ ℓ)
⦃ε⦄ = record
  { 𝕃 = [] ≋_
  ; _≈ᴸ_ = ≡._≡_
  ; ⤖ = flip ≋-trans
  ; isLanguage = record
    { ≈ᴸ-isEquivalence = ≡.isEquivalence
    ; ⤖-cong = λ {_} {_} {l₁≋l₂} → ≡.cong (flip ≋-trans l₁≋l₂)
    ; ⤖-bijective = λ {_} {_} {l₁≋l₂} →
                  ( (λ {x} {y} x≡y → case x , y return (λ (x , y) → x ≡.≡ y) of λ { ([] , []) → ≡.refl })
                  , (λ { [] → (case l₁≋l₂ return (λ x → ∃[ y ](≋-trans y x ≡.≡ [])) of λ { [] → [] , ≡.refl})}))
    ; ⤖-refl = λ {_} {[]≋l} → case []≋l return (λ []≋l → ≋-trans []≋l ≋-refl ≡.≡ []≋l) of λ {[] → ≡.refl}
    ; ⤖-sym = λ {_} {_} {[]≋l₁} {[]≋l₂} {l₁≋l₂} _ →
      case []≋l₁ , []≋l₂ , l₁≋l₂
      return (λ ([]≋l₁ , []≋l₂ , l₁≋l₂) → ≋-trans []≋l₂ (≋-sym l₁≋l₂) ≡.≡ []≋l₁)
      of λ { ([] , [] , []) → ≡.refl }
    ; ⤖-trans = λ {_} {_} {_} {[]≋l₁} {[]≋l₂} {[]≋l₃} {l₁≋l₂} {l₂≋l₃} _ _ →
      case []≋l₁ , []≋l₂ , []≋l₃ , l₁≋l₂ , l₂≋l₃
      return (λ ([]≋l₁ , []≋l₂ , []≋l₃ , l₁≋l₂ , l₂≋l₃) → ≋-trans []≋l₁ (≋-trans l₁≋l₂ l₂≋l₃) ≡.≡ []≋l₃)
      of λ { ([] , [] , [] , [] , []) → ≡.refl }
    }
  }

_≤_ : {a aℓ b bℓ : Level} → REL (Language a aℓ) (Language b bℓ) (c ⊔ a ⊔ b)
A ≤ B = ∀ {l} → l ∈ A → l ∈ B
