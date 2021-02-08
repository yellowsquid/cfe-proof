{-# OPTIONS --without-K --safe #-}

open import Function
open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡

module Cfe.Language.Construct.Single
  {a ℓ} (setoid : Setoid a ℓ)
  (≈-trans-bijₗ : ∀ {a b c : Setoid.Carrier setoid}
                  → {b≈c : Setoid._≈_ setoid b c}
                  → Bijective ≡._≡_ ≡._≡_ (flip (Setoid.trans setoid {a}) b≈c))
  (≈-trans-reflₗ : ∀ {a b : Setoid.Carrier setoid} {a≈b : Setoid._≈_ setoid a b}
                   → Setoid.trans setoid a≈b (Setoid.refl setoid) ≡.≡ a≈b)
  (≈-trans-symₗ : ∀ {a b c : Setoid.Carrier setoid}
                  → {a≈b : Setoid._≈_ setoid a b}
                  → {a≈c : Setoid._≈_ setoid a c}
                  → {b≈c : Setoid._≈_ setoid b c}
                  → Setoid.trans setoid a≈b b≈c ≡.≡ a≈c
                  → Setoid.trans setoid a≈c (Setoid.sym setoid b≈c) ≡.≡ a≈b)
  (≈-trans-transₗ : ∀ {a b c d : Setoid.Carrier setoid}
                  → {a≈b : Setoid._≈_ setoid a b}
                  → {a≈c : Setoid._≈_ setoid a c}
                  → {a≈d : Setoid._≈_ setoid a d}
                  → {b≈c : Setoid._≈_ setoid b c}
                  → {c≈d : Setoid._≈_ setoid c d}
                  → Setoid.trans setoid a≈b b≈c ≡.≡ a≈c
                  → Setoid.trans setoid a≈c c≈d ≡.≡ a≈d
                  → Setoid.trans setoid a≈b (Setoid.trans setoid b≈c c≈d) ≡.≡ a≈d)
  where

open Setoid setoid renaming (Carrier to A)

open import Cfe.Language setoid
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid setoid
open import Data.Product as Product
open import Level

private
  ∷-inj : {a b : A} {l₁ l₂ : List A} {a≈b a≈b′ : a ≈ b} {l₁≋l₂ l₁≋l₂′ : l₁ ≋ l₂} → ≡._≡_ {A = a ∷ l₁ ≋ b ∷ l₂} (a≈b ∷ l₁≋l₂) (a≈b′ ∷ l₁≋l₂′) → (a≈b ≡.≡ a≈b′) × (l₁≋l₂ ≡.≡ l₁≋l₂′)
  ∷-inj ≡.refl = ≡.refl , ≡.refl

  ≋-trans-injₗ : {x l₁ l₂ : List A} → {l₁≋l₂ : l₁ ≋ l₂} → Injective ≡._≡_ ≡._≡_ (flip (≋-trans {x}) l₁≋l₂)
  ≋-trans-injₗ {_} {_} {_} {_} {[]} {[]} _ = ≡.refl
  ≋-trans-injₗ {_} {_} {_} {_ ∷ _} {_ ∷ _} {_ ∷ _} = uncurry (≡.cong₂ _∷_)
                                               ∘ Product.map (proj₁ ≈-trans-bijₗ) ≋-trans-injₗ
                                               ∘ ∷-inj

  ≋-trans-surₗ : {x l₁ l₂ : List A} → {l₁≋l₂ : l₁ ≋ l₂} → Surjective {A = x ≋ l₁} ≡._≡_ ≡._≡_ (flip (≋-trans {x}) l₁≋l₂)
  ≋-trans-surₗ {_} {_} {_} {[]} [] = [] , ≡.refl
  ≋-trans-surₗ {_} {_} {_} {_ ∷ _} (a≈c ∷ x≋l₂) = Product.zip _∷_ (≡.cong₂ _∷_) (proj₂ ≈-trans-bijₗ a≈c) (≋-trans-surₗ x≋l₂)

  ≋-trans-reflₗ : {l₁ l₂ : List A} {l₁≋l₂ : l₁ ≋ l₂} → ≋-trans l₁≋l₂ ≋-refl ≡.≡ l₁≋l₂
  ≋-trans-reflₗ {_} {_} {[]} = ≡.refl
  ≋-trans-reflₗ {_} {_} {a≈b ∷ l₁≋l₂} = ≡.cong₂ _∷_ ≈-trans-reflₗ ≋-trans-reflₗ

  ≋-trans-symₗ : {l₁ l₂ l₃ : List A} {l₁≋l₂ : l₁ ≋ l₂} {l₁≋l₃ : l₁ ≋ l₃} {l₂≋l₃ : l₂ ≋ l₃}
               → ≋-trans l₁≋l₂ l₂≋l₃ ≡.≡ l₁≋l₃
               → ≋-trans l₁≋l₃ (≋-sym l₂≋l₃) ≡.≡ l₁≋l₂
  ≋-trans-symₗ {_} {_} {_} {[]} {[]} {[]} _ = ≡.refl
  ≋-trans-symₗ {_} {_} {_} {_ ∷ _} {_ ∷ _} {_ ∷ _} = uncurry (≡.cong₂ _∷_)
                                                   ∘ Product.map ≈-trans-symₗ ≋-trans-symₗ
                                                   ∘ ∷-inj

  ≋-trans-transₗ : {l₁ l₂ l₃ l₄ : List A}
                 → {l₁≋l₂ : l₁ ≋ l₂} {l₁≋l₃ : l₁ ≋ l₃} {l₁≋l₄ : l₁ ≋ l₄} {l₂≋l₃ : l₂ ≋ l₃} {l₃≋l₄ : l₃ ≋ l₄}
                 → ≋-trans l₁≋l₂ l₂≋l₃ ≡.≡ l₁≋l₃
                 → ≋-trans l₁≋l₃ l₃≋l₄ ≡.≡ l₁≋l₄
                 → ≋-trans l₁≋l₂ (≋-trans l₂≋l₃ l₃≋l₄) ≡.≡ l₁≋l₄
  ≋-trans-transₗ {l₁≋l₂ = []} {[]} {[]} {[]} {[]} _ _ = ≡.refl
  ≋-trans-transₗ {l₁≋l₂ = _ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} = uncurry (≡.cong₂ _∷_)
                                                                 ∘₂ uncurry (Product.zip ≈-trans-transₗ ≋-trans-transₗ)
                                                                 ∘₂ curry (Product.map ∷-inj ∷-inj)

｛_｝ : List A → Language (a ⊔ ℓ) (a ⊔ ℓ)
｛ l ｝ = record
  { 𝕃 = l ≋_
  ; _≈ᴸ_ = ≡._≡_
  ; ⤖ = flip ≋-trans
  ; isLanguage = record
    { ≈ᴸ-isEquivalence = ≡.isEquivalence
    ; ⤖-cong = λ {_} {_} {l₁≋l₂} → ≡.cong (flip ≋-trans l₁≋l₂)
    ; ⤖-bijective = ≋-trans-injₗ , ≋-trans-surₗ
    ; ⤖-refl = ≋-trans-reflₗ
    ; ⤖-sym = ≋-trans-symₗ
    ; ⤖-trans = ≋-trans-transₗ
    }
  }
