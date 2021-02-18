{-# OPTIONS --without-K --safe #-}

open import Function
open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡

module Cfe.Language.Construct.Single
  {c ℓ} (over : Setoid c ℓ)
  (≈-trans-bijₗ : ∀ {a b c b≈c}
                  → Bijective ≡._≡_ ≡._≡_ (flip (Setoid.trans over {a} {b} {c}) b≈c))
  (≈-trans-reflₗ : ∀ {a b a≈b}
                   → Setoid.trans over {a} a≈b (Setoid.refl over {b}) ≡.≡ a≈b)
  (≈-trans-symₗ : ∀ {a b c a≈b a≈c b≈c}
                  → Setoid.trans over {a} {b} {c} a≈b b≈c ≡.≡ a≈c
                  → Setoid.trans over a≈c (Setoid.sym over b≈c) ≡.≡ a≈b)
  (≈-trans-transₗ : ∀ {a b c d a≈b a≈c a≈d b≈c c≈d}
                  → Setoid.trans over {a} {b} a≈b b≈c ≡.≡ a≈c
                  → Setoid.trans over {a} {c} {d} a≈c c≈d ≡.≡ a≈d
                  → Setoid.trans over a≈b (Setoid.trans over b≈c c≈d) ≡.≡ a≈d)
  where

open Setoid over renaming (Carrier to C)

open import Cfe.Language over hiding (_≈_)
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Product as Product
open import Level

private
  ∷-inj : {a b : C} {l₁ l₂ : List C} {a≈b a≈b′ : a ≈ b} {l₁≋l₂ l₁≋l₂′ : l₁ ≋ l₂} → ≡._≡_ {A = a ∷ l₁ ≋ b ∷ l₂} (a≈b ∷ l₁≋l₂) (a≈b′ ∷ l₁≋l₂′) → (a≈b ≡.≡ a≈b′) × (l₁≋l₂ ≡.≡ l₁≋l₂′)
  ∷-inj ≡.refl = ≡.refl , ≡.refl

  ≋-trans-injₗ : {x l₁ l₂ : List C} → {l₁≋l₂ : l₁ ≋ l₂} → Injective ≡._≡_ ≡._≡_ (flip (≋-trans {x}) l₁≋l₂)
  ≋-trans-injₗ {_} {_} {_} {_} {[]} {[]} _ = ≡.refl
  ≋-trans-injₗ {_} {_} {_} {_ ∷ _} {_ ∷ _} {_ ∷ _} = uncurry (≡.cong₂ _∷_)
                                               ∘ Product.map (proj₁ ≈-trans-bijₗ) ≋-trans-injₗ
                                               ∘ ∷-inj

  ≋-trans-surₗ : {x l₁ l₂ : List C} → {l₁≋l₂ : l₁ ≋ l₂} → Surjective {A = x ≋ l₁} ≡._≡_ ≡._≡_ (flip (≋-trans {x}) l₁≋l₂)
  ≋-trans-surₗ {_} {_} {_} {[]} [] = [] , ≡.refl
  ≋-trans-surₗ {_} {_} {_} {_ ∷ _} (a≈c ∷ x≋l₂) = Product.zip _∷_ (≡.cong₂ _∷_) (proj₂ ≈-trans-bijₗ a≈c) (≋-trans-surₗ x≋l₂)

  ≋-trans-reflₗ : {l₁ l₂ : List C} {l₁≋l₂ : l₁ ≋ l₂} → ≋-trans l₁≋l₂ ≋-refl ≡.≡ l₁≋l₂
  ≋-trans-reflₗ {_} {_} {[]} = ≡.refl
  ≋-trans-reflₗ {_} {_} {a≈b ∷ l₁≋l₂} = ≡.cong₂ _∷_ ≈-trans-reflₗ ≋-trans-reflₗ

  ≋-trans-symₗ : {l₁ l₂ l₃ : List C} {l₁≋l₂ : l₁ ≋ l₂} {l₁≋l₃ : l₁ ≋ l₃} {l₂≋l₃ : l₂ ≋ l₃}
               → ≋-trans l₁≋l₂ l₂≋l₃ ≡.≡ l₁≋l₃
               → ≋-trans l₁≋l₃ (≋-sym l₂≋l₃) ≡.≡ l₁≋l₂
  ≋-trans-symₗ {_} {_} {_} {[]} {[]} {[]} _ = ≡.refl
  ≋-trans-symₗ {_} {_} {_} {_ ∷ _} {_ ∷ _} {_ ∷ _} = uncurry (≡.cong₂ _∷_)
                                                   ∘ Product.map ≈-trans-symₗ ≋-trans-symₗ
                                                   ∘ ∷-inj

  ≋-trans-transₗ : {l₁ l₂ l₃ l₄ : List C}
                 → {l₁≋l₂ : l₁ ≋ l₂} {l₁≋l₃ : l₁ ≋ l₃} {l₁≋l₄ : l₁ ≋ l₄} {l₂≋l₃ : l₂ ≋ l₃} {l₃≋l₄ : l₃ ≋ l₄}
                 → ≋-trans l₁≋l₂ l₂≋l₃ ≡.≡ l₁≋l₃
                 → ≋-trans l₁≋l₃ l₃≋l₄ ≡.≡ l₁≋l₄
                 → ≋-trans l₁≋l₂ (≋-trans l₂≋l₃ l₃≋l₄) ≡.≡ l₁≋l₄
  ≋-trans-transₗ {l₁≋l₂ = []} {[]} {[]} {[]} {[]} _ _ = ≡.refl
  ≋-trans-transₗ {l₁≋l₂ = _ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} = uncurry (≡.cong₂ _∷_)
                                                                 ∘₂ uncurry (Product.zip ≈-trans-transₗ ≋-trans-transₗ)
                                                                 ∘₂ curry (Product.map ∷-inj ∷-inj)

｛_｝ : C → Language (c ⊔ ℓ) (c ⊔ ℓ)
｛ c ｝ = record
  { Carrier = [ c ] ≋_
  ; _≈_ = λ l≋m l≋n → ∃[ m≋n ] ≋-trans l≋m m≋n ≡.≡ l≋n
  ; isEquivalence = record
    { refl = ≋-refl , ≋-trans-reflₗ
    ; sym = Product.map ≋-sym ≋-trans-symₗ
    ; trans = Product.zip ≋-trans ≋-trans-transₗ
    }
  }
