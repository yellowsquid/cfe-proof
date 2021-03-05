{-# OPTIONS --without-K --safe #-}

open import Relation.Binary as B using (Setoid)

module Cfe.Language.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C)

open import Algebra
open import Data.Empty
open import Data.List hiding (null)
open import Data.Product
open import Data.Unit using (⊤; tt)
open import Function hiding (Injection; Surjection; Inverse)
import Function.Equality as Equality using (setoid)
open import Level as L hiding (Lift)
open import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial as Trivial
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.Indexed.Heterogeneous

infix 4 _∈_
infix 4 _∉_

Language : ∀ a aℓ → Set (suc c ⊔ suc a ⊔ suc aℓ)
Language a aℓ = IndexedSetoid (List C) a aℓ

∅ : Language 0ℓ 0ℓ
∅ = Trivial.indexedSetoid (≡.setoid ⊥)

｛ε｝ : Language c 0ℓ
｛ε｝ = record
  { Carrier = [] ≡_
  ; _≈_ = λ _ _ → ⊤
  ; isEquivalence = record
    { refl = tt
    ; sym = λ _ → tt
    ; trans = λ _ _ → tt
    }
  }

Lift : ∀ {a aℓ} → (b bℓ : Level) → Language a aℓ → Language (a ⊔ b) (aℓ ⊔ bℓ)
Lift b bℓ A = record
  { Carrier = L.Lift b ∘ A.Carrier
  ; _≈_ = λ (lift x) (lift y) → L.Lift bℓ (x A.≈ y)
  ; isEquivalence = record
    { refl = lift A.refl
    ; sym = λ (lift x) → lift (A.sym x)
    ; trans = λ (lift x) (lift y) → lift (A.trans x y)
    }
  }
  where
  module A = IndexedSetoid A

𝕃 : ∀ {a aℓ} → Language a aℓ → List C → Set a
𝕃 = IndexedSetoid.Carrier

_∈_ : ∀ {a aℓ} → List C → Language a aℓ → Set a
_∈_ = flip 𝕃

_∉_ : ∀ {a aℓ} → List C → Language a aℓ → Set a
l ∉ A = l ∈ A → ⊥

∈-cong : ∀ {a aℓ} → (A : Language a aℓ) → ∀ {l₁ l₂} → l₁ ≡ l₂ → l₁ ∈ A → l₂ ∈ A
∈-cong A ≡.refl l∈A = l∈A

≈ᴸ : ∀ {a aℓ} → (A : Language a aℓ) → ∀ {l₁ l₂} → 𝕃 A l₁ → 𝕃 A l₂ → Set aℓ
≈ᴸ = IndexedSetoid._≈_

≈ᴸ-refl : ∀ {a aℓ} → (A : Language a aℓ) → Reflexive (𝕃 A) (≈ᴸ A)
≈ᴸ-refl = IsIndexedEquivalence.refl ∘ IndexedSetoid.isEquivalence

≈ᴸ-sym : ∀ {a aℓ} → (A : Language a aℓ) → Symmetric (𝕃 A) (≈ᴸ A)
≈ᴸ-sym = IsIndexedEquivalence.sym ∘ IndexedSetoid.isEquivalence

≈ᴸ-trans : ∀ {a aℓ} → (A : Language a aℓ) → Transitive (𝕃 A) (≈ᴸ A)
≈ᴸ-trans = IsIndexedEquivalence.trans ∘ IndexedSetoid.isEquivalence

≈ᴸ-cong : ∀ {a aℓ} → (A : Language a aℓ) → ∀ {l₁ l₂ l₃ l₄} →
          (l₁≡l₂ : l₁ ≡ l₂) → (l₃≡l₄ : l₃ ≡ l₄) →
          (l₁∈A : l₁ ∈ A) → (l₃∈A : l₃ ∈ A) →
          ≈ᴸ A l₁∈A l₃∈A →
          ≈ᴸ A (∈-cong A l₁≡l₂ l₁∈A) (∈-cong A l₃≡l₄ l₃∈A)
≈ᴸ-cong A ≡.refl ≡.refl l₁∈A l₃∈A eq = eq

record _≤_ {a aℓ b bℓ} (A : Language a aℓ) (B : Language b bℓ) : Set (c ⊔ a ⊔ aℓ ⊔ b ⊔ bℓ) where
  field
    f : ∀ {l} → l ∈ A → l ∈ B
    cong : ∀ {l₁ l₂ l₁∈A l₂∈A} → ≈ᴸ A {l₁} {l₂} l₁∈A l₂∈A → ≈ᴸ B (f l₁∈A) (f l₂∈A)

record _≈_ {a aℓ b bℓ} (A : Language a aℓ) (B : Language b bℓ) : Set (c ⊔ ℓ ⊔ a ⊔ aℓ ⊔ b ⊔ bℓ) where
  field
    f : ∀ {l} → l ∈ A → l ∈ B
    f⁻¹ : ∀ {l} → l ∈ B → l ∈ A
    cong₁ : ∀ {l₁ l₂ l₁∈A l₂∈A} → ≈ᴸ A {l₁} {l₂} l₁∈A l₂∈A → ≈ᴸ B (f l₁∈A) (f l₂∈A)
    cong₂ : ∀ {l₁ l₂ l₁∈B l₂∈B} → ≈ᴸ B {l₁} {l₂} l₁∈B l₂∈B → ≈ᴸ A (f⁻¹ l₁∈B) (f⁻¹ l₂∈B)

null : ∀ {a} {aℓ} → Language a aℓ → Set a
null A = [] ∈ A

first : ∀ {a} {aℓ} → Language a aℓ → C → Set (c ⊔ a)
first A x = ∃[ l ] x ∷ l ∈ A

flast : ∀ {a} {aℓ} → Language a aℓ → C → Set (c ⊔ a)
flast A x = ∃[ l ] (l ≡.≢ [] × ∃[ l′ ] l ++ x ∷ l′ ∈ A)
