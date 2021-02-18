{-# OPTIONS --without-K --safe #-}

open import Relation.Binary as B using (Setoid)

module Cfe.Language.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C)

open import Cfe.Relation.Indexed
open import Data.Empty
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Product
open import Function hiding (Injection; Surjection; Inverse)
import Function.Equality as Equality using (setoid)
open import Level as L hiding (Lift)
open import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial as Trivial
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.Indexed.Heterogeneous

Language : ∀ a aℓ → Set (suc c ⊔ suc a ⊔ suc aℓ)
Language a aℓ = IndexedSetoid (List C) a aℓ

∅ : Language 0ℓ 0ℓ
∅ = Trivial.indexedSetoid (≡.setoid ⊥)

｛ε｝ : Language (c ⊔ ℓ) (c ⊔ ℓ)
｛ε｝ = record
  { Carrier = [] ≋_
  ; _≈_ = λ {l₁} {l₂} []≋l₁ []≋l₂ → ∃[ l₁≋l₂ ] (≋-trans []≋l₁ l₁≋l₂ ≡.≡ []≋l₂)
  ; isEquivalence = record
    { refl = λ {_} {x} →
      ≋-refl ,
      ( case x return (λ x → ≋-trans x ≋-refl ≡.≡ x) of λ {[] → ≡.refl} )
    ; sym = λ {_} {_} {x} {y} (z , _) →
      ≋-sym z ,
      ( case (x , y , z)
        return (λ (x , y , z) → ≋-trans y (≋-sym z) ≡.≡ x)
        of λ {([] , [] , []) → ≡.refl} )
    ; trans = λ {_} {_} {_} {v} {w} {x} (y , _) (z , _) →
      ≋-trans y z ,
      ( case (v , w , x , y , z)
        return (λ (v , _ , x , y , z) → ≋-trans v (≋-trans y z) ≡.≡ x)
        of λ {([] , [] , [] , [] , []) → ≡.refl} )
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

≈ᴸ : ∀ {a aℓ} → (A : Language a aℓ) → ∀ {l₁ l₂} → 𝕃 A l₁ → 𝕃 A l₂ → Set aℓ
≈ᴸ = IndexedSetoid._≈_

≈ᴸ-refl : ∀ {a aℓ} → (A : Language a aℓ) → Reflexive (𝕃 A) (≈ᴸ A)
≈ᴸ-refl = IsIndexedEquivalence.refl ∘ IndexedSetoid.isEquivalence

≈ᴸ-sym : ∀ {a aℓ} → (A : Language a aℓ) → Symmetric (𝕃 A) (≈ᴸ A)
≈ᴸ-sym = IsIndexedEquivalence.sym ∘ IndexedSetoid.isEquivalence

≈ᴸ-trans : ∀ {a aℓ} → (A : Language a aℓ) → Transitive (𝕃 A) (≈ᴸ A)
≈ᴸ-trans = IsIndexedEquivalence.trans ∘ IndexedSetoid.isEquivalence

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

≈-refl : ∀ {a aℓ} → B.Reflexive (_≈_ {a} {aℓ})
≈-refl {x = A} = record
  { f = id
  ; f⁻¹ = id
  ; cong₁ = id
  ; cong₂ = id
  }

≈-sym : ∀ {a aℓ b bℓ} → B.Sym (_≈_ {a} {aℓ} {b} {bℓ}) _≈_
≈-sym A≈B = record
  { f = A≈B.f⁻¹
  ; f⁻¹ = A≈B.f
  ; cong₁ = A≈B.cong₂
  ; cong₂ = A≈B.cong₁
  }
  where
  module A≈B = _≈_ A≈B

≈-trans : ∀ {a aℓ b bℓ c cℓ} → B.Trans (_≈_ {a} {aℓ}) (_≈_ {b} {bℓ} {c} {cℓ}) _≈_
≈-trans {i = A} {B} {C} A≈B B≈C = record
  { f = B≈C.f ∘ A≈B.f
  ; f⁻¹ = A≈B.f⁻¹ ∘ B≈C.f⁻¹
  ; cong₁ = B≈C.cong₁ ∘ A≈B.cong₁
  ; cong₂ = A≈B.cong₂ ∘ B≈C.cong₂
  }
  where
  module A≈B = _≈_ A≈B
  module B≈C = _≈_ B≈C

setoid : ∀ a aℓ → B.Setoid (suc (c ⊔ a ⊔ aℓ)) (c ⊔ ℓ ⊔ a ⊔ aℓ)
setoid a aℓ = record
  { Carrier = Language a aℓ
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl = ≈-refl
    ; sym = ≈-sym
    ; trans = ≈-trans
    }
  }

≤-refl : ∀ {a aℓ} → B.Reflexive (_≤_ {a} {aℓ})
≤-refl = record
  { f = id
  ; cong = id
  }

≤-trans : ∀ {a aℓ b bℓ c cℓ} → B.Trans (_≤_ {a} {aℓ}) (_≤_ {b} {bℓ} {c} {cℓ}) _≤_
≤-trans A≤B B≤C = record
  { f = B≤C.f ∘ A≤B.f
  ; cong = B≤C.cong ∘ A≤B.cong
  }
  where
  module A≤B = _≤_ A≤B
  module B≤C = _≤_ B≤C

≤-antisym : ∀ {a aℓ b bℓ} → B.Antisym (_≤_ {a} {aℓ} {b} {bℓ}) _≤_ _≈_
≤-antisym A≤B B≤A = record
  { f = A≤B.f
  ; f⁻¹ = B≤A.f
  ; cong₁ = A≤B.cong
  ; cong₂ = B≤A.cong
  }
  where
  module A≤B = _≤_ A≤B
  module B≤A = _≤_ B≤A

≤-min : ∀ {b bℓ} → B.Min (_≤_ {b = b} {bℓ}) ∅
≤-min A = record
  { f = λ ()
  ; cong = λ {_} {_} {}
  }
