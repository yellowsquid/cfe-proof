{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Language.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C)
open import Cfe.Language.Base over
-- open Language

open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid over
open import Function
open import Level

≈-refl : ∀ {a aℓ} → Reflexive (_≈_ {a} {aℓ})
≈-refl {x = A} = record
  { f = id
  ; f⁻¹ = id
  ; cong₁ = id
  ; cong₂ = id
  }

≈-sym : ∀ {a aℓ b bℓ} → Sym (_≈_ {a} {aℓ} {b} {bℓ}) _≈_
≈-sym A≈B = record
  { f = A≈B.f⁻¹
  ; f⁻¹ = A≈B.f
  ; cong₁ = A≈B.cong₂
  ; cong₂ = A≈B.cong₁
  }
  where
  module A≈B = _≈_ A≈B

≈-trans : ∀ {a aℓ b bℓ c cℓ} → Trans (_≈_ {a} {aℓ}) (_≈_ {b} {bℓ} {c} {cℓ}) _≈_
≈-trans {i = A} {B} {C} A≈B B≈C = record
  { f = B≈C.f ∘ A≈B.f
  ; f⁻¹ = A≈B.f⁻¹ ∘ B≈C.f⁻¹
  ; cong₁ = B≈C.cong₁ ∘ A≈B.cong₁
  ; cong₂ = A≈B.cong₂ ∘ B≈C.cong₂
  }
  where
  module A≈B = _≈_ A≈B
  module B≈C = _≈_ B≈C

≈-isEquivalence : ∀ {a aℓ} → IsEquivalence (_≈_ {a} {aℓ} {a} {aℓ})
≈-isEquivalence = record
  { refl = ≈-refl
  ; sym = ≈-sym
  ; trans = ≈-trans
  }

setoid : ∀ a aℓ → Setoid (suc (c ⊔ a ⊔ aℓ)) (c ⊔ ℓ ⊔ a ⊔ aℓ)
setoid a aℓ = record { isEquivalence = ≈-isEquivalence {a} {aℓ} }

≤-refl : ∀ {a aℓ} → Reflexive (_≤_ {a} {aℓ})
≤-refl = record
  { f = id
  ; cong = id
  }

≤-reflexive : ∀ {a aℓ b bℓ} → _≈_ {a} {aℓ} {b} {bℓ} ⇒ _≤_
≤-reflexive A≈B = record
  { f = A≈B.f
  ; cong = A≈B.cong₁
  }
  where
  module A≈B = _≈_ A≈B

≤-trans : ∀ {a aℓ b bℓ c cℓ} → Trans (_≤_ {a} {aℓ}) (_≤_ {b} {bℓ} {c} {cℓ}) _≤_
≤-trans A≤B B≤C = record
  { f = B≤C.f ∘ A≤B.f
  ; cong = B≤C.cong ∘ A≤B.cong
  }
  where
  module A≤B = _≤_ A≤B
  module B≤C = _≤_ B≤C

≤-antisym : ∀ {a aℓ b bℓ} → Antisym (_≤_ {a} {aℓ} {b} {bℓ}) _≤_ _≈_
≤-antisym A≤B B≤A = record
  { f = A≤B.f
  ; f⁻¹ = B≤A.f
  ; cong₁ = A≤B.cong
  ; cong₂ = B≤A.cong
  }
  where
  module A≤B = _≤_ A≤B
  module B≤A = _≤_ B≤A

≤-min : ∀ {b bℓ} → Min (_≤_ {b = b} {bℓ}) ∅
≤-min A = record
  { f = λ ()
  ; cong = λ {_} {_} {}
  }

≤-isPartialOrder : ∀ a aℓ → IsPartialOrder (_≈_ {a} {aℓ}) _≤_
≤-isPartialOrder a aℓ = record
  { isPreorder = record
    { isEquivalence = ≈-isEquivalence
    ; reflexive = ≤-reflexive
    ; trans = ≤-trans
    }
  ; antisym = ≤-antisym
  }

poset : ∀ a aℓ → Poset (suc (c ⊔ a ⊔ aℓ)) (c ⊔ ℓ ⊔ a ⊔ aℓ) (c ⊔ a ⊔ aℓ)
poset a aℓ = record { isPartialOrder = ≤-isPartialOrder a aℓ }
