{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Language.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C)
open import Cfe.Language.Base over
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid over
open import Function
open import Level hiding (Lift)

≈-refl : ∀ {a} → Reflexive (_≈_ {a})
≈-refl {x = A} = record
  { f = id
  ; f⁻¹ = id
  }

≈-sym : ∀ {a b} → Sym (_≈_ {a} {b}) _≈_
≈-sym A≈B = record
  { f = A≈B.f⁻¹
  ; f⁻¹ = A≈B.f
  }
  where
  module A≈B = _≈_ A≈B

≈-trans : ∀ {a b c} → Trans (_≈_ {a}) (_≈_ {b} {c}) _≈_
≈-trans {i = A} {B} {C} A≈B B≈C = record
  { f = B≈C.f ∘ A≈B.f
  ; f⁻¹ = A≈B.f⁻¹ ∘ B≈C.f⁻¹
  }
  where
  module A≈B = _≈_ A≈B
  module B≈C = _≈_ B≈C

≈-isEquivalence : ∀ {a} → IsEquivalence (_≈_ {a})
≈-isEquivalence = record
  { refl = ≈-refl
  ; sym = ≈-sym
  ; trans = ≈-trans
  }

setoid : ∀ a → Setoid (c ⊔ ℓ ⊔ suc a) (c ⊔ ℓ ⊔ a)
setoid a = record { isEquivalence = ≈-isEquivalence {a} }

≤-refl : ∀ {a} → Reflexive (_≤_ {a})
≤-refl = record
  { f = id
  }

≤-reflexive : ∀ {a b} → _≈_ {a} {b} ⇒ _≤_
≤-reflexive A≈B = record
  { f = A≈B.f
  }
  where
  module A≈B = _≈_ A≈B

≤-trans : ∀ {a b c} → Trans (_≤_ {a}) (_≤_ {b} {c}) _≤_
≤-trans A≤B B≤C = record
  { f = B≤C.f ∘ A≤B.f
  }
  where
  module A≤B = _≤_ A≤B
  module B≤C = _≤_ B≤C

≤-antisym : ∀ {a b} → Antisym (_≤_ {a} {b}) _≤_ _≈_
≤-antisym A≤B B≤A = record
  { f = A≤B.f
  ; f⁻¹ = B≤A.f
  }
  where
  module A≤B = _≤_ A≤B
  module B≤A = _≤_ B≤A

≤-min : ∀ {b} → Min (_≤_ {b = b}) ∅
≤-min A = record
  { f = λ ()
  }

≤-isPartialOrder : ∀ a → IsPartialOrder (_≈_ {a}) _≤_
≤-isPartialOrder a = record
  { isPreorder = record
    { isEquivalence = ≈-isEquivalence
    ; reflexive = ≤-reflexive
    ; trans = ≤-trans
    }
  ; antisym = ≤-antisym
  }

poset : ∀ a → Poset (c ⊔ ℓ ⊔ suc a) (c ⊔ ℓ ⊔ a) (c ⊔ a)
poset a = record { isPartialOrder = ≤-isPartialOrder a }

<-trans : ∀ {a b c} → Trans (_<_ {a}) (_<_ {b} {c}) _<_
<-trans A<B B<C = record
  { f = B<C.f ∘ A<B.f
  ; l = A<B.l
  ; l∉A = A<B.l∉A
  ; l∈B = B<C.f A<B.l∈B
  }
  where
  module A<B = _<_ A<B
  module B<C = _<_ B<C

<-irrefl : ∀ {a b} → Irreflexive (_≈_ {a} {b}) _<_
<-irrefl A≈B A<B = A<B.l∉A (A≈B.f⁻¹ A<B.l∈B)
  where
  module A≈B = _≈_ A≈B
  module A<B = _<_ A<B

<-asym : ∀ {a} → Asymmetric (_<_ {a})
<-asym A<B B<A = A<B.l∉A (B<A.f A<B.l∈B)
  where
  module A<B = _<_ A<B
  module B<A = _<_ B<A

lift-cong : ∀ {a} b (L : Language a) → Lift b L ≈ L
lift-cong b L = record
  { f = lower
  ; f⁻¹ = lift
  }
