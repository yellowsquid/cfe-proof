{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Language.Properties
  {c ℓ} {setoid : Setoid c ℓ}
  where

open Setoid setoid renaming (Carrier to A)
open import Cfe.Language setoid
open Language

open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid setoid
open import Function
open import Level
open import Relation.Binary.Construct.InducedPoset

_≤′_ : ∀ {a aℓ} → Rel (Language a aℓ) (c ⊔ a)
_≤′_ = _≤_

------------------------------------------------------------------------
-- Properties of _≤_

≤-refl : ∀ {a aℓ} → Reflexive (_≤′_ {a} {aℓ})
≤-refl = id

≤-trans : ∀ {a b c aℓ bℓ cℓ} → Trans (_≤_ {a} {aℓ}) (_≤_ {b} {bℓ} {c} {cℓ}) _≤_
≤-trans A≤B B≤C = B≤C ∘ A≤B

≤-poset : ∀ {a aℓ} → Poset (c ⊔ ℓ ⊔ suc (a ⊔ aℓ)) (c ⊔ a) (c ⊔ a)
≤-poset {a} {aℓ} = InducedPoset (_≤′_ {a} {aℓ}) id (λ i≤j j≤k → j≤k ∘ i≤j)

-- ------------------------------------------------------------------------
-- -- Properties of _∪_

-- ∪-cong-≤ : Congruent₂ _≤_ _∪_
-- ∪-cong-≤ A≤B C≤D = map A≤B C≤D

-- ∪-cong : Congruent₂ _≈_ _∪_
-- ∪-cong {A} {B} {C} {D} = ≤-cong₂→≈-cong₂ {_∪_} (λ A≤B C≤D → map A≤B C≤D) {A} {B} {C} {D}
