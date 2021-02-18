{-# OPTIONS --without-K --safe #-}

open import Relation.Binary as B using (Setoid)

module Cfe.Language.Indexed.Construct.Iterate
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C)

open import Cfe.Language over
open import Cfe.Language.Indexed.Homogeneous over
open import Data.List
open import Data.Nat as ℕ hiding (_⊔_)
open import Data.Product as Product
open import Function
open import Level hiding (Lift) renaming (suc to lsuc)
open import Relation.Binary.Indexed.Heterogeneous
open import Relation.Binary.PropositionalEquality as ≡

open IndexedLanguage

iter : ∀ {a} {A : Set a} → (A → A) → ℕ → A → A
iter f ℕ.zero = id
iter f (ℕ.suc n) = f ∘ iter f n

Iterate : ∀ {a aℓ} → (Language a aℓ → Language a aℓ) → IndexedLanguage 0ℓ 0ℓ a aℓ
Iterate {a} {aℓ} f = record
  { Carrierᵢ = ℕ
  ; _≈ᵢ_ = ≡._≡_
  ; isEquivalenceᵢ = ≡.isEquivalence
  ; F = λ n → iter f n (Lift a aℓ ∅)
  ; cong = λ {≡.refl → ≈-refl}
  }

≈ᵗ-refl : ∀ {a aℓ} →
          (g : Language a aℓ → Language a aℓ) →
          Reflexive (Tagged (Iterate g)) (_≈ᵗ_ (Iterate g))
≈ᵗ-refl g {_} {n , _} = refl , (≈ᴸ-refl (Iter.F n))
  where
  module Iter = IndexedLanguage (Iterate g)

≈ᵗ-sym : ∀ {a aℓ} →
         (g : Language a aℓ → Language a aℓ) →
         Symmetric (Tagged (Iterate g)) (_≈ᵗ_ (Iterate g))
≈ᵗ-sym g {_} {_} {n , _} (refl , x∈Fn≈y∈Fn) =
  refl , (≈ᴸ-sym (Iter.F n) x∈Fn≈y∈Fn)
  where
  module Iter = IndexedLanguage (Iterate g)

≈ᵗ-trans : ∀ {a aℓ} →
          (g : Language a aℓ → Language a aℓ) →
          Transitive (Tagged (Iterate g)) (_≈ᵗ_ (Iterate g))
≈ᵗ-trans g {_} {_} {_} {n , _} (refl , x∈Fn≈y∈Fn) (refl , y∈Fn≈z∈Fn) =
  refl , (≈ᴸ-trans (Iter.F n) x∈Fn≈y∈Fn y∈Fn≈z∈Fn)
  where
  module Iter = IndexedLanguage (Iterate g)

⋃ : ∀ {a aℓ} → (Language a aℓ → Language a aℓ) → Language a aℓ
⋃ f = record
  { Carrier = Iter.Tagged
  ; _≈_ = Iter._≈ᵗ_
  ; isEquivalence = record
    { refl = ≈ᵗ-refl f
    ; sym = ≈ᵗ-sym f
    ; trans = ≈ᵗ-trans f
    }
  }
  where
  module Iter = IndexedLanguage (Iterate f)
