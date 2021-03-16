{-# OPTIONS --without-K --safe #-}

open import Relation.Binary as B using (Setoid)

module Cfe.Language.Indexed.Homogeneous
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Language over
open import Level
open import Data.List
open import Data.Product
open import Relation.Binary.Indexed.Heterogeneous

open _≈_

open Setoid over using () renaming (Carrier to C)

record IndexedLanguage i iℓ a : Set (ℓ ⊔ suc (c ⊔ i ⊔ iℓ ⊔ a)) where
  field
    Carrierᵢ : Set i
    _≈ᵢ_ : B.Rel Carrierᵢ iℓ
    isEquivalenceᵢ : B.IsEquivalence _≈ᵢ_
    F : Carrierᵢ → Language a
    cong : F B.Preserves _≈ᵢ_ ⟶ _≈_

  open B.IsEquivalence isEquivalenceᵢ using () renaming (refl to reflᵢ; sym to symᵢ; trans to transᵢ) public

  Tagged : List C → Set (i ⊔ a)
  Tagged l = ∃[ i ] l ∈ F i
