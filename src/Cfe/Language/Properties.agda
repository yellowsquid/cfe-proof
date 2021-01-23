{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Language.Properties
  {a ℓ} (setoid : Setoid a ℓ)
  where

open Setoid setoid renaming (Carrier to A)

open import Cfe.Language setoid
open import Function

------------------------------------------------------------------------
-- Properties of _≤_

≤-refl : Reflexive _≤_
≤-refl = id

≤-trans : Transitive _≤_
≤-trans A≤B B≤C = B≤C ∘ A≤B
