{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Derivation
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Derivation.Base over public
open import Cfe.Derivation.Properties over public
