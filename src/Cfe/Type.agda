{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Type
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Type.Base over public
open import Cfe.Type.Properties over public
