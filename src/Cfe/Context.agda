{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Context
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Context.Base over public
open import Cfe.Context.Properties over public
