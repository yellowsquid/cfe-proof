{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Parse
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Parse.Base over public
open import Cfe.Parse.Properties over public
