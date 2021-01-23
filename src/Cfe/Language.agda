{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Language
  {a ℓ} (setoid : Setoid a ℓ)
  where

open import Cfe.Language.Base setoid public
