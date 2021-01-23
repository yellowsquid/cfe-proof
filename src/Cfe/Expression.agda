{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Expression
  {a ℓ} (setoid : Setoid a ℓ)
  where

open import Cfe.Expression.Base setoid public
