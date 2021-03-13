{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Judgement
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Judgement.Base over public
open import Cfe.Judgement.Properties over public
