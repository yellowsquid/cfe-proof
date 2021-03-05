{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Type.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C)

open import Cfe.Language over
open import Data.Bool
open import Level renaming (suc to lsuc)
open import Relation.Unary

infix 4 _⊨_

record Type fℓ lℓ : Set (c ⊔ lsuc (fℓ ⊔ lℓ)) where
  field
    Null : Bool
    First : Pred C fℓ
    Flast : Pred C lℓ

open Type public

record _⊨_ {a} {aℓ} {fℓ} {lℓ} (A : Language a aℓ) (τ : Type fℓ lℓ) : Set (c ⊔ a ⊔ fℓ ⊔ lℓ) where
  field
    n⇒n : null A → T (Null τ)
    f⇒f : first A ⊆ First τ
    l⇒l : flast A ⊆ Flast τ
