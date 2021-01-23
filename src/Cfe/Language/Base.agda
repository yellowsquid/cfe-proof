{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Language.Base
  {a ℓ} (setoid : Setoid a ℓ)
  where

open Setoid setoid renaming (Carrier to A)

open import Data.Empty.Polymorphic
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid setoid
open import Data.Nat hiding (_≤_; _⊔_)
open import Data.Product
open import Data.Sum
open import Function
open import Level renaming (suc to lsuc)

Language : Set (lsuc a ⊔ lsuc ℓ)
Language = List A → Set (a ⊔ ℓ)

∅ : Language
∅ = const ⊥

｛ε｝ : Language
｛ε｝ = [] ≋_

｛_｝ : A → Language
｛ a ｝ = [ a ] ≋_

infix 4 _∪_
infix 4 _∙_

_∪_ : Language → Language → Language
(A ∪ B) l = A l ⊎ B l

_∙_ : Language → Language → Language
(A ∙ B) l = ∃[ l₁ ] ∃[ l₂ ] (A l₁ × B l₂ × l₁ ++ l₂ ≋ l)

iterate : (Language → Language) → ℕ → Language → Language
iterate f ℕ.zero = id
iterate f (suc n) = f ∘ iterate f n

fix : (Language → Language) → Language
fix f l = ∃[ n ] iterate f n ∅ l

_≤_ : Language → Language → Set (a ⊔ ℓ)
A ≤ B = ∀ {l} → A l → B l
