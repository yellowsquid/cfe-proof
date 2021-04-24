{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (REL; Setoid)

module Cfe.Derivation.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over renaming (Carrier to C; _≈_ to _∼_)

open import Cfe.Expression over hiding (_≈_)
open import Data.Fin using (zero)
open import Data.List using (List; []; [_]; _++_)
open import Data.List.Relation.Binary.Equality.Setoid over using (_≋_)
open import Level using (_⊔_)

infix 5 _⤇_
infix 4 _≈_

data _⤇_ : Expression 0 → List C → Set (c ⊔ ℓ) where
  Eps  : ε ⤇ []
  Char : ∀ {c y} → (c∼y : c ∼ y) → Char c ⤇ [ y ]
  Cat  : ∀ {e₁ e₂ w₁ w₂ w} → e₁ ⤇ w₁ → e₂ ⤇ w₂ → w₁ ++ w₂ ≋ w → e₁ ∙ e₂ ⤇ w
  Veeˡ : ∀ {e₁ e₂ w} → e₁ ⤇ w → e₁ ∨ e₂ ⤇ w
  Veeʳ : ∀ {e₁ e₂ w} → e₂ ⤇ w → e₁ ∨ e₂ ⤇ w
  Fix  : ∀ {e w} → e [ μ e / zero ] ⤇ w → μ e ⤇ w

data _≈_ : ∀ {e w w′} → REL (e ⤇ w) (e ⤇ w′) (c ⊔ ℓ) where
  Eps  : Eps ≈ Eps
  Char : ∀ {c y y′} → (c∼y : c ∼ y) → (c∼y′ : c ∼ y′) → Char c∼y ≈ Char c∼y′
  Cat  :
    ∀ {e₁ e₂ w w₁ w₂ w₁′ w₂′ e₁⤇w₁ e₁⤇w₁′ e₂⤇w₂ e₂⤇w₂′} →
    (e₁⤇w₁≈e₁⤇w′ : _≈_ {e₁} {w₁} {w₁′} e₁⤇w₁ e₁⤇w₁′) →
    (e₂⤇w₂≈e₂⤇w′ : _≈_ {e₂} {w₂} {w₂′} e₂⤇w₂ e₂⤇w₂′) →
    (eq : w₁ ++ w₂ ≋ w) → (eq′ : w₁′ ++ w₂′ ≋ w) →
    Cat e₁⤇w₁ e₂⤇w₂ eq ≈ Cat e₁⤇w₁′ e₂⤇w₂′ eq′
  Veeˡ :
    ∀ {e₁ e₂ w w′ e₁⤇w e₁⤇w′} →
    (e₁⤇w≈e₁⤇w′ : _≈_ {e₁} {w} {w′} e₁⤇w e₁⤇w′) →
    Veeˡ {e₂ = e₂} e₁⤇w ≈ Veeˡ e₁⤇w′
  Veeʳ :
    ∀ {e₁ e₂ w w′ e₂⤇w e₂⤇w′} →
    (e₂⤇w≈e₂⤇w′ : _≈_ {e₂} {w} {w′} e₂⤇w e₂⤇w′) →
    Veeʳ {e₁} e₂⤇w ≈ Veeʳ e₂⤇w′
  Fix  :
    ∀ {e w w′ e[μe/0]⤇w e[μe/0]⤇w′} →
    (e[μe/0]⤇w≈e[μe/0]⤇w′ : _≈_ {e [ μ e / zero ]} {w} {w′} e[μe/0]⤇w e[μe/0]⤇w′) →
    Fix {e} e[μe/0]⤇w ≈ Fix e[μe/0]⤇w′
