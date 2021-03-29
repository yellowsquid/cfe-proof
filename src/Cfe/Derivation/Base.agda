{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (REL; Setoid)

module Cfe.Derivation.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over renaming (Carrier to C; _≈_ to _∼_)

open import Cfe.Expression over hiding (_≋_)
open import Data.Fin
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid over
open import Level using (_⊔_)

infix 5 _⤇_
infix 4 _≈_

data _⤇_ : Expression 0 → List C → Set (c ⊔ ℓ) where
  Eps : ε ⤇ []
  Char : ∀ {c y} → (c∼y : c ∼ y) → Char c ⤇ [ y ]
  Cat : ∀ {e₁ e₂ l₁ l₂ l} → e₁ ⤇ l₁ → e₂ ⤇ l₂ → l₁ ++ l₂ ≋ l → e₁ ∙ e₂ ⤇ l
  Veeˡ : ∀ {e₁ e₂ l} → e₁ ⤇ l → e₁ ∨ e₂ ⤇ l
  Veeʳ : ∀ {e₁ e₂ l} → e₂ ⤇ l → e₁ ∨ e₂ ⤇ l
  Fix : ∀ {e l} → e [ μ e / zero ] ⤇ l → μ e ⤇ l

data _≈_ : ∀ {e l l′} → REL (e ⤇ l) (e ⤇ l′) (c ⊔ ℓ) where
  Eps : Eps ≈ Eps
  Char : ∀ {c y y′} → (c∼y : c ∼ y) → (c∼y′ : c ∼ y′) → Char c∼y ≈ Char c∼y′
  Cat : ∀ {e₁ e₂ l l₁ l₂ l₁′ l₂′ e₁⤇l₁ e₁⤇l₁′ e₂⤇l₂ e₂⤇l₂′} →
          (e₁⤇l₁≈e₁⤇l′ : _≈_ {e₁} {l₁} {l₁′} e₁⤇l₁ e₁⤇l₁′) →
          (e₂⤇l₂≈e₂⤇l′ : _≈_ {e₂} {l₂} {l₂′} e₂⤇l₂ e₂⤇l₂′) →
          (eq : l₁ ++ l₂ ≋ l) → (eq′ : l₁′ ++ l₂′ ≋ l) →
          Cat e₁⤇l₁ e₂⤇l₂ eq ≈ Cat e₁⤇l₁′ e₂⤇l₂′ eq′
  Veeˡ : ∀ {e₁ e₂ l l′ e₁⤇l e₁⤇l′} →
         (e₁⤇l≈e₁⤇l′ : _≈_ {e₁} {l} {l′} e₁⤇l e₁⤇l′) →
         Veeˡ {e₂ = e₂} e₁⤇l ≈ Veeˡ e₁⤇l′
  Veeʳ : ∀ {e₁ e₂ l l′ e₂⤇l e₂⤇l′} →
         (e₂⤇l≈e₂⤇l′ : _≈_ {e₂} {l} {l′} e₂⤇l e₂⤇l′) →
         Veeʳ {e₁} e₂⤇l ≈ Veeʳ e₂⤇l′
  Fix : ∀ {e l l′ e[μe/0]⤇l e[μe/0]⤇l′} →
        (e[μe/0]⤇l≈e[μe/0]⤇l′ : _≈_ {e [ μ e / zero ]} {l} {l′} e[μe/0]⤇l e[μe/0]⤇l′) →
        Fix {e} e[μe/0]⤇l ≈ Fix e[μe/0]⤇l′
