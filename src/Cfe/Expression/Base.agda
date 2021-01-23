{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Expression.Base
  {a ℓ} (setoid : Setoid a ℓ)
  where

open Setoid setoid renaming (Carrier to A)

open import Cfe.Language setoid renaming (_∙_ to _∙ₗ_)
open import Data.Fin
open import Data.Nat
open import Data.Vec

data Expression : ℕ → Set a where
  ⊥ : {n : ℕ} → Expression n
  ε : {n : ℕ} → Expression n
  Char : {n : ℕ} → A → Expression n
  _∨_ : {n : ℕ} → Expression n → Expression n → Expression n
  _∙_ : {n : ℕ} → Expression n → Expression n → Expression n
  Var : {n : ℕ} → Fin n → Expression n
  μ : {n : ℕ} → Expression (suc n) → Expression n

〚_〛 : {n : ℕ} → Expression n → Vec Language n → Language
〚 ⊥ 〛 _ = ∅
〚 ε 〛 _ = ｛ε｝
〚 Char c 〛 _ = ｛ c ｝
〚 e₁ ∨ e₂ 〛 γ = 〚 e₁ 〛 γ ∪ 〚 e₂ 〛 γ
〚 e₁ ∙ e₂ 〛 γ = 〚 e₁ 〛 γ ∙ₗ 〚 e₂ 〛 γ
〚 Var n 〛 γ = lookup γ n
〚 μ e 〛 γ = fix (λ X → 〚 e 〛 (X ∷ γ))
