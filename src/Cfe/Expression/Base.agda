{-# OPTIONS --without-K --safe #-}

module Cfe.Expression.Base
  {ℓ} (A : Set ℓ)
  where

open import Data.Nat

data Expression : ℕ → Set ℓ where
  ⊥ : {n : ℕ} → Expression n
  ε : {n : ℕ} → Expression n
  Char : {n : ℕ} → A → Expression n
  _∨_ : {n : ℕ} → Expression n → Expression n → Expression n
  _∙_ : {n : ℕ} → Expression n → Expression n → Expression n
  Var : {m : ℕ} → (n : ℕ) → Expression (suc (m + n))
  μ : {n : ℕ} → Expression (suc n) → Expression n
