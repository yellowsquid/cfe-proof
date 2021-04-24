{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; REL; Setoid)

module Cfe.Judgement.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Context over
open import Cfe.Expression over
open import Cfe.Fin using (zero; raise!>)
open import Cfe.Type over renaming (_∙_ to _∙ᵗ_; _∨_ to _∨ᵗ_)
open import Data.Fin using (inject₁)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (∃-syntax)
open import Data.Vec using (lookup)
open import Level using (_⊔_) renaming (suc to lsuc)

infix 2 _⊢_∶_

private
  variable
    n : ℕ
    ctx : Context n

data _⊢_∶_ : {n : ℕ} → Context n → Expression n → Type ℓ ℓ → Set (c ⊔ lsuc ℓ) where
  Eps  : ctx ⊢ ε ∶ τε
  Char : ∀ c → ctx ⊢ Char c ∶ τ[ c ]
  Bot  : ctx ⊢ ⊥ ∶ τ⊥
  Var  : ∀ j → ctx ⊢ Var (raise!> {i = guard ctx} j) ∶ lookup (Γ,Δ ctx) (raise!> j)
  Fix  : ∀ {e τ} → wkn₂ ctx zero τ ⊢ e ∶ τ → ctx ⊢ μ e ∶ τ
  Cat  : ∀ {e₁ e₂ τ₁ τ₂} →
         ctx ⊢ e₁ ∶ τ₁ →
         shift ctx zero ⊢ e₂ ∶ τ₂ →
         (τ₁⊛τ₂ : τ₁ ⊛ τ₂) →
         ctx ⊢ e₁ ∙ e₂ ∶ τ₁ ∙ᵗ τ₂
  Vee  : ∀ {e₁ e₂ τ₁ τ₂} →
         ctx ⊢ e₁ ∶ τ₁ →
         ctx ⊢ e₂ ∶ τ₂ →
         (τ₁#τ₂ : τ₁ # τ₂) →
         ctx ⊢ e₁ ∨ e₂ ∶ τ₁ ∨ᵗ τ₂
