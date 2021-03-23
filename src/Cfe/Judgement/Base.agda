{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Judgement.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Context over
open import Cfe.Expression over
open import Cfe.Type over renaming (_∙_ to _∙ₜ_; _∨_ to _∨ₜ_)
open import Cfe.Type.Construct.Lift over
open import Data.Fin as F
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding (_⊛_)
open import Level hiding (Lift) renaming (suc to lsuc)

infix 2 _⊢_∶_

data _⊢_∶_ : {n : ℕ} → Context n → Expression n → Type ℓ ℓ → Set (c ⊔ lsuc ℓ) where
  Eps : ∀ {n} {Γ,Δ : Context n} → Γ,Δ ⊢ ε ∶ Lift ℓ ℓ τε
  Char : ∀ {n} {Γ,Δ : Context n} c → Γ,Δ ⊢ Char c ∶ Lift ℓ ℓ τ[ c ]
  Bot : ∀ {n} {Γ,Δ : Context n} → Γ,Δ ⊢ ⊥ ∶ Lift ℓ ℓ τ⊥
  Var : ∀ {n} {Γ,Δ : Context n} {i} (i≥m : toℕ i ≥ _) → Γ,Δ ⊢ Var i ∶ lookup (Context.Γ Γ,Δ) (reduce≥′ (Context.m≤n Γ,Δ) i≥m)
  Fix : ∀ {n} {Γ,Δ : Context n} {e τ} → cons Γ,Δ τ ⊢ e ∶ τ → Γ,Δ ⊢ μ e ∶ τ
  Cat : ∀ {n} {Γ,Δ : Context n} {e₁ e₂ τ₁ τ₂} → Γ,Δ ⊢ e₁ ∶ τ₁ → shift Γ,Δ ⊢ e₂ ∶ τ₂ → (τ₁⊛τ₂ : τ₁ ⊛ τ₂) → Γ,Δ ⊢ e₁ ∙ e₂ ∶ τ₁ ∙ₜ τ₂
  Vee : ∀ {n} {Γ,Δ : Context n} {e₁ e₂ τ₁ τ₂} → Γ,Δ ⊢ e₁ ∶ τ₁ → Γ,Δ ⊢ e₂ ∶ τ₂ → (τ₁#τ₂ : τ₁ # τ₂) → Γ,Δ ⊢ e₁ ∨ e₂ ∶ τ₁ ∨ₜ τ₂
