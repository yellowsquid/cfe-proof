{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Judgement.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Expression over renaming (shift to shiftₑ)
open import Cfe.Type over renaming (_∙_ to _∙ₜ_; _∨_ to _∨ₜ_)
open import Cfe.Type.Construct.Lift over
open import Data.Fin as F
open import Data.Fin.Properties
open import Data.Nat as ℕ hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Vec hiding (_⊛_) renaming (lookup to lookup′)
open import Level hiding (Lift) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality

record Context n : Set (c ⊔ lsuc ℓ) where
  field
    m : ℕ
    m≤n : m ℕ.≤ n
    Γ : Vec (Type ℓ ℓ) (n ∸ m)
    Δ : Vec (Type ℓ ℓ) m

-- Fin n → Fin n∸m

  lookup : (i : Fin n) → toℕ i ≥ m → Type ℓ ℓ
  lookup i i≥m = lookup′ Γ (reduce≥
      (F.cast (begin-equality
        n ≡˘⟨ m+n∸m≡n m n ⟩
        m ℕ.+ n ∸ m ≡⟨ +-∸-assoc m m≤n ⟩
        m ℕ.+ (n ∸ m) ∎) i)
      (begin
        m ≤⟨ i≥m ⟩
        toℕ i ≡˘⟨ toℕ-cast _ i ⟩
        toℕ (F.cast _ i) ∎))
    where
    open ≤-Reasoning

cons : ∀ {n} → Type ℓ ℓ → Context n → Context (suc n)
cons {n} τ Γ,Δ = record
  { m≤n = s≤s m≤n
  ; Γ = Γ
  ; Δ = τ ∷ Δ
  }
  where
  open Context Γ,Δ

shift : ∀ {n} → Context n → Context n
shift {n} Γ,Δ = record
  { m≤n = z≤n
  ; Γ = subst (Vec (Type ℓ ℓ)) (trans (sym (+-∸-assoc m m≤n)) (m+n∸m≡n m n)) (Δ ++ Γ)
  ; Δ = []
  }
  where
  open Context Γ,Δ

infix 2 _⊢_∶_

data _⊢_∶_ : {n : ℕ} → Context n → Expression n → Type ℓ ℓ → Set (c ⊔ lsuc ℓ) where
  Eps : ∀ {n} {Γ,Δ : Context n} → Γ,Δ ⊢ ε ∶ Lift ℓ ℓ τε
  Char : ∀ {n} {Γ,Δ : Context n} c → Γ,Δ ⊢ Char c ∶ Lift ℓ ℓ τ[ c ]
  Bot : ∀ {n} {Γ,Δ : Context n} → Γ,Δ ⊢ ⊥ ∶ Lift ℓ ℓ τ⊥
  Var : ∀ {n} {Γ,Δ : Context n} {i : Fin n} (i≥m : toℕ i ℕ.≥ Context.m Γ,Δ) → Γ,Δ ⊢ Var i ∶ Context.lookup Γ,Δ i i≥m
  Fix : ∀ {n} {Γ,Δ : Context n} {e τ} → cons τ Γ,Δ ⊢ e ∶ τ → Γ,Δ ⊢ μ e ∶ τ
  Cat : ∀ {n} {Γ,Δ : Context n} {e₁ e₂ τ₁ τ₂} → Γ,Δ ⊢ e₁ ∶ τ₁ → shift Γ,Δ ⊢ e₂ ∶ τ₂ → (τ₁⊛τ₂ : τ₁ ⊛ τ₂) → Γ,Δ ⊢ e₁ ∙ e₂ ∶ τ₁ ∙ₜ τ₂
  Vee : ∀ {n} {Γ,Δ : Context n} {e₁ e₂ τ₁ τ₂} → Γ,Δ ⊢ e₁ ∶ τ₁ → Γ,Δ ⊢ e₂ ∶ τ₂ → (τ₁#τ₂ : τ₁ # τ₂) → Γ,Δ ⊢ e₁ ∨ e₂ ∶ τ₁ ∨ₜ τ₂
