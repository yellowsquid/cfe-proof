{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Judgement.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Expression over
open import Cfe.Type over renaming (_∙_ to _∙ₜ_; _∨_ to _∨ₜ_)
open import Cfe.Type.Construct.Lift over
open import Data.Fin
open import Data.Nat as ℕ hiding (_⊔_)
open import Data.Vec hiding (_⊛_)
open import Level hiding (Lift) renaming (suc to lsuc)

infix 2 _,_⊢_∶_

data _,_⊢_∶_ {m} {n} : Vec (Type ℓ ℓ) m → Vec (Type ℓ ℓ) n → Expression (n ℕ.+ m) → Type ℓ ℓ → Set (c ⊔ lsuc ℓ) where
  Eps : ∀ {Γ Δ} → Γ , Δ ⊢ ε ∶ Lift ℓ ℓ τε
  Char : ∀ {Γ Δ} c → Γ , Δ ⊢ Char c ∶ Lift ℓ ℓ τ[ c ]
  Bot : ∀ {Γ Δ} → Γ , Δ ⊢ ⊥ ∶ Lift ℓ ℓ τ⊥
  Var : ∀ {Γ Δ i} i≥n → Γ , Δ ⊢ Var i ∶ lookup Γ (reduce≥ i i≥n)
  Fix : ∀ {Γ Δ e τ} → Γ , τ ∷ Δ ⊢ e ∶ τ → Γ , Δ ⊢ μ e ∶ τ
  Cat : ∀ {Γ Δ e e′ τ τ′} → Γ , Δ ⊢ e ∶ τ → Δ ++ Γ , [] ⊢ e′ ∶ τ′ → τ ⊛ τ′ → Γ , Δ ⊢ e ∙ e′ ∶ τ ∙ₜ τ′
  Vee : ∀ {Γ Δ e e′ τ τ′} → Γ , Δ ⊢ e ∶ τ → Γ , Δ ⊢ e′ ∶ τ′ → τ # τ′ → Γ , Δ ⊢ e ∨ e′ ∶ τ ∨ₜ τ′
