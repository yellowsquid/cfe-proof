{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Judgement.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Expression over as E
open import Cfe.Type over renaming (_∙_ to _∙ₜ_; _∨_ to _∨ₜ_)
open import Cfe.Type.Construct.Lift over
open import Data.Fin as F
open import Data.Nat as ℕ hiding (_⊔_)
open import Data.Vec hiding (_⊛_)
open import Level hiding (Lift) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality

infix 2 _,_⊢_∶_
infix 4 _≅_

data _,_⊢_∶_ : {m : ℕ} → {n : ℕ} → Vec (Type ℓ ℓ) m → Vec (Type ℓ ℓ) n → Expression (n ℕ.+ m) → Type ℓ ℓ → Set (c ⊔ lsuc ℓ) where
  Eps : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} → Γ , Δ ⊢ ε ∶ Lift ℓ ℓ τε
  Char : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} c → Γ , Δ ⊢ Char c ∶ Lift ℓ ℓ τ[ c ]
  Bot : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} → Γ , Δ ⊢ ⊥ ∶ Lift ℓ ℓ τ⊥
  Var : ∀ {m n : ℕ} {Γ : Vec _ m} {Δ : Vec _ n} {i : Fin (n ℕ.+ m)} (i≥n : toℕ i ≥ n) → Γ , Δ ⊢ Var i ∶ lookup Γ (reduce≥ i i≥n)
  Fix : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} {e τ} → Γ , τ ∷ Δ ⊢ e ∶ τ → Γ , Δ ⊢ μ e ∶ τ
  Cat : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} {e₁ e₂ τ₁ τ₂} → Γ , Δ ⊢ e₁ ∶ τ₁ → Δ ++ Γ , [] ⊢ e₂ ∶ τ₂ → (τ₁⊛τ₂ : τ₁ ⊛ τ₂) → Γ , Δ ⊢ e₁ ∙ e₂ ∶ τ₁ ∙ₜ τ₂
  Vee : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} {e₁ e₂ τ₁ τ₂} → Γ , Δ ⊢ e₁ ∶ τ₁ → Γ , Δ ⊢ e₂ ∶ τ₂ → (τ₁#τ₂ : τ₁ # τ₂) → Γ , Δ ⊢ e₁ ∨ e₂ ∶ τ₁ ∨ₜ τ₂

vcast : ∀ {a A m n} → .(m ≡ n) → Vec {a} A m → Vec A n
vcast {n = ℕ.zero} eq [] = []
vcast {n = suc n} eq (x ∷ xs) = x ∷ vcast (suc-injective eq) xs
  where
  open import Data.Nat.Properties using (suc-injective)

data _≅_ {a A} : {m n : ℕ} → Vec {a} A m → Vec A n → Set a where
  []≅[] : [] ≅ []
  _∷_ : ∀ {m n x y} {xs : Vec _ m} {ys : Vec _ n} → (x≡y : x ≡ y) → xs ≅ ys → x ∷ xs ≅ y ∷ ys
