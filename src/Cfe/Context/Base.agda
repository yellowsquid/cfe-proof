{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; Rel)

module Cfe.Context.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Fin
open import Cfe.Type over using (Type) renaming (_≈_ to _≈ᵗ_; _≤_ to _≤ᵗ_)
open import Data.Fin hiding (_+_) renaming (zero to #0; suc to 1+_; _≤_ to _≤ᶠ_)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁)
open import Data.Nat using (ℕ; suc; _∸_; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (_×_)
open import Data.Vec using (Vec; []; insert; remove)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)
open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; module ≡-Reasoning)
open import Relation.Nullary.Decidable using (True)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Definitions

infix 4 _⊐_

record Context n : Set (c ⊔ lsuc ℓ) where
  constructor _⊐_
  field
    Γ,Δ     : Vec (Type ℓ ℓ) n
    guard   : Fin (suc n)

open Context public

∙,∙ : Context 0
∙,∙ = [] ⊐ #0

------------------------------------------------------------------------
-- Insertions

wkn₂ : ∀ (ctx : Context n) → Fin< (1+ guard ctx) → Type ℓ ℓ → Context (suc n)
wkn₂ (Γ,Δ ⊐ g) i τ = insert Γ,Δ (inject!< i) τ ⊐ 1+ g

wkn₁ : ∀ (ctx : Context n) → Fin> (inject₁ (guard ctx)) → Type ℓ ℓ → Context (suc n)
wkn₁ (Γ,Δ ⊐ g) i τ = insert Γ,Δ (raise!> i) τ ⊐ inject₁ g

------------------------------------------------------------------------
-- Modifications

shift : ∀ (ctx : Context n) → Fin< (1+ guard ctx) → Context n
shift (Γ,Δ ⊐ _) i = Γ,Δ ⊐ inject!< i

------------------------------------------------------------------------
-- Deletions

remove₂ : ∀ (ctx : Context (suc n)) → Fin< (guard ctx) → Context n
remove₂ (Γ,Δ ⊐ g) i = remove Γ,Δ (inject!< i) ⊐ predⁱ< i

remove₁ : ∀ (ctx : Context (suc n)) → Fin> (guard ctx) → Context n
remove₁ (Γ,Δ ⊐ g) i = remove Γ,Δ (raise!> i) ⊐ inject₁ⁱ> i

------------------------------------------------------------------------
-- Relations

-- infix 4 _≈_ _≤_

_≈_ : Rel (Context n) _
(Γ,Δ₁ ⊐ g₁) ≈ (Γ,Δ₂ ⊐ g₂) = g₁ ≡ g₂ × Pointwise _≈ᵗ_ Γ,Δ₁ Γ,Δ₂

_≤_ : Rel (Context n) _
(Γ,Δ₁ ⊐ g₁) ≤ (Γ,Δ₂ ⊐ g₂) = g₂ ≤ᶠ g₁ × Pointwise _≤ᵗ_ Γ,Δ₁ Γ,Δ₂
