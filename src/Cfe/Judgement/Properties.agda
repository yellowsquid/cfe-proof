{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Judgement.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Context over renaming (wkn₁ to cwkn₁; wkn₂ to cwkn₂; _≋_ to _≋ᶜ_)
open import Cfe.Expression over
open import Cfe.Judgement.Base over
open import Data.Fin
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Product
open import Data.Vec
open import Relation.Binary.PropositionalEquality

toℕ-punchIn : ∀ {n} i j → toℕ j ℕ.≤ toℕ (punchIn {n} i j)
toℕ-punchIn zero j = n≤1+n (toℕ j)
toℕ-punchIn (suc i) zero = ≤-refl
toℕ-punchIn (suc i) (suc j) = s≤s (toℕ-punchIn i j)

congᶜ : ∀ {n} {Γ,Δ Γ,Δ′ : Context n} {e τ} → Γ,Δ ≋ᶜ Γ,Δ′ → Γ,Δ ⊢ e ∶ τ → Γ,Δ′ ⊢ e ∶ τ
congᶜ {Γ,Δ = Γ,Δ} {Γ,Δ′} (refl , refl , refl) Γ,Δ⊢e∶τ with ≤-irrelevant (Context.m≤n Γ,Δ) (Context.m≤n Γ,Δ′)
... | refl = Γ,Δ⊢e∶τ

congᵗ : ∀ {n} {Γ,Δ : Context n} {e τ τ′} → τ ≡ τ′ → Γ,Δ ⊢ e ∶ τ → Γ,Δ ⊢ e ∶ τ′
congᵗ refl Γ,Δ⊢e∶τ = Γ,Δ⊢e∶τ

wkn₁ : ∀ {n} {Γ,Δ : Context n} {e τ} → Γ,Δ ⊢ e ∶ τ → ∀ i τ′ i≥m → cwkn₁ Γ,Δ i i≥m τ′ ⊢ wkn e i ∶ τ
wkn₁ Eps i τ′ i≥m = Eps
wkn₁ (Char c) i τ′ i≥m = Char c
wkn₁ Bot i τ′ i≥m = Bot
wkn₁ {Γ,Δ = Γ,Δ} (Var {i = j} j≥m) i τ′ i≥m = congᵗ (τ≡τ′ Γ,Δ i j i≥m j≥m τ′) (Var (≤-trans j≥m (toℕ-punchIn i j)))
  where
  open Context Γ,Δ
  τ≡τ′ : ∀ {n} (Γ,Δ : Context n) i j i≥m j≥m τ → lookup (Context.Γ (cwkn₁ Γ,Δ i i≥m τ)) (reduce≥′ (≤-step (Context.m≤n Γ,Δ)) (punchIn i j) (≤-trans j≥m (toℕ-punchIn i j))) ≡ lookup (Context.Γ Γ,Δ) (reduce≥′ (Context.m≤n Γ,Δ) j j≥m)
  τ≡τ′ {suc _} record { m = zero ; m≤n = _ ; Γ = (_ ∷ _) ; Δ = _ } zero zero _ _ _ = refl
  τ≡τ′ {suc n} record { m = zero ; m≤n = _ ; Γ = (_ ∷ Γ) ; Δ = Δ } zero (suc j) _ _ τ = τ≡τ′ (record { m≤n = z≤n ; Γ = Γ ; Δ = Δ }) zero j z≤n z≤n τ
  τ≡τ′ {suc n} record { m = zero ; m≤n = _ ; Γ = (_ ∷ _) ; Δ = _ } (suc _) zero _ _ τ = refl
  τ≡τ′ {suc n} record { m = zero ; m≤n = _ ; Γ = (_ ∷ Γ) ; Δ = Δ } (suc i) (suc j) _ _ τ = τ≡τ′ (record { m≤n = z≤n ; Γ = Γ ; Δ = Δ}) i j z≤n z≤n τ
  τ≡τ′ {suc n} record { m = (suc m) ; m≤n = (s≤s m≤n) ; Γ = Γ ; Δ = (_ ∷ Δ) } (suc i) (suc j) (s≤s i≥m) (s≤s j≥m) τ = τ≡τ′ (record { m≤n = m≤n ; Γ = Γ ; Δ = Δ}) i j i≥m j≥m τ
wkn₁ (Fix Γ,Δ⊢e∶τ) i τ′ i≥m = Fix (wkn₁ Γ,Δ⊢e∶τ (suc i) τ′ (s≤s i≥m))
wkn₁ {Γ,Δ = Γ,Δ} (Cat Γ,Δ⊢e₁∶τ₁ Δ++Γ,∙⊢e₂∶τ₂ τ₁⊛τ₂) i τ′ i≥m = Cat (wkn₁ Γ,Δ⊢e₁∶τ₁ i τ′ i≥m) (congᶜ (≋-sym (wkn₁-shift Γ,Δ i i≥m τ′)) (wkn₁ Δ++Γ,∙⊢e₂∶τ₂ i τ′ z≤n)) τ₁⊛τ₂
wkn₁ (Vee Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e₂∶τ₂ τ₁#τ₂) i τ′ i≥m = Vee (wkn₁ Γ,Δ⊢e₁∶τ₁ i τ′ i≥m) (wkn₁ Γ,Δ⊢e₂∶τ₂ i τ′ i≥m) τ₁#τ₂

wkn₂ : ∀ {n} {Γ,Δ : Context n} {e τ} → Γ,Δ ⊢ e ∶ τ → ∀ i τ′ i≤m → cwkn₂ Γ,Δ i i≤m τ′ ⊢ wkn e i ∶ τ
wkn₂ Eps i τ′ i≤m = Eps
wkn₂ (Char c) i τ′ i≤m = Char c
wkn₂ Bot i τ′ i≤m = Bot
wkn₂ {Γ,Δ = Γ,Δ} (Var {i = j} j≥m) i τ′ i≤m =
  congᵗ
    (τ≡τ′ (Context.Γ Γ,Δ) (Context.m≤n Γ,Δ) i j i≤m j≥m)
    (Var (punchIn[i,j]≥m i j i≤m j≥m))
  where
  punchIn[i,j]≥m : ∀ {m n} i j → toℕ i ℕ.≤ m → toℕ j ≥ m → toℕ (punchIn {n} i j) ≥ suc m
  punchIn[i,j]≥m {m} zero j i≤m j≥m = s≤s j≥m
  punchIn[i,j]≥m {suc m} (suc i) (suc j) (s≤s i≤m) (s≤s j≥m) = s≤s (punchIn[i,j]≥m i j i≤m j≥m)

  τ≡τ′ : ∀ {a A m n} xs m≤n i j i≤m j≥m → lookup {a} {A} xs (reduce≥′ {suc m} (s≤s m≤n) (punchIn {n} i j) (punchIn[i,j]≥m i j i≤m j≥m)) ≡ lookup xs (reduce≥′ m≤n j j≥m)
  τ≡τ′ {m = zero} xs m≤n zero j i≤m j≥m = refl
  τ≡τ′ {m = suc _} xs m≤n zero (suc j) i≤m (s≤s j≥m) = τ≡τ′ xs (pred-mono m≤n) zero j z≤n j≥m
  τ≡τ′ {m = suc _} xs m≤n (suc i) (suc j) (s≤s i≤m) (s≤s j≥m) = τ≡τ′ xs (pred-mono m≤n) i j i≤m j≥m
wkn₂ (Fix Γ,Δ⊢e∶τ) i τ′ i≤m = Fix (wkn₂ Γ,Δ⊢e∶τ (suc i) τ′ (s≤s i≤m))
wkn₂ {Γ,Δ = Γ,Δ} (Cat Γ,Δ⊢e₁∶τ₁ Δ++Γ,∙⊢e₂∶τ₂ τ₁⊛τ₂) i τ′ i≤m = Cat (wkn₂ Γ,Δ⊢e₁∶τ₁ i τ′ i≤m) (congᶜ (≋-sym (wkn₂-shift Γ,Δ i i≤m τ′)) (wkn₁ Δ++Γ,∙⊢e₂∶τ₂ i τ′ z≤n)) τ₁⊛τ₂
wkn₂ (Vee Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e₂∶τ₂ τ₁#τ₂) i τ′ i≤m = Vee (wkn₂ Γ,Δ⊢e₁∶τ₁ i τ′ i≤m) (wkn₂ Γ,Δ⊢e₂∶τ₂ i τ′ i≤m) τ₁#τ₂
