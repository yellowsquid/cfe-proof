{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Judgement.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Context over
  renaming
  ( wkn₁ to cwkn₁
  ; wkn₂ to cwkn₂
  ; rotate to crotate
  ; rotate₁ to crotate₁
  ; transfer to ctransfer
  ; _≋_ to _≋ᶜ_
  )
open import Cfe.Expression over
open import Cfe.Judgement.Base over
open import Data.Empty
open import Data.Fin as F
open import Data.Fin.Properties hiding (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Product
open import Data.Vec
open import Data.Vec.Properties
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

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

rotate₁ : ∀ {n} {Γ,Δ : Context n} {e τ} → Γ,Δ ⊢ e ∶ τ → ∀ i j i≥m i≤j → crotate₁ Γ,Δ i j i≥m i≤j ⊢ rotate e i j i≤j ∶ τ
rotate₁ Eps i j i≥m i≤j = Eps
rotate₁ (Char c) i j i≥m i≤j = Char c
rotate₁ Bot i j i≥m i≤j = Bot
rotate₁ {suc n} {Γ,Δ = record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ }} (Var {i = k} k≥m) i j i≥m i≤j with i F.≟ k
... | yes refl = congᵗ (τ≡τ′ Γ m≤n i j i≥m i≤j) (Var (≤-trans i≥m i≤j))
  where
    τ≡τ′ : ∀ {a A m n} xs m≤n i j i≥m i≤j → lookup {a} {A} (crotate (reduce≥′ {m} {n} m≤n i i≥m) (reduce≥′ m≤n j (≤-trans i≥m i≤j)) (reduce≥′-mono m≤n i j i≥m i≤j) xs) (reduce≥′ m≤n j (≤-trans i≥m i≤j)) ≡ lookup xs (reduce≥′ m≤n i i≥m)
    τ≡τ′ {m = zero} (x ∷ xs) m≤n zero j i≥m i≤j = insert-lookup xs j x
    τ≡τ′ {m = zero} (x ∷ xs) m≤n (suc i) (suc j) i≥m i≤j = τ≡τ′ xs z≤n i j z≤n (pred-mono i≤j)
    τ≡τ′ {m = suc m} {suc n} xs m≤n (suc i) (suc j) (s≤s i≥m) (s≤s i≤j) = τ≡τ′ xs (pred-mono m≤n) i j i≥m i≤j
... | no i≢k = congᵗ (τ≡τ′ Γ m≤n i j k i≢k i≥m i≤j k≥m) (Var (punchIn-punchOut≥m i j k i≢k i≥m i≤j k≥m))
  where
  punchIn-punchOut≥m : ∀ {m n} (i j k : Fin (suc n)) (i≢k : i ≢ k) → toℕ i ≥ m → i F.≤ j → toℕ k ≥ m → toℕ (punchIn j (punchOut i≢k)) ≥ m
  punchIn-punchOut≥m {zero} _ _ _ _ _ _ _ = z≤n
  punchIn-punchOut≥m {suc _} zero _ zero i≢k _ _ _ = ⊥-elim (i≢k refl)
  punchIn-punchOut≥m {suc _} zero zero (suc _) _ _ _ k≥m = k≥m
  punchIn-punchOut≥m {suc _} {suc _} (suc i) (suc j) (suc k) i≢k (s≤s i≥m) (s≤s i≤j) (s≤s k≥m) = s≤s (punchIn-punchOut≥m i j k (i≢k ∘ cong suc) i≥m i≤j k≥m)

  τ≡τ′ : ∀ {a A m n} xs m≤n i j k i≢k i≥m i≤j k≥m →
    lookup {a} {A}
      (crotate
        (reduce≥′ {m} {suc n} m≤n i i≥m)
        (reduce≥′ m≤n j (≤-trans i≥m i≤j))
        (reduce≥′-mono m≤n i j i≥m i≤j) xs)
        (reduce≥′
          m≤n
          (punchIn j (punchOut i≢k))
          (punchIn-punchOut≥m i j k i≢k i≥m i≤j k≥m)) ≡
    lookup xs (reduce≥′ m≤n k k≥m)
  τ≡τ′ {m = zero} _ _ zero _ zero i≢k _ _ _ = ⊥-elim (i≢k refl)
  τ≡τ′ {m = zero} (_ ∷ _) _ zero zero (suc _) _ _ _ _ = refl
  τ≡τ′ {m = zero} (_ ∷ _ ∷ _) _ zero (suc _) (suc zero) _ _ _ _ = refl
  τ≡τ′ {m = zero} (x ∷ _ ∷ xs) _ zero (suc j) (suc (suc k)) _ _ _ _ = τ≡τ′ (x ∷ xs) z≤n zero j (suc k) (λ ()) z≤n z≤n z≤n
  τ≡τ′ {m = zero} (_ ∷ _ ∷ _) _ (suc _) (suc _) zero _ _ _ _ = refl
  τ≡τ′ {m = zero} (_ ∷ x ∷ xs) _ (suc i) (suc j) (suc k) i≢k _ i≤j _ = τ≡τ′ (x ∷ xs) z≤n i j k (i≢k ∘ cong suc) z≤n (pred-mono i≤j) z≤n
  τ≡τ′ {m = suc m} {suc _} xs m≤n (suc i) (suc j) (suc k) i≢k i≥m i≤j k≥m = τ≡τ′ xs (pred-mono m≤n) i j k (i≢k ∘ cong suc) (pred-mono i≥m) (pred-mono i≤j) (pred-mono k≥m)
rotate₁ (Fix Γ,Δ⊢e∶τ) i j i≥m i≤j = Fix (rotate₁ Γ,Δ⊢e∶τ (suc i) (suc j) (s≤s i≥m) (s≤s i≤j))
rotate₁ {Γ,Δ = Γ,Δ} (Cat Γ,Δ⊢e₁∶τ₁ Δ++Γ,∙⊢e₂∶τ₂ τ₁⊛τ₂) i j i≥m i≤j = Cat (rotate₁ Γ,Δ⊢e₁∶τ₁ i j i≥m i≤j) (congᶜ (rotate₁-shift Γ,Δ i j i≥m i≤j) (rotate₁ Δ++Γ,∙⊢e₂∶τ₂ i j z≤n i≤j)) τ₁⊛τ₂
rotate₁ (Vee Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e₂∶τ₂ τ₁#τ₂) i j i≥m i≤j = Vee (rotate₁ Γ,Δ⊢e₁∶τ₁ i j i≥m i≤j) (rotate₁ Γ,Δ⊢e₂∶τ₂ i j i≥m i≤j) τ₁#τ₂

transfer : ∀ {n} {Γ,Δ : Context n} {e τ} → Γ,Δ ⊢ e ∶ τ → ∀ i j i<m 1+j≥m → ctransfer Γ,Δ i j i<m 1+j≥m ⊢ rotate e i j (pred-mono (≤-trans i<m 1+j≥m)) ∶ τ
transfer Eps i j i<m 1+j≥m = Eps
transfer (Char c) i j i<m 1+j≥m = Char c
transfer Bot i j i<m 1+j≥m = Bot
transfer {suc n} {Γ,Δ = record { m = suc m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ }} (Var {i = k} k≥m) i j i<m 1+j≥m with suc m ℕ.≟ 0 | i F.≟ k
... | no m≢0 | yes refl = ⊥-elim (<⇒≱ i<m k≥m)
... | no m≢0 | no i≢k = congᵗ (τ≡τ′ Γ (lookup Δ (fromℕ< i<m)) m≢0 m≤n i j k i<m 1+j≥m k≥m i≢k) (Var (punchIn≥m i j k i≢k i<m 1+j≥m k≥m))
  where
  punchIn≥m : ∀ {m n} (i j k : Fin (suc n)) (i≢k : i ≢ k) → toℕ i ℕ.< m → .(suc (toℕ j) ≥ m) → toℕ k ≥ m → toℕ (punchIn j (punchOut i≢k)) ≥ ℕ.pred m
  punchIn≥m {suc zero} _ _ _ _ _ _ _ = z≤n
  punchIn≥m {suc (suc _)} zero _ zero i≢k _ _ _ = ⊥-elim (i≢k refl)
  punchIn≥m {suc (suc _)} zero zero (suc _) _ _ _ (s≤s k≥m) = ≤-step k≥m
  punchIn≥m {suc (suc _)} {suc _} (suc i) zero (suc k) i≢k (s≤s i<m) 1+j≥m (s≤s k≥m) = ⊥-elim (<⇒≱ (s≤s (s≤s z≤n)) (≤-recomputable 1+j≥m))
  punchIn≥m {suc (suc _)} zero (suc _) (suc zero) _ _ _ (s≤s k≥m) = k≥m
  punchIn≥m {suc (suc _)} zero (suc j) (suc (suc k)) _ _ 1+j≥m (s≤s k≥m) = s≤s (punchIn≥m zero j (suc k) (λ ()) (s≤s z≤n) (pred-mono 1+j≥m) k≥m)
  punchIn≥m {suc (suc _)} {suc _} (suc i) (suc j) (suc k) i≢k (s≤s i<m) 1+j≥m (s≤s k≥m) = s≤s (punchIn≥m i j k (i≢k ∘ cong suc) i<m (pred-mono 1+j≥m) k≥m)

  τ≡τ′ : ∀ {a A m n} xs y m≢0 .(m≤n : _) i j k i<m .(1+j≥m : _) k≥m i≢k →
    lookup
      (insert′ {a} {A} {m} {suc n} xs m≤n m≢0
        (reduce≥′ (pred-mono (≤-step m≤n)) j (pred-mono 1+j≥m))
        y)
      (reduce≥′
        (pred-mono (≤-step m≤n))
        (punchIn j (punchOut i≢k))
        (punchIn≥m i j k i≢k i<m 1+j≥m k≥m)) ≡
    lookup xs (reduce≥′ m≤n k k≥m)
  τ≡τ′ {m = suc zero} _ _ _ _ zero zero (suc _) _ _ (s≤s z≤n) _ = refl
  τ≡τ′ {m = suc zero} _ _ _ _ (suc _) zero (suc _) (s≤s ()) _ _ _
  τ≡τ′ {m = suc zero} (_ ∷ _) _ _ _ zero (suc _) (suc zero) _ _ (s≤s z≤n) _ = refl
  τ≡τ′ {m = suc zero} (_ ∷ xs) y _ _ zero (suc j) (suc (suc k)) _ _ (s≤s z≤n) _ = τ≡τ′ xs y (λ ()) (s≤s (z≤n)) zero j (suc k) (s≤s z≤n) (s≤s z≤n) (s≤s z≤n) (λ ())
  τ≡τ′ {m = suc (suc _)} _ _ _ _ _ zero _ _ 1+j≥m _ _ = ⊥-elim (<⇒≱ (s≤s (s≤s z≤n)) (≤-recomputable 1+j≥m))
  τ≡τ′ {m = suc (suc _)} _ _ _ _ zero _ (suc zero) _ _ (s≤s ()) _
  τ≡τ′ {m = suc (suc _)} {suc (suc _)} xs y _ m≤n zero (suc j) (suc (suc k)) _ 1+j≥m (s≤s k≥m) _ = τ≡τ′ xs y (λ ()) (pred-mono m≤n) zero j (suc k) (s≤s z≤n) (pred-mono 1+j≥m) k≥m (λ ())
  τ≡τ′ {m = suc (suc m)} xs y m≢0 m≤n (suc i) (suc j) (suc zero) (s≤s i<m) 1+j≥m (s≤s k≥m) i≢k = τ≡τ′ xs y (λ ()) (pred-mono m≤n) i j zero i<m (pred-mono 1+j≥m) k≥m (i≢k ∘ cong suc)
  τ≡τ′ {m = suc (suc m)} xs y m≢0 m≤n (suc i) (suc j) (suc (suc k)) (s≤s i<m) 1+j≥m (s≤s k≥m) i≢k = τ≡τ′ xs y (λ ()) (pred-mono m≤n) i j (suc k) i<m (pred-mono 1+j≥m) k≥m (i≢k ∘ cong suc)
transfer {Γ,Δ = Γ,Δ} {τ = τ} (Fix Γ,Δ⊢e∶τ) i j i<m 1+j≥m = Fix (congᶜ (transfer-cons Γ,Δ i j i<m 1+j≥m τ) (transfer Γ,Δ⊢e∶τ (suc i) (suc j) (s≤s i<m) (s≤s 1+j≥m)))
transfer {Γ,Δ = Γ,Δ} (Cat Γ,Δ⊢e₁∶τ₁ Δ++Γ,∙⊢e₂∶τ₂ τ₁⊛τ₂) i j i<m 1+j≥m = Cat (transfer Γ,Δ⊢e₁∶τ₁ i j i<m 1+j≥m) (congᶜ (transfer-shift Γ,Δ i j i<m 1+j≥m) (rotate₁ Δ++Γ,∙⊢e₂∶τ₂ i j z≤n (pred-mono (≤-trans i<m 1+j≥m)))) τ₁⊛τ₂
transfer (Vee Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e₂∶τ₂ τ₁#τ₂) i j i<m 1+j≥m = Vee (transfer Γ,Δ⊢e₁∶τ₁ i j i<m 1+j≥m) (transfer Γ,Δ⊢e₂∶τ₂ i j i<m 1+j≥m) τ₁#τ₂
