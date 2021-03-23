{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Judgement.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Context over as C
  hiding
  ( shift≤ ; wkn₁ ; wkn₂ )
  renaming (_≋_ to _≋ᶜ_; ≋-sym to ≋ᶜ-sym; ≋-trans to ≋ᶜ-trans )
open import Cfe.Expression over as E
open import Cfe.Judgement.Base over
open import Data.Empty
open import Data.Fin as F hiding (splitAt)
open import Data.Fin.Properties hiding (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Product
open import Data.Vec
open import Data.Vec.Properties
open import Function
open import Relation.Binary.PropositionalEquality hiding (subst₂)
open import Relation.Nullary

private
  toℕ-punchIn : ∀ {n} i j → toℕ j ℕ.≤ toℕ (punchIn {n} i j)
  toℕ-punchIn zero j = n≤1+n (toℕ j)
  toℕ-punchIn (suc i) zero = ≤-refl
  toℕ-punchIn (suc i) (suc j) = s≤s (toℕ-punchIn i j)

  punchIn[i,j]≥m : ∀ {n m i j} → toℕ i ℕ.≤ m → toℕ j ≥ m → toℕ (punchIn {n} i j) ≥ suc m
  punchIn[i,j]≥m {i = zero} i≤m j≥m = s≤s j≥m
  punchIn[i,j]≥m {i = suc i} {suc j} (s≤s i≤m) (s≤s j≥m) = s≤s (punchIn[i,j]≥m i≤m j≥m)

congᶜ : ∀ {n} {Γ,Δ Γ,Δ′ : Context n} {e τ} → Γ,Δ ≋ᶜ Γ,Δ′ → Γ,Δ ⊢ e ∶ τ → Γ,Δ′ ⊢ e ∶ τ
congᶜ {Γ,Δ = Γ,Δ} {Γ,Δ′} (refl , refl , refl) Γ,Δ⊢e∶τ with ≤-irrelevant (Context.m≤n Γ,Δ) (Context.m≤n Γ,Δ′)
... | refl = Γ,Δ⊢e∶τ

congᵗ : ∀ {n} {Γ,Δ : Context n} {e τ τ′} → τ ≡ τ′ → Γ,Δ ⊢ e ∶ τ → Γ,Δ ⊢ e ∶ τ′
congᵗ refl Γ,Δ⊢e∶τ = Γ,Δ⊢e∶τ

wkn₁ : ∀ {n} {Γ,Δ : Context n} {e τ} → Γ,Δ ⊢ e ∶ τ → ∀ {i} i≥m τ′ → C.wkn₁ {i = i} Γ,Δ i≥m τ′ ⊢ wkn e i ∶ τ
wkn₁ Eps i≥m τ′ = Eps
wkn₁ (Char c) i≥m τ′ = Char c
wkn₁ Bot i≥m τ′ = Bot
wkn₁ {Γ,Δ = record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ }} (Var {i = j} j≥m) {i = i} i≥m τ′ =
  congᵗ (τ≡τ′ Γ m≤n i≥m j≥m τ′) (Var (≤-trans j≥m (toℕ-punchIn i j)))
  where
  τ≡τ′ : ∀ {a A n m i j} xs (m≤n : m ℕ.≤ n) (i≥m : toℕ i ≥ _) j≥m x →
    lookup {a} {A}
      (insert′ xs (s≤s m≤n) (reduce≥′ (≤-step m≤n) i≥m) x)
      (reduce≥′ (≤-step m≤n) (≤-trans j≥m (toℕ-punchIn i j))) ≡
    lookup xs (reduce≥′ m≤n j≥m)
  τ≡τ′ {i = zero} {j} (y ∷ xs) z≤n z≤n z≤n x = refl
  τ≡τ′ {i = suc i} {zero} (y ∷ xs) z≤n z≤n z≤n x = refl
  τ≡τ′ {i = suc i} {suc j} (y ∷ xs) z≤n z≤n z≤n x = τ≡τ′ {i = i} xs z≤n z≤n z≤n x
  τ≡τ′ {i = suc i} {suc j} xs (s≤s m≤n) (s≤s i≥m) (s≤s j≥m) x = τ≡τ′ xs m≤n i≥m j≥m x
wkn₁ (Fix Γ,Δ⊢e∶τ) i≥m τ′ = Fix (wkn₁ Γ,Δ⊢e∶τ (s≤s i≥m) τ′)
wkn₁ {Γ,Δ = Γ,Δ} (Cat Γ,Δ⊢e₁∶τ₁ Δ++Γ,∙⊢e₂∶τ₂ τ₁⊛τ₂) i≥m τ′ = Cat (wkn₁ Γ,Δ⊢e₁∶τ₁ i≥m τ′) (congᶜ (≋ᶜ-sym (shift≤-wkn₁-comm Γ,Δ z≤n i≥m τ′)) (wkn₁ Δ++Γ,∙⊢e₂∶τ₂ z≤n τ′)) τ₁⊛τ₂
wkn₁ (Vee Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e₂∶τ₂ τ₁#τ₂) i≥m τ′ = Vee (wkn₁ Γ,Δ⊢e₁∶τ₁ i≥m τ′) (wkn₁ Γ,Δ⊢e₂∶τ₂ i≥m τ′) τ₁#τ₂

wkn₂ : ∀ {n} {Γ,Δ : Context n} {e τ} → Γ,Δ ⊢ e ∶ τ → ∀ {i} i≤m τ′ → C.wkn₂ {i = i} Γ,Δ i≤m τ′ ⊢ wkn e i ∶ τ
wkn₂ Eps i≤m τ′ = Eps
wkn₂ (Char c) i≤m τ′ = Char c
wkn₂ Bot i≤m τ′ = Bot
wkn₂ {Γ,Δ = record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ }}(Var {i = j} j≥m) i≤m τ′ = congᵗ (τ≡τ′ Γ m≤n i≤m j≥m) (Var (punchIn[i,j]≥m i≤m j≥m))
  where
  τ≡τ′ : ∀ {a A n m i j} xs (m≤n : m ℕ.≤ n) (i≤m : toℕ i ℕ.≤ _) (j≥m : toℕ j ≥ _) →
         lookup {a} {A} xs (reduce≥′ (s≤s m≤n) (punchIn[i,j]≥m i≤m j≥m)) ≡
         lookup xs (reduce≥′ m≤n j≥m)
  τ≡τ′ {i = zero} _ z≤n _ _ = refl
  τ≡τ′ {i = zero} _ (s≤s _) _ _ = refl
  τ≡τ′ {i = suc i} {suc j} xs (s≤s m≤n) (s≤s i≤m) (s≤s j≥m) = τ≡τ′ xs m≤n i≤m j≥m
wkn₂ (Fix Γ,Δ⊢e∶τ) i≤m τ′ = Fix (wkn₂ Γ,Δ⊢e∶τ (s≤s i≤m) τ′)
wkn₂ {Γ,Δ = Γ,Δ} (Cat Γ,Δ⊢e₁∶τ₁ Δ++Γ,∙⊢e₂∶τ₂ τ₁⊛τ₂) i≤m τ′ = Cat (wkn₂ Γ,Δ⊢e₁∶τ₁ i≤m τ′) (congᶜ (≋ᶜ-sym (shift≤-wkn₂-comm-≤ Γ,Δ z≤n i≤m τ′)) (wkn₁ Δ++Γ,∙⊢e₂∶τ₂ z≤n τ′)) τ₁⊛τ₂
wkn₂ (Vee Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e₂∶τ₂ τ₁#τ₂) i≤m τ′ = Vee (wkn₂ Γ,Δ⊢e₁∶τ₁ i≤m τ′) (wkn₂ Γ,Δ⊢e₂∶τ₂ i≤m τ′) τ₁#τ₂

shift≤ : ∀ {n} {Γ,Δ : Context n} {e τ} → Γ,Δ ⊢ e ∶ τ → ∀ {i} (i≤m : i ℕ.≤ _) → C.shift≤ Γ,Δ i≤m ⊢ e ∶ τ
shift≤ Eps i≤m = Eps
shift≤ (Char c) i≤m = Char c
shift≤ Bot i≤m = Bot
shift≤ {Γ,Δ = record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ }} (Var {i = j} j≥m) i≤m =
  congᵗ (τ≡τ′ Γ Δ m≤n i≤m j≥m) (Var (≤-trans i≤m j≥m))
  where
  τ≡τ′ : ∀ {a A n m i j} xs ys (m≤n : m ℕ.≤ n) (i≤m : i ℕ.≤ m) (j≥m : toℕ j ≥ m) →
         lookup {a} {A} (drop′ m≤n i≤m (ys ++ xs)) (reduce≥′ (≤-trans i≤m m≤n) (≤-trans i≤m j≥m)) ≡
         lookup xs (reduce≥′ m≤n j≥m)
  τ≡τ′ xs [] z≤n z≤n z≤n = refl
  τ≡τ′ {j = suc j} xs (x ∷ ys) (s≤s m≤n) z≤n (s≤s j≥m) = τ≡τ′ xs ys m≤n z≤n j≥m
  τ≡τ′ {j = suc j} xs (x ∷ ys) (s≤s m≤n) (s≤s i≤m) (s≤s j≥m) = τ≡τ′ xs ys m≤n i≤m j≥m
shift≤ {Γ,Δ = Γ,Δ} {τ = τ} (Fix Γ,Δ⊢e∶τ) {i} i≤m = Fix (congᶜ (shift≤-wkn₂-comm-> Γ,Δ z≤n i≤m τ) (shift≤ Γ,Δ⊢e∶τ (s≤s i≤m)))
shift≤ {Γ,Δ = Γ,Δ} (Cat Γ,Δ⊢e₁∶τ₁ Δ++Γ,∙⊢e₂∶τ₂ τ₁⊛τ₂) i≤m =
  Cat (shift≤ Γ,Δ⊢e₁∶τ₁ i≤m)
      (congᶜ (≋ᶜ-trans (shift≤-identity (shift Γ,Δ))
                       (≋ᶜ-sym (shift≤-idem Γ,Δ z≤n i≤m)))
             (shift≤ Δ++Γ,∙⊢e₂∶τ₂ z≤n))
      τ₁⊛τ₂
shift≤ (Vee Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e₂∶τ₂ τ₁#τ₂) i≤m = Vee (shift≤ Γ,Δ⊢e₁∶τ₁ i≤m) (shift≤ Γ,Δ⊢e₂∶τ₂ i≤m) τ₁#τ₂

subst₁ : ∀ {n} {Γ,Δ : Context n} {e τ i τ′} (i≥m : toℕ i ≥ _) → C.wkn₁ Γ,Δ i≥m τ′ ⊢ e ∶ τ → ∀ {e′} → Γ,Δ ⊢ e′ ∶ τ′ → Γ,Δ ⊢ e [ e′ / i ] ∶ τ
subst₁ _ Eps Γ,Δ⊢e′∶τ′ = Eps
subst₁ _ (Char c) Γ,Δ⊢e′∶τ′ = Char c
subst₁ _ Bot Γ,Δ⊢e′∶τ′ = Bot
subst₁ {Γ,Δ = record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ }} {i = i} {τ′} i≥m (Var {i = j} j≥m) Γ,Δ⊢e′∶τ′ with  i F.≟ j
... | no i≢j =
  congᵗ (sym (τ≡τ′ Γ m≤n i≢j i≥m j≥m τ′)) (Var (punchOut≥m i≢j i≥m j≥m))
  where
  punchOut≥m : ∀ {n m i j} → (i≢j : i ≢ j) → toℕ {suc n} i ≥ m → toℕ j ≥ m → toℕ (punchOut i≢j) ≥ m
  punchOut≥m {m = zero} _ z≤n _ = z≤n
  punchOut≥m {n = suc _} {.(suc _)} {suc _} {suc _} i≢j (s≤s i≥m) (s≤s j≥m) = s≤s (punchOut≥m (i≢j ∘ cong suc) i≥m j≥m)

  τ≡τ′ : ∀ {a A n m i j} xs (m≤n : m ℕ.≤ n) (i≢j : i ≢ j) (i≥m : toℕ i ≥ m) (j≥m : toℕ j ≥ m) x →
        lookup {a} {A} (insert′ xs (s≤s m≤n) (reduce≥′ (≤-step m≤n) i≥m) x) (reduce≥′ (≤-step m≤n) j≥m) ≡
        lookup xs (reduce≥′ m≤n (punchOut≥m i≢j i≥m j≥m))
  τ≡τ′ {i = zero} {zero} xs m≤n i≢j i≥m j≥m x = ⊥-elim (i≢j refl)
  τ≡τ′ {n = suc n} {i = zero} {suc j} xs z≤n i≢j z≤n z≤n x = refl
  τ≡τ′ {n = suc n} {i = suc i} {zero} (y ∷ xs) z≤n i≢j z≤n z≤n x = refl
  τ≡τ′ {n = suc n} {i = suc i} {suc j} (y ∷ xs) z≤n i≢j z≤n z≤n x = τ≡τ′ xs z≤n (i≢j ∘ cong suc) z≤n z≤n x
  τ≡τ′ {n = suc n} {i = suc i} {suc j} xs (s≤s m≤n) i≢j (s≤s i≥m) (s≤s j≥m) x = τ≡τ′ xs m≤n (i≢j ∘ cong suc) i≥m j≥m x
... | yes refl with ≤-irrelevant i≥m j≥m
... | refl = congᵗ (sym (τ≡τ′ Γ m≤n i≥m τ′)) Γ,Δ⊢e′∶τ′
  where
  τ≡τ′ : ∀ {a A n m i} xs (m≤n : m ℕ.≤ n) (i≥m : toℕ i ≥ m) x →
         lookup {a} {A} (insert′ xs (s≤s m≤n) (reduce≥′ (≤-step m≤n) i≥m) x) (reduce≥′ (≤-step m≤n) i≥m) ≡ x
  τ≡τ′ {i = zero} xs z≤n z≤n x = refl
  τ≡τ′ {i = suc i} (y ∷ xs) z≤n z≤n x = insert-lookup xs i x
  τ≡τ′ {i = suc i} xs (s≤s m≤n) (s≤s i≥m) = τ≡τ′ xs m≤n i≥m
subst₁ {τ = τ} i≥m (Fix Γ,Δ⊢e∶τ) Γ,Δ⊢e′∶τ′ = Fix (subst₁ (s≤s i≥m) Γ,Δ⊢e∶τ (wkn₂ Γ,Δ⊢e′∶τ′ z≤n τ))
subst₁ {Γ,Δ = Γ,Δ} {i = i} {τ′} i≥m (Cat Γ,Δ⊢e₁∶τ₁ Δ++Γ,∙⊢e₂∶τ₂ τ₁⊛τ₂) Γ,Δ⊢e′∶τ′ = Cat (subst₁ i≥m Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e′∶τ′) (subst₁ z≤n (congᶜ (shift≤-wkn₁-comm Γ,Δ z≤n i≥m τ′) Δ++Γ,∙⊢e₂∶τ₂) (shift≤ Γ,Δ⊢e′∶τ′ z≤n)) τ₁⊛τ₂
subst₁ i≥m (Vee Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e₂∶τ₂ τ₁#τ₂) Γ,Δ⊢e′∶τ′ = Vee (subst₁ i≥m Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e′∶τ′) (subst₁ i≥m Γ,Δ⊢e₂∶τ₂ Γ,Δ⊢e′∶τ′) τ₁#τ₂


subst₂ : ∀ {n} {Γ,Δ : Context n} {e τ i τ′} (i≤m : toℕ i ℕ.≤ _) → C.wkn₂ Γ,Δ i≤m τ′ ⊢ e ∶ τ → ∀ {e′} → shift Γ,Δ ⊢ e′ ∶ τ′ → Γ,Δ ⊢ e [ e′ / i ] ∶ τ
subst₂ i≤m Eps Γ,Δ⊢e′∶τ′ = Eps
subst₂ i≤m (Char c) Γ,Δ⊢e′∶τ′ = Char c
subst₂ i≤m Bot Γ,Δ⊢e′∶τ′ = Bot
subst₂ {Γ,Δ = record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ }} {i = i} i≤m (Var {i = j} j>m) Γ,Δ⊢e′∶τ′ with i F.≟ j
... | yes refl = ⊥-elim (<⇒≱ j>m i≤m)
... | no i≢j = congᵗ (cong (lookup Γ) (τ≡τ′ m≤n i≢j i≤m j>m)) (Var (punchOut≥m i≢j i≤m j>m))
  where
  punchOut≥m : ∀ {n m i j} → (i≢j : i ≢ j) → toℕ {suc n} i ℕ.≤ m → toℕ j > m → toℕ (punchOut i≢j) ≥ m
  punchOut≥m {m = zero} i≢j i≤m j>m = z≤n
  punchOut≥m {m = suc _} {zero} {suc _} _ _ (s≤s j>m) = j>m
  punchOut≥m {n = suc _} {i = suc _} {suc _} i≢j (s≤s i≤m) (s≤s j>m) = s≤s (punchOut≥m (i≢j ∘ cong suc) i≤m j>m)

  τ≡τ′ : ∀ {n m i j} (m≤n : m ℕ.≤ n) (i≢j : i ≢ j) (i≤m : toℕ i ℕ.≤ m) (j>m : toℕ j > m) →
    reduce≥′ m≤n (punchOut≥m i≢j i≤m j>m) ≡ reduce≥′ (s≤s m≤n) j>m
  τ≡τ′ {m = zero} {zero} {suc _} m≤n i≢j z≤n (s≤s z≤n) = refl
  τ≡τ′ {m = suc _} {zero} {suc _} m≤n i≢j z≤n (s≤s j>m) = refl
  τ≡τ′ {n = suc _} {i = suc _} {suc _} (s≤s m≤n) i≢j (s≤s i≤m) (s≤s j>m) = τ≡τ′ m≤n (i≢j ∘ cong suc) i≤m j>m

subst₂ {Γ,Δ = Γ,Δ} {τ = τ} {τ′ = τ′} i≤m (Fix Γ,Δ⊢e∶τ) Γ,Δ⊢e′∶τ′ =
  Fix (subst₂ (s≤s i≤m)
              (congᶜ (≋ᶜ-sym (wkn₂-comm Γ,Δ z≤n i≤m τ τ′)) Γ,Δ⊢e∶τ)
              (congᶜ (≋ᶜ-sym (shift≤-wkn₂-comm-≤ Γ,Δ z≤n z≤n τ)) (wkn₁ Γ,Δ⊢e′∶τ′ z≤n τ)))
subst₂ {Γ,Δ = Γ,Δ} {τ′ = τ′} i≤m (Cat Γ,Δ⊢e₁∶τ₁ Δ++Γ,∙⊢e₂∶τ₂ τ₁⊛τ₂) Γ,Δ⊢e′∶τ′ =
  Cat (subst₂ i≤m Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e′∶τ′)
      (subst₁ z≤n
              (congᶜ (shift≤-wkn₂-comm-≤ Γ,Δ z≤n i≤m τ′) Δ++Γ,∙⊢e₂∶τ₂)
              Γ,Δ⊢e′∶τ′)
      τ₁⊛τ₂
subst₂ i≤m (Vee Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e₂∶τ₂ τ₁#τ₂) Γ,Δ⊢e′∶τ′ = Vee (subst₂ i≤m Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e′∶τ′) (subst₂ i≤m Γ,Δ⊢e₂∶τ₂ Γ,Δ⊢e′∶τ′) τ₁#τ₂
