{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; Symmetric; Transitive)

module Cfe.Context.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Context.Base over as C
open import Cfe.Type over
open import Data.Empty
open import Data.Fin as F
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Product
open import Data.Vec
open import Function
open import Relation.Binary.PropositionalEquality

≋-sym : ∀ {n} → Symmetric (_≋_ {n})
≋-sym (refl , refl , refl) = refl , refl , refl

≋-trans : ∀ {n} → Transitive (_≋_ {n})
≋-trans (refl , refl , refl) (refl , refl , refl) = refl , refl , refl

i≤j⇒inject₁[i]≤1+j : ∀ {n i j} → i F.≤ j → inject₁ {n} i F.≤ suc j
i≤j⇒inject₁[i]≤1+j {i = zero} i≤j = z≤n
i≤j⇒inject₁[i]≤1+j {i = suc i} {suc j} (s≤s i≤j) = s≤s (i≤j⇒inject₁[i]≤1+j i≤j)

wkn₂-comm : ∀ {n i j} Γ,Δ i≤j j≤m τ₁ τ₂ → wkn₂ (wkn₂ {n} {i} Γ,Δ (≤-trans i≤j j≤m) τ₁) (s≤s j≤m) τ₂ ≋ wkn₂ (wkn₂ {i = j} Γ,Δ j≤m τ₂) (≤-trans (i≤j⇒inject₁[i]≤1+j i≤j) (s≤s j≤m)) τ₁
wkn₂-comm record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i≤j j≤m τ₁ τ₂ = refl , refl , eq Δ i≤j j≤m τ₁ τ₂
  where
  eq : ∀ {a A n m i j} ys (i≤j : i F.≤ j) (j≤m : toℕ {n} j ℕ.≤ m) y₁ y₂ →
       insert {a} {A} (insert ys (fromℕ< (s≤s (≤-trans i≤j j≤m))) y₁) (fromℕ< (s≤s (s≤s j≤m))) y₂ ≡
       insert (insert ys (fromℕ< (s≤s j≤m)) y₂) (fromℕ< (s≤s (≤-trans (i≤j⇒inject₁[i]≤1+j i≤j) (s≤s j≤m)))) y₁
  eq {i = zero} _ _ _ _ _ = refl
  eq {i = suc i} {j = suc j} (x ∷ ys) (s≤s i≤j) (s≤s j≤m) y₁ y₂ = cong (x ∷_) (eq ys i≤j j≤m y₁ y₂)

shift≤-identity : ∀ {n} Γ,Δ → shift≤ {n} Γ,Δ ≤-refl ≋ Γ,Δ
shift≤-identity record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } = refl , eq₁ Γ Δ m≤n , eq₂ Δ
  where
  eq₁ : ∀ {a A n m} xs ys (m≤n : m ℕ.≤ n) → drop′ {a} {A} m≤n ≤-refl (ys ++ xs) ≡ xs
  eq₁ xs [] z≤n = refl
  eq₁ xs (_ ∷ ys) (s≤s m≤n) = eq₁ xs ys m≤n

  eq₂ : ∀ {a A m} ys → take′ {a} {A} {m} ≤-refl ys ≡ ys
  eq₂ [] = refl
  eq₂ (x ∷ ys) = cong (x ∷_) (eq₂ ys)

shift≤-idem : ∀ {n i j} Γ,Δ i≤j j≤m → shift≤ {n} {i} (shift≤ {i = j} Γ,Δ j≤m) i≤j ≋ shift≤ Γ,Δ (≤-trans i≤j j≤m)
shift≤-idem record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i≤j j≤m = refl , eq₁ Γ Δ m≤n i≤j j≤m , eq₂ Δ i≤j j≤m
  where
  eq₁ : ∀ {a A n m i j} xs ys (m≤n : m ℕ.≤ n) (i≤j : i ℕ.≤ j) (j≤m : j ℕ.≤ m) →
        drop′ {a} {A} (≤-trans j≤m m≤n) i≤j (take′ j≤m ys ++ drop′ m≤n j≤m (ys ++ xs)) ≡
        drop′ m≤n (≤-trans i≤j j≤m) (ys ++ xs)
  eq₁ _ _ _ z≤n z≤n = refl
  eq₁ xs (y ∷ ys) (s≤s m≤n) z≤n (s≤s j≤m) = cong (y ∷_) (eq₁ xs ys m≤n z≤n j≤m)
  eq₁ xs (_ ∷ ys) (s≤s m≤n) (s≤s i≤j) (s≤s j≤m) = eq₁ xs ys m≤n i≤j j≤m

  eq₂ : ∀ {a A m i j} ys (i≤j : i ℕ.≤ j) (j≤m : j ℕ.≤ m) → take′ {a} {A} i≤j (take′ j≤m ys) ≡ take′ (≤-trans i≤j j≤m) ys
  eq₂ ys z≤n j≤m = refl
  eq₂ (y ∷ ys) (s≤s i≤j) (s≤s j≤m) = cong (y ∷_) (eq₂ ys i≤j j≤m)

shift≤-wkn₁-comm : ∀ {n i j} Γ,Δ i≤m j≥m τ →
                   shift≤ {i = i} (wkn₁ {n} {j} Γ,Δ j≥m τ) i≤m ≋
                   wkn₁ (shift≤ Γ,Δ i≤m) (≤-trans i≤m j≥m) τ
shift≤-wkn₁-comm record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i≤m j≥m τ =
  refl , eq Γ Δ m≤n i≤m j≥m τ , refl
  where
  eq : ∀ {a A n m i j} xs ys (m≤n : m ℕ.≤ n) (i≤m : i ℕ.≤ m) (j≥m : toℕ {suc n} j ≥ m) y →
       drop′ {a} {A} (≤-step m≤n) i≤m (ys ++ (insert′ xs (s≤s m≤n) (reduce≥′ (≤-step m≤n) j≥m) y)) ≡
       insert′ (drop′ m≤n i≤m (ys ++ xs)) (s≤s (≤-trans i≤m m≤n)) (reduce≥′ (≤-step (≤-trans i≤m m≤n)) (≤-trans i≤m j≥m)) y
  eq _ [] z≤n z≤n _ _ = refl
  eq {j = suc _} xs (x ∷ ys) (s≤s m≤n) z≤n (s≤s j≥m) y = cong (x ∷_) (eq xs ys m≤n z≤n j≥m y)
  eq {j = suc _} xs (_ ∷ ys) (s≤s m≤n) (s≤s i≤m) (s≤s j≥m) y = eq xs ys m≤n i≤m j≥m y

shift≤-wkn₂-comm-≤ : ∀ {n i j} Γ,Δ i≤j j≤m τ →
                     shift≤ {i = i} (wkn₂ {n} {j} Γ,Δ j≤m τ) (≤-trans i≤j (≤-step j≤m)) ≋
                     wkn₁ (shift≤ Γ,Δ (≤-trans i≤j j≤m)) i≤j τ
shift≤-wkn₂-comm-≤ record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i≤j j≤m τ =
  refl , eq₁ Γ Δ m≤n i≤j j≤m τ , eq₂ Δ i≤j j≤m τ
  where
  eq₁ : ∀ {a A n m i j} xs ys (m≤n : m ℕ.≤ n) (i≤j : i ℕ.≤ toℕ {suc n} j) (j≤m : toℕ j ℕ.≤ m) y →
        drop′ {a} {A} (s≤s m≤n) (≤-trans i≤j (≤-step j≤m)) (insert ys (fromℕ< (s≤s j≤m)) y ++ xs) ≡
        insert′
          (drop′ m≤n (≤-trans i≤j j≤m) (ys ++ xs))
          (s≤s (≤-trans (≤-trans i≤j j≤m) m≤n))
          (reduce≥′ (≤-step (≤-trans (≤-trans i≤j j≤m) m≤n)) i≤j)
          y
  eq₁ {j = zero} _ _ _ z≤n _ _ = refl
  eq₁ {j = suc j} xs (x ∷ ys) (s≤s m≤n) z≤n (s≤s j≤m) y = cong (x ∷_) (eq₁ xs ys m≤n z≤n j≤m y)
  eq₁ {j = suc j} xs (x ∷ ys) (s≤s m≤n) (s≤s i≤j) (s≤s j≤m) y = eq₁ xs ys m≤n i≤j j≤m y

  eq₂ : ∀ {a A n m i j} ys (i≤j : i ℕ.≤ toℕ {suc n} j) (j≤m : toℕ j ℕ.≤ m) y →
        take′ {a} {A} (≤-trans i≤j (≤-step j≤m)) (insert ys (fromℕ< (s≤s j≤m)) y) ≡
        take′ (≤-trans i≤j j≤m) ys
  eq₂ {j = zero} _ z≤n _ _ = refl
  eq₂ {j = suc _} _ z≤n _ _ = refl
  eq₂ {j = suc zero} (_ ∷ _) (s≤s z≤n) (s≤s _) _ = refl
  eq₂ {j = suc (suc _)} (x ∷ ys) (s≤s i≤j) (s≤s j≤m) y = cong (x ∷_) (eq₂ ys i≤j j≤m y)

shift≤-wkn₂-comm-> : ∀ {n i j} Γ,Δ i≤j j≤m τ →
                     shift≤ {i = suc j} (wkn₂ {n} {i} Γ,Δ (≤-trans i≤j j≤m) τ) (s≤s j≤m) ≋
                     wkn₂ (shift≤ Γ,Δ j≤m) i≤j τ
shift≤-wkn₂-comm-> record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i≤j j≤m τ = refl , eq₁ Γ Δ m≤n i≤j j≤m τ , eq₂ Δ m≤n i≤j j≤m τ
  where
  eq₁ : ∀ {a A n m i j} xs ys (m≤n : m ℕ.≤ n) (i≤j : toℕ {suc n} i ℕ.≤ j) (j≤m : j ℕ.≤ m) y →
        drop′ {a} {A} (s≤s m≤n) (s≤s j≤m) (insert ys (fromℕ< (s≤s (≤-trans i≤j j≤m))) y ++ xs) ≡
        drop′ m≤n j≤m (ys ++ xs)
  eq₁ {i = zero} _ _ _ _ _ _ = refl
  eq₁ {i = suc _} xs (_ ∷ ys) (s≤s m≤n) (s≤s i≤j) (s≤s j≤m) y = eq₁ xs ys m≤n i≤j j≤m y

  eq₂ : ∀ {a A n m i j} ys (m≤n : m ℕ.≤ n) (i≤j : toℕ {suc n} i ℕ.≤ j) (j≤m : j ℕ.≤ m) y →
        take′ {a} {A} (s≤s j≤m) (insert ys (fromℕ< (s≤s (≤-trans i≤j j≤m))) y) ≡
        insert (take′ j≤m ys) (fromℕ< (s≤s i≤j)) y
  eq₂ {i = zero} _ _ _ _ _ = refl
  eq₂ {i = suc _} (x ∷ ys) (s≤s m≤n) (s≤s i≤j) (s≤s j≤m) y = cong (x ∷_) (eq₂ ys m≤n i≤j j≤m y)

shift≤-toVec : ∀ {n i} (Γ,Δ : Context n) (i≤m : i ℕ.≤ _) → toVec (shift≤ Γ,Δ i≤m) ≡ toVec Γ,Δ
shift≤-toVec record { m = .0 ; m≤n = z≤n ; Γ = Γ ; Δ = [] } z≤n = refl
shift≤-toVec {suc n} record { m = .(suc _) ; m≤n = (s≤s m≤n) ; Γ = Γ ; Δ = (x ∷ Δ) } z≤n = cong (x ∷_) (shift≤-toVec (record { m≤n = m≤n ; Γ = Γ ; Δ = Δ }) z≤n)
shift≤-toVec {suc n} record { m = .(suc _) ; m≤n = (s≤s m≤n) ; Γ = Γ ; Δ = (x ∷ Δ) } (s≤s i≤m) = cong (x ∷_) (shift≤-toVec (record { m≤n = m≤n ; Γ = Γ ; Δ = Δ }) i≤m)
