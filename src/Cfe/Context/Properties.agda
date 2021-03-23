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

-- rotate₁-shift : ∀ {n i j} Γ,Δ i≥m i≤j → rotate₁ {n} {i} {j} (shift Γ,Δ) z≤n i≤j ≋ shift (rotate₁ Γ,Δ i≥m i≤j)
-- rotate₁-shift record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i≥m i≤j =
--   refl ,
--   eq Γ Δ m≤n i≥m i≤j ,
--   refl
--   where
--   eq : ∀ {a A m n i j} xs ys (m≤n : m ℕ.≤ n) i≥m i≤j → ?
--     -- rotate {a} {A} i j i≤j (C.cast (trans (sym (+-∸-assoc m m≤n)) (m+n∸m≡n m n)) (ys ++ xs)) ≡
--     -- C.cast (trans (sym (+-∸-assoc m m≤n)) (m+n∸m≡n m n)) (ys ++ rotate (reduce≥′ m≤n i i≥m) (reduce≥′ m≤n j (≤-trans i≥m i≤j)) (reduce≥′-mono m≤n i j i≥m i≤j) xs)
--   eq xs ys m≤n i≥m i≤j = ?
--   -- eq {m = zero} {suc _} (x ∷ xs) [] _ zero j _ _ = sym (cast-insert xs refl j j refl x)
--   -- eq {m = zero} (x ∷ xs) [] _ (suc i) (suc j) _ i≤j = cong (x ∷_) (eq xs [] z≤n i j z≤n (pred-mono i≤j))
--   -- eq {m = suc _} {suc _} xs (y ∷ ys) m≤n (suc i) (suc j) (s≤s i≥m) (s≤s i≤j) = cong (y ∷_) (eq xs ys (pred-mono m≤n) i j i≥m i≤j)

-- transfer-cons : ∀ {n i j} Γ,Δ i<m 1+j≥m τ → transfer {suc n} {suc i} {suc j} (cons Γ,Δ τ) (s≤s i<m) 1+j≥m ≋ cons (transfer Γ,Δ i<m (pred-mono 1+j≥m)) τ
-- transfer-cons record { m = suc m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i<m 1+j≥m τ =
--   refl , eq₁ Γ Δ m≤n (fromℕ< i<m) 1+j≥m τ , eq₂ Δ (fromℕ< i<m) τ
--   where
--   eq₁ : ∀ {a A m n j} xs ys (m≤n : suc m ℕ.≤ n) i 1+j≥m y → ? ≡ ?
--     -- insert′ {a} {A} xs (s≤s m≤n) (reduce≥′ (≤-step m≤n) 1+j≥m) (lookup (y ∷ ys) (suc i)) ≡
--     -- insert′ xs m≤n (reduce≥′ (pred-mono (≤-step m≤n)) (pred-mono 1+j≥m)) (lookup ys i)
--   eq₁ xs ys m≤n i 1+j≥m y = ?
--   -- eq₁ {m = zero} {suc _} xs ys m≤n i j 1+j≥m y = refl
--   -- eq₁ {m = suc m} xs ys m≤n i zero 1+j≥m x = ⊥-elim (<⇒≱ (s≤s (s≤s z≤n)) (≤-recomputable 1+j≥m))
--   -- eq₁ {m = suc m} {suc _} xs (x ∷ ys) m≤n i (suc j) 1+j≥m y = refl

--   eq₂ : ∀ {a A m} ys (i : Fin (suc m)) y →
--     remove′ {a} {A} (y ∷ ys) (suc i) ≡ y ∷ remove′ ys i
--   eq₂ (x ∷ ys) i y = refl

-- transfer-shift : ∀ {n i j} (Γ,Δ : Context n) i j i<m 1+j≥m → rotate₁ (shift Γ,Δ) z≤n (pred-mono (≤-trans i<m 1+j≥m)) ≋ shift (transfer Γ,Δ i j i<m 1+j≥m)
-- transfer-shift record { m = suc m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i j i<m 1+j≥m =
--   refl ,
--   eq Γ Δ m≤n i j i<m 1+j≥m ,
--   refl
--   where
--   eq : ∀ {a A m n} xs ys .(m≤n : suc m ℕ.≤ n) i j i<m .(1+j≥m : _) →
--     rotate {a} {A} i j
--       (pred-mono {_} {suc (toℕ j)} (≤-trans i<m 1+j≥m))
--       (C.cast (trans (sym (+-∸-assoc (suc m) m≤n)) (m+n∸m≡n (suc m) n)) (ys ++ xs)) ≡
--     C.cast
--       (trans (sym (+-∸-assoc m (pred-mono (≤-step m≤n)))) (m+n∸m≡n (suc m) n))
--       ( remove′ ys (λ ()) (fromℕ< i<m) ++
--         insert′ xs m≤n (λ ())
--           (reduce≥′ (pred-mono (≤-step m≤n)) j (pred-mono 1+j≥m))
--           (lookup ys (fromℕ< i<m)))
--   eq {m = zero} {suc _} xs (y ∷ []) m≤n zero zero i<m 1+j≥m = refl
--   eq {m = zero} {suc (suc _)} (x ∷ xs) (y ∷ []) _ zero (suc j) _ _ = cong (x ∷_) (eq xs (y ∷ []) (s≤s z≤n) zero j (s≤s z≤n) (s≤s z≤n))
--   eq {m = zero} {suc _} _ (_ ∷ []) _ (suc _) _ (s≤s ()) _
--   eq {m = suc _} {suc _} _ (_ ∷ _) _ _ zero _ 1+j≥m = ⊥-elim (<⇒≱ (s≤s (s≤s z≤n)) (≤-recomputable 1+j≥m))
--   eq {m = suc _} {suc (suc _)} xs (x ∷ y ∷ ys) m≤n zero (suc j) i<m 1+j≥m = cong (y ∷_) (eq xs (x ∷ ys) (pred-mono m≤n) zero j (s≤s z≤n) (pred-mono 1+j≥m))
--   eq {m = suc _} {suc (suc _)} xs (x ∷ y ∷ ys) m≤n (suc i) (suc j) (s≤s i<m) 1+j≥m = cong (x ∷_) (eq xs (y ∷ ys) (pred-mono m≤n) i j i<m (pred-mono 1+j≥m))
