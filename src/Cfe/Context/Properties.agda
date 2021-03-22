{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; Symmetric)

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

cast-involutive : ∀ {a A k m n} .(k≡m : k ≡ m) .(m≡n : m ≡ n) .(k≡n : _) xs → C.cast m≡n (C.cast {a} {A} k≡m xs) ≡ C.cast k≡n xs
cast-involutive {k = zero} {zero} {zero} k≡m m≡n k≡n [] = refl
cast-involutive {k = suc _} {suc _} {suc _} k≡m m≡n k≡n (x ∷ xs) = cong (x ∷_) (cast-involutive (cong ℕ.pred k≡m) (cong ℕ.pred m≡n) (cong ℕ.pred k≡n) xs)

cast-insert : ∀ {a A m n} xs .(m≡n : _) i j .(_ : toℕ i ≡ toℕ j) y → C.cast {a} {A} {suc m} {suc n} (cong suc m≡n) (insert xs i y) ≡ insert (C.cast m≡n xs) j y
cast-insert [] m≡n zero zero _ y = refl
cast-insert (x ∷ xs) m≡n zero zero _ y = refl
cast-insert {m = suc _} {n = suc _} (x ∷ xs) m≡n (suc i) (suc j) i≡j y = cong (x ∷_) (cast-insert xs (cong ℕ.pred m≡n) i j (cong ℕ.pred i≡j) y)

wkn₁-shift : ∀ {n} (Γ,Δ : Context n) i i≥m τ → shift (wkn₁ Γ,Δ i i≥m τ) ≋ wkn₁ (shift Γ,Δ) i z≤n τ
wkn₁-shift record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i i≥m τ =
  refl ,
  eq Δ Γ m≤n i i≥m τ ,
  refl
  where
  eq : ∀ {a A m n} xs ys .(m≤n : m ℕ.≤ n) i (i≥m : toℕ i ≥ m) y →
       C.cast {a} {A}
         (trans (sym (+-∸-assoc m (≤-step m≤n))) (m+n∸m≡n m (suc n)))
         (xs ++ C.cast (sym (+-∸-assoc 1 m≤n)) (insert ys (F.cast (+-∸-assoc 1 m≤n) (reduce≥′ (≤-step m≤n) i i≥m)) y)) ≡
       C.cast refl (insert (C.cast (trans (sym (+-∸-assoc m m≤n)) (m+n∸m≡n m n)) (xs ++ ys)) (F.cast refl i) y)
  eq [] [] m≤n zero i≥m y = refl
  eq [] (x ∷ ys) m≤n zero i≥m y = refl
  eq [] (x ∷ ys) m≤n (suc i) i≥m y = cong (x ∷_) (eq [] ys z≤n i z≤n y)
  eq {m = suc m} {suc n} (x ∷ xs) ys m≤n (suc i) (s≤s i≥m) y = cong (x ∷_) (eq xs ys (pred-mono m≤n) i i≥m y)

wkn₂-shift : ∀ {n} (Γ,Δ : Context n) i i≤m τ → shift (wkn₂ Γ,Δ i i≤m τ) ≋ wkn₁ (shift Γ,Δ) i z≤n τ
wkn₂-shift record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i i≤m τ =
  refl ,
  eq Δ Γ m≤n i i≤m τ ,
  refl
  where
  eq : ∀ {a A m n} xs ys .(m≤n : m ℕ.≤ n) i (i≤m : toℕ i ℕ.≤ m) y →
       C.cast {a} {A}
         (trans (sym (+-∸-assoc (suc m) (s≤s m≤n))) (m+n∸m≡n (suc m) (suc n)))
         (insert xs (fromℕ< (s≤s i≤m)) y ++ ys) ≡
       C.cast
         (sym (+-∸-assoc 1 z≤n))
         (insert (C.cast (trans (sym (+-∸-assoc m m≤n)) (m+n∸m≡n m n)) (xs ++ ys))
                 (F.cast (+-∸-assoc 1 z≤n) (reduce≥′ (≤-step z≤n) i z≤n)) y)
  eq [] [] m≤n zero i≤m y = refl
  eq [] (x ∷ ys) m≤n zero i≤m y = cong (λ z → y ∷ x ∷ z) (sym (cast-involutive refl refl refl ys))
  eq {m = suc m} {suc n} (x ∷ xs) ys m≤n zero i≤m y =
    cong (λ z → y ∷ x ∷ z)
         (sym (cast-involutive (trans (sym (+-∸-assoc m (pred-mono m≤n))) (m+n∸m≡n m n))
                               refl
                               (trans (sym (+-∸-assoc m (pred-mono m≤n))) (m+n∸m≡n m n))
                               (xs ++ ys)))
  eq {m = suc m} {suc n} (x ∷ xs) ys m≤n (suc i) (s≤s i≤m) y = cong (x ∷_) (eq xs ys (pred-mono m≤n) i i≤m y)

rotate₁-shift : ∀ {n} (Γ,Δ : Context n) i j i≥m i≤j → rotate₁ (shift Γ,Δ) i j z≤n i≤j ≋ shift (rotate₁ Γ,Δ i j i≥m i≤j)
rotate₁-shift record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i j i≥m i≤j =
  refl ,
  eq Γ Δ m≤n i j i≥m i≤j ,
  refl
  where
  eq : ∀ {a A m n} xs ys .(m≤n : m ℕ.≤ n) i j i≥m i≤j →
    rotate {a} {A} i j i≤j (C.cast (trans (sym (+-∸-assoc m m≤n)) (m+n∸m≡n m n)) (ys ++ xs)) ≡
    C.cast (trans (sym (+-∸-assoc m m≤n)) (m+n∸m≡n m n)) (ys ++ rotate (reduce≥′ m≤n i i≥m) (reduce≥′ m≤n j (≤-trans i≥m i≤j)) (reduce≥′-mono m≤n i j i≥m i≤j) xs)
  eq {m = zero} {suc _} (x ∷ xs) [] _ zero j _ _ = sym (cast-insert xs refl j j refl x)
  eq {m = zero} (x ∷ xs) [] _ (suc i) (suc j) _ i≤j = cong (x ∷_) (eq xs [] z≤n i j z≤n (pred-mono i≤j))
  eq {m = suc _} {suc _} xs (y ∷ ys) m≤n (suc i) (suc j) (s≤s i≥m) (s≤s i≤j) = cong (y ∷_) (eq xs ys (pred-mono m≤n) i j i≥m i≤j)

transfer-cons : ∀ {n} (Γ,Δ : Context n) i j i<m 1+j≥m τ → transfer (cons Γ,Δ τ) (suc i) (suc j) (s≤s i<m) (s≤s 1+j≥m) ≋ cons (transfer Γ,Δ i j i<m 1+j≥m) τ
transfer-cons record { m = suc m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i j i<m 1+j≥m τ =
  refl , eq₁ Γ Δ m≤n (fromℕ< i<m) j 1+j≥m τ , eq₂ Δ (fromℕ< i<m) τ
  where
  eq₁ : ∀ {a A m n} xs ys .(m≤n : suc m ℕ.≤ n) (i : Fin (suc m)) j .(1+j≥m : _) y →
    insert′ {a} {A} xs (s≤s m≤n) (λ ()) (reduce≥′ (≤-step m≤n) (suc j) 1+j≥m) (lookup (y ∷ ys) (suc i)) ≡
    insert′ xs m≤n (λ ()) (reduce≥′ (pred-mono (≤-step m≤n)) j (pred-mono 1+j≥m)) (lookup ys i)
  eq₁ {m = zero} {suc _} xs ys m≤n i j 1+j≥m y = refl
  eq₁ {m = suc m} xs ys m≤n i zero 1+j≥m x = ⊥-elim (<⇒≱ (s≤s (s≤s z≤n)) (≤-recomputable 1+j≥m))
  eq₁ {m = suc m} {suc _} xs (x ∷ ys) m≤n i (suc j) 1+j≥m y = refl

  eq₂ : ∀ {a A m} ys (i : Fin (suc m)) y →
    remove′ {a} {A} (y ∷ ys) (λ ()) (suc i) ≡ y ∷ remove′ ys (λ ()) i
  eq₂ (x ∷ ys) i y = refl

transfer-shift : ∀ {n} (Γ,Δ : Context n) i j i<m 1+j≥m → rotate₁ (shift Γ,Δ) i j z≤n (pred-mono (≤-trans i<m 1+j≥m)) ≋ shift (transfer Γ,Δ i j i<m 1+j≥m)
transfer-shift record { m = suc m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i j i<m 1+j≥m =
  refl ,
  eq Γ Δ m≤n i j i<m 1+j≥m ,
  refl
  where
  eq : ∀ {a A m n} xs ys .(m≤n : suc m ℕ.≤ n) i j i<m .(1+j≥m : _) →
    rotate {a} {A} i j
      (pred-mono {_} {suc (toℕ j)} (≤-trans i<m 1+j≥m))
      (C.cast (trans (sym (+-∸-assoc (suc m) m≤n)) (m+n∸m≡n (suc m) n)) (ys ++ xs)) ≡
    C.cast
      (trans (sym (+-∸-assoc m (pred-mono (≤-step m≤n)))) (m+n∸m≡n (suc m) n))
      ( remove′ ys (λ ()) (fromℕ< i<m) ++
        insert′ xs m≤n (λ ())
          (reduce≥′ (pred-mono (≤-step m≤n)) j (pred-mono 1+j≥m))
          (lookup ys (fromℕ< i<m)))
  eq {m = zero} {suc _} xs (y ∷ []) m≤n zero zero i<m 1+j≥m = refl
  eq {m = zero} {suc (suc _)} (x ∷ xs) (y ∷ []) _ zero (suc j) _ _ = cong (x ∷_) (eq xs (y ∷ []) (s≤s z≤n) zero j (s≤s z≤n) (s≤s z≤n))
  eq {m = zero} {suc _} _ (_ ∷ []) _ (suc _) _ (s≤s ()) _
  eq {m = suc _} {suc _} _ (_ ∷ _) _ _ zero _ 1+j≥m = ⊥-elim (<⇒≱ (s≤s (s≤s z≤n)) (≤-recomputable 1+j≥m))
  eq {m = suc _} {suc (suc _)} xs (x ∷ y ∷ ys) m≤n zero (suc j) i<m 1+j≥m = cong (y ∷_) (eq xs (x ∷ ys) (pred-mono m≤n) zero j (s≤s z≤n) (pred-mono 1+j≥m))
  eq {m = suc _} {suc (suc _)} xs (x ∷ y ∷ ys) m≤n (suc i) (suc j) (s≤s i<m) 1+j≥m = cong (x ∷_) (eq xs (y ∷ ys) (pred-mono m≤n) i j i<m (pred-mono 1+j≥m))
