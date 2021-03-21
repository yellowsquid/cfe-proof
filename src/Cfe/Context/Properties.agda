{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; Symmetric)

module Cfe.Context.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Context.Base over as C
open import Cfe.Type over
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
