{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; Rel)

module Cfe.Context.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Type over
open import Data.Empty
open import Data.Fin as F hiding (cast)
open import Data.Fin.Properties hiding (≤-trans)
open import Data.Nat as ℕ hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Vec
open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

cast : ∀ {a A m n} → .(m ≡ n) → Vec {a} A m → Vec {a} A n
cast {m = 0} {0} eq [] = []
cast {m = suc _} {suc n} eq (x ∷ xs) = x ∷ cast (cong ℕ.pred eq) xs

reduce≥′ : ∀ {m n} → .(m ℕ.≤ n) → (i : Fin n) → toℕ i ≥ m → Fin (n ∸ m)
reduce≥′ {ℕ.zero} {n} m≤n i i≥m = i
reduce≥′ {suc m} {suc n} m≤n (suc i) (s≤s i≥m) = reduce≥′ (pred-mono m≤n) i i≥m

private
  insert′ : ∀ {a A m n} → Vec {a} A (n ∸ m) → m ℕ.≤ n → m ≢ 0 → (i : Fin (n ∸ ℕ.pred m)) → A → Vec A (n ∸ ℕ.pred m)
  insert′ {a} {A} {ℕ.zero} {n} xs m≤n m≢0 i x = ⊥-elim (m≢0 refl)
  insert′ {a} {A} {suc ℕ.zero} {suc _} xs _ _ F.zero x = x ∷ xs
  insert′ {a} {A} {suc ℕ.zero} {suc (suc n)} (y ∷ xs) _ _ (suc i) x = y ∷ insert′ {m = suc ℕ.zero} {suc n} xs (s≤s z≤n) (λ ()) i x
  insert′ {a} {A} {suc (suc m)} {suc ℕ.zero} xs m≤n _ i x = ⊥-elim (<⇒≱ (s≤s (s≤s z≤n)) m≤n)
  insert′ {a} {A} {suc (suc m)} {suc (suc n)} xs m≤n _ i x = insert′ {m = suc m} xs (pred-mono m≤n) (λ ()) i x

  reduce≥′-mono : ∀ {m n} → .(m≤n : m ℕ.≤ n) → (i j : Fin n) → (i≥m : toℕ i ≥ m) → (i≤j : i F.≤ j) → reduce≥′ m≤n i i≥m F.≤ reduce≥′ m≤n j (≤-trans i≥m i≤j)
  reduce≥′-mono {ℕ.zero} {n} m≤n i j i≥m i≤j = i≤j
  reduce≥′-mono {suc m} {suc n} m≤n (suc i) (suc j) (s≤s i≥m) (s≤s i≤j) = reduce≥′-mono (pred-mono m≤n) i j i≥m i≤j

  remove′ : ∀ {a A m} → Vec {a} A m → .(m ≢ 0) → Fin m → Vec A (ℕ.pred m)
  remove′ (x ∷ xs) m≢0 F.zero = xs
  remove′ (x ∷ y ∷ xs) m≢0 (suc i) = x ∷ remove′ (y ∷ xs) (λ ()) i

  rotate : ∀ {a A n} → (i j : Fin n) → .(i F.≤ j) → Vec {a} A n → Vec A n
  rotate F.zero j i≤j (x ∷ xs) = insert xs j x
  rotate (suc i) (suc j) i≤j (x ∷ xs) = x ∷ (rotate i j (pred-mono i≤j) xs)

record Context n : Set (c ⊔ lsuc ℓ) where
  field
    m : ℕ
    m≤n : m ℕ.≤ n
    Γ : Vec (Type ℓ ℓ) (n ∸ m)
    Δ : Vec (Type ℓ ℓ) m

wkn₁ : ∀ {n} → (Γ,Δ : Context n) → (i : Fin (suc n)) → (toℕ i ≥ Context.m Γ,Δ) → Type ℓ ℓ → Context (suc n)
wkn₁ Γ,Δ i i≥m τ = record
  { m≤n = ≤-step m≤n
  ; Γ = cast (sym (+-∸-assoc 1 m≤n)) (insert Γ (F.cast (+-∸-assoc 1 m≤n) (reduce≥′ (≤-step m≤n) i i≥m)) τ)
  ; Δ = Δ
  }
  where
  open Context Γ,Δ

wkn₂ : ∀ {n} → (Γ,Δ : Context n) → (i : Fin (suc n)) → toℕ i ℕ.≤ Context.m Γ,Δ → Type ℓ ℓ → Context (suc n)
wkn₂ Γ,Δ i i≤m τ = record
  { m≤n = s≤s m≤n
  ; Γ = Γ
  ; Δ = insert Δ (fromℕ< (s≤s i≤m)) τ
  }
  where
  open Context Γ,Δ

rotate₁ : ∀ {n} → (Γ,Δ : Context n) → (i j : Fin n) → toℕ i ≥ Context.m Γ,Δ → (i F.≤ j) → Context n
rotate₁ {n} Γ,Δ i j i≥m i≤j = record
  { m≤n = m≤n
  ; Γ = rotate (reduce≥′ m≤n i i≥m) (reduce≥′ m≤n j (≤-trans i≥m i≤j)) (reduce≥′-mono m≤n i j i≥m i≤j) Γ
  ; Δ = Δ
  }
  where
  open Context Γ,Δ

rotate₂ : ∀ {n} → (Γ,Δ : Context n) → (i j : Fin n) → (toℕ j ℕ.< Context.m Γ,Δ) → (i F.≤ j) → Context n
rotate₂ {n} Γ,Δ i j j<m i≤j = record
  { m≤n = m≤n
  ; Γ = Γ
  ; Δ = rotate
    (fromℕ< (≤-trans (s≤s i≤j) j<m))
    (fromℕ< j<m)
    (begin
      toℕ (fromℕ< (≤-trans (s≤s i≤j) j<m)) ≡⟨ toℕ-fromℕ< (≤-trans (s≤s i≤j) j<m) ⟩
      toℕ i ≤⟨ i≤j ⟩
      toℕ j ≡˘⟨ toℕ-fromℕ< j<m ⟩
      toℕ (fromℕ< j<m) ∎)
    Δ
  }
  where
  open Context Γ,Δ
  open ≤-Reasoning

transfer : ∀ {n} → (Γ,Δ : Context n) → (i j : Fin n) → (toℕ i ℕ.< Context.m Γ,Δ) → (suc (toℕ j) ≥ Context.m Γ,Δ) → Context n
transfer {n} Γ,Δ i j i<m 1+j≥m with Context.m Γ,Δ ℕ.≟ 0
... | yes m≡0 = ⊥-elim (m<n⇒n≢0 i<m m≡0)
... | no m≢0 = record
  { m≤n = pred-mono (≤-step m≤n)
  ; Γ = insert′ Γ m≤n m≢0 (reduce≥′ (pred-mono (≤-step m≤n)) j (pred-mono 1+j≥m)) (lookup Δ (fromℕ< i<m))
  ; Δ = remove′ Δ m≢0 (fromℕ< i<m)
  }
  where
  open Context Γ,Δ

cons : ∀ {n} → Context n → Type ℓ ℓ → Context (suc n)
cons {n} Γ,Δ τ = record
  { m≤n = s≤s m≤n
  ; Γ = Γ
  ; Δ = τ ∷ Δ
  }
  where
  open Context Γ,Δ

shift : ∀ {n} → Context n → Context n
shift {n} Γ,Δ = record
  { m≤n = z≤n
  ; Γ = cast (trans (sym (+-∸-assoc m m≤n)) (m+n∸m≡n m n)) (Δ ++ Γ)
  ; Δ = []
  }
  where
  open Context Γ,Δ

_≋_ : ∀ {n} → Rel (Context n) (c ⊔ lsuc ℓ)
Γ,Δ ≋ Γ,Δ′ = Σ (Context.m Γ,Δ ≡ Context.m Γ,Δ′) λ {refl → Context.Γ Γ,Δ ≡ Context.Γ Γ,Δ′ × Context.Δ Γ,Δ ≡ Context.Δ Γ,Δ′}
