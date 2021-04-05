{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.List.Compare
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over renaming (Carrier to C)

open import Data.Empty
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Product
open import Data.Unit using (⊤)
open import Function
open import Level

------------------------------------------------------------------------
-- Definition

data Compare : List C → List C → List C → List C → Set (c ⊔ ℓ) where
  back : ∀ {xs zs} → (xs≋zs : xs ≋ zs) → Compare [] xs [] zs
  left :
    ∀ {w ws xs z zs} →
    Compare ws xs [] zs → (w∼z : w ≈ z) →
    Compare (w ∷ ws) xs [] (z ∷ zs)
  right :
    ∀ {x xs y ys zs} →
    Compare [] xs ys zs → (x∼y : x ≈ y) →
    Compare [] (x ∷ xs) (y ∷ ys) zs
  front :
    ∀ {w ws xs y ys zs} →
    Compare ws xs ys zs →
    (w∼y : w ≈ y) →
    Compare (w ∷ ws) xs (y ∷ ys) zs

------------------------------------------------------------------------
-- Predicates

IsLeft : ∀ {ws xs ys zs} → Compare ws xs ys zs → Set
IsLeft (back xs≋zs)    = ⊥
IsLeft (left cmp w∼z)  = ⊤
IsLeft (right cmp x∼y) = ⊥
IsLeft (front cmp w∼y) = IsLeft cmp

IsRight : ∀ {ws xs ys zs} → Compare ws xs ys zs → Set
IsRight (back xs≋zs)    = ⊥
IsRight (left cmp w∼z)  = ⊥
IsRight (right cmp x∼y) = ⊤
IsRight (front cmp w∼y) = IsRight cmp

IsEqual : ∀ {ws xs ys zs} → Compare ws xs ys zs → Set
IsEqual (back xs≋zs)    = ⊤
IsEqual (left cmp w∼z)  = ⊥
IsEqual (right cmp x∼y) = ⊥
IsEqual (front cmp w∼y) = IsEqual cmp

-- Predicates are disjoint

<?> : ∀ {ws xs ys zs} → (cmp : Compare ws xs ys zs) → Tri (IsLeft cmp) (IsEqual cmp) (IsRight cmp)
<?> (back xs≋zs)    = tri≈ id  _ id
<?> (left cmp w∼z)  = tri<  _ id id
<?> (right cmp x∼y) = tri> id id  _
<?> (front cmp w∼y) = <?> cmp

------------------------------------------------------------------------
-- Introduction

-- Construct from the equality of two pairs of lists

compare : ∀ ws xs ys zs → ws ++ xs ≋ ys ++ zs → Compare ws xs ys zs
compare []       xs       []       zs       eq         = back eq
compare []       (x ∷ xs) (y ∷ ys) zs       (x∼y ∷ eq) = right (compare [] xs ys zs eq) x∼y
compare (w ∷ ws) xs       []       (z ∷ zs) (w∼z ∷ eq) = left (compare ws xs [] zs eq) w∼z
compare (w ∷ ws) xs       (y ∷ ys) zs       (w∼y ∷ eq) = front (compare ws xs ys zs eq) w∼y

------------------------------------------------------------------------
-- Elimination

-- Eliminate left splits

left-split :
  ∀ {ws xs ys zs} →
  (cmp : Compare ws xs ys zs) →
  IsLeft cmp →
  ∃₂ λ w ws′ → ws ≋ ys ++ w ∷ ws′ × w ∷ ws′ ++ xs ≋ zs
left-split (left (back xs≋zs) w∼z) _ = -, -, ≋-refl , w∼z ∷ xs≋zs
left-split (left (left cmp w′∼z′) w∼z) _ with left-split (left cmp w′∼z′) _
... | (_ , _ , eq₁ , eq₂) = -, -, refl ∷ eq₁ , w∼z ∷ eq₂
left-split (front cmp w∼y) l with left-split cmp l
... | (_ , _ , eq₁ , eq₂) = -, -, w∼y ∷ eq₁ , eq₂

-- Eliminate right splits

right-split :
  ∀ {ws xs ys zs} →
  (cmp : Compare ws xs ys zs) →
  IsRight cmp →
  ∃₂ λ y ys′ → ws ++ y ∷ ys′ ≋ ys × xs ≋ y ∷ ys′ ++ zs
right-split (right (back xs≋zs) x∼y) _ = -, -, ≋-refl , x∼y ∷ xs≋zs
right-split (right (right cmp x′∼y′) x∼y) _ with right-split (right cmp x′∼y′) _
... | (_ , _ , eq₁ , eq₂) = -, -, refl ∷ eq₁ , x∼y ∷ eq₂
right-split (front cmp w∼y) r with right-split cmp r
... | (_ , _ , eq₁ , eq₂) = -, -, w∼y ∷ eq₁ , eq₂

-- Eliminate equal splits

eq-split : ∀ {ws xs ys zs} → (cmp : Compare ws xs ys zs) → IsEqual cmp → ws ≋ ys × xs ≋ zs
eq-split (back xs≋zs)    e = [] , xs≋zs
eq-split (front cmp w∼y) e = map₁ (w∼y ∷_) (eq-split cmp e)
