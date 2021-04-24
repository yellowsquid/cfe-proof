{-# OPTIONS --without-K --safe #-}

module Cfe.Fin.Base where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; pred; z≤n)
open import Data.Nat.Properties using (pred-mono)
open import Data.Fin using (Fin; zero; suc; toℕ; inject₁; _≤_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

data Fin< : ∀ {n} → Fin n → Set where
  zero : ∀ {n i} → Fin< {suc n} (suc i)
  suc  : ∀ {n i} → Fin< {n} i → Fin< (suc i)

data Fin<< : ∀ {n i} → Fin< {n} i → Set where
  zero : ∀ {n i j} → Fin<< {suc n} {suc i} (suc j)
  suc  : ∀ {n i j} → Fin<< {n} {i} j → Fin<< (suc j)

data Fin> : ∀ {n} → Fin n → Set where
  zero : ∀ {n} → Fin> {suc (suc n)} zero
  suc  : ∀ {n} → Fin> {suc n} zero → Fin> {suc (suc n)} zero
  inj  : ∀ {n i} → Fin> {n} i → Fin> (suc i)

data Fin>< : ∀ {n i} → Fin> {n} i → Set where
  zero : ∀ {n j} → Fin>< {suc (suc n)} {zero} (suc j)
  suc  : ∀ {n j} → Fin>< {suc n} {zero} j → Fin>< (suc j)
  inj  : ∀ {n i j} → Fin>< {n} {i} j → Fin>< (inj j)

------------------------------------------------------------------------
-- Coversions to ℕ

toℕ< : ∀ {n i} → Fin< {n} i → ℕ
toℕ< zero    = 0
toℕ< (suc j) = suc (toℕ< j)

toℕ> : ∀ {n i} → Fin> {n} i → ℕ
toℕ> zero    = 0
toℕ> (suc j) = suc (toℕ> j)
toℕ> (inj j) = suc (toℕ> j)

------------------------------------------------------------------------
-- Upwards injections

inject!< : ∀ {n i} → Fin< {suc n} i → Fin n
inject!< {suc _} zero    = zero
inject!< {suc _} (suc j) = suc (inject!< j)

inject< : ∀ {n i} → Fin< {n} i → Fin n
inject< zero    = zero
inject< (suc j) = suc (inject< j)

inject₁< : ∀ {n i} → Fin< {n} i → Fin< (suc i)
inject₁< zero    = zero
inject₁< (suc j) = suc (inject₁< j)

inject!<< : ∀ {n i j} → Fin<< {suc n} {suc i} j → Fin< i
inject!<< {suc _} {suc _} zero    = zero
inject!<< {suc _} {suc _} (suc k) = suc (inject!<< k)

inject<< : ∀ {n i j} → Fin<< {n} {i} j → Fin< i
inject<< zero    = zero
inject<< (suc k) = suc (inject<< k)

inject!>< : ∀ {n i j} → Fin>< {suc n} {inject₁ i} j → Fin> i
inject!>< {suc (suc _)} {zero}  {suc j}  zero    = zero
inject!>< {suc (suc _)} {zero}  {suc j}  (suc k) = suc (inject!>< k)
inject!>< {suc (suc _)} {suc _} {inj j}  (inj k) = inj (inject!>< k)

inject>< : ∀ {n i j} → Fin>< {n} {i} j → Fin> {n} i
inject>< zero    = zero
inject>< (suc k) = suc (inject>< k)
inject>< (inj k) = inj (inject>< k)

------------------------------------------------------------------------
-- Downwards injections

strengthen< : ∀ {n} → (i : Fin n) → Fin< (suc i)
strengthen< zero    = zero
strengthen< (suc i) = suc (strengthen< i)

------------------------------------------------------------------------
-- Casts

cast< : ∀ {m n i j} → .(toℕ i ≡ toℕ j) → Fin< {m} i → Fin< {n} j
cast< {i = suc _} {suc _} _   zero    = zero
cast< {i = suc _} {suc _} i≡j (suc k) = suc (cast< (cong pred i≡j) k)

cast<< : ∀ {m n i j k l} → .(toℕ< k ≡ toℕ< l) → Fin<< {m} {i} k → Fin<< {n} {j} l
cast<< {k = suc _} {suc _} _   zero    = zero
cast<< {k = suc _} {suc _} k≡l (suc x) = suc (cast<< (cong pred k≡l) x)

cast> : ∀ {n i j} → .(j ≤ i) → Fin> {n} i → Fin> j
cast> {_}           {zero}  {zero}  j≤i zero    = zero
cast> {_}           {zero}  {zero}  j≤i (suc k) = suc (cast> j≤i k)
cast> {suc (suc _)} {suc i} {zero}  j≤i (inj k) = suc (cast> z≤n k)
cast> {suc (suc _)} {suc i} {suc j} j≤i (inj k) = inj (cast> (pred-mono j≤i) k)

------------------------------------------------------------------------
-- Additions

raise!> : ∀ {n i} → Fin> {suc n} i → Fin n
raise!> {suc _} zero    = zero
raise!> {suc _} (suc j) = suc (raise!> j)
raise!> {suc _} (inj j) = suc (raise!> j)

suc> : ∀ {n i} → Fin> {n} i → Fin> (inject₁ i)
suc> zero    = suc zero
suc> (suc j) = suc (suc> j)
suc> (inj j) = inj (suc> j)

------------------------------------------------------------------------
-- Operations on the index

-- predⁱ< {i = "i"} _ = "pred i"

predⁱ< : ∀ {n i} → Fin< {suc n} i → Fin n
predⁱ< {i = suc i} _ = i

-- inject₁ⁱ> {i = "i"} _ = "i"

inject₁ⁱ> : ∀ {n i} → Fin> {suc n} i → Fin n
inject₁ⁱ>         zero    = zero
inject₁ⁱ>         (suc _) = zero
inject₁ⁱ> {suc _} (inj j) = suc (inject₁ⁱ> j)

------------------------------------------------------------------------
-- Operations

punchIn> : ∀ {n i} → Fin> {suc n} (inject₁ i) → Fin> i → Fin> (inject₁ i)
punchIn> {i = zero}  zero    k       = suc k
punchIn> {i = zero}  (suc j) zero    = zero
punchIn> {i = zero}  (suc j) (suc k) = suc (punchIn> j k)
punchIn> {i = suc _} (inj j) (inj k) = inj (punchIn> j k)

punchOut> : ∀ {n i j k} → raise!> {n} {i} j ≢ raise!> {n} {i} k → Fin> (inject₁ⁱ> j)
punchOut>               {j = zero}        {zero}  j≢k = ⊥-elim (j≢k refl)
punchOut>               {j = zero}        {suc k} j≢k = k
punchOut> {suc (suc _)} {j = suc j}       {zero}  j≢k = zero
punchOut> {suc (suc _)} {j = suc zero}    {suc k} j≢k = suc (punchOut> (j≢k ∘ cong suc))
punchOut> {suc (suc _)} {j = suc (suc j)} {suc k} j≢k = suc (punchOut> {j = suc j} (j≢k ∘ cong suc))
punchOut> {suc _}       {j = inj j}       {inj k} j≢k = inj (punchOut> (j≢k ∘ cong suc))

-- reflect "j" _ ≡ "j"

reflect! :
  ∀ {n i} → (j : Fin< (suc {n} i)) → (k : Fin<< (suc j)) → Fin> (inject₁ (inject!< (inject!<< k)))
reflect! {suc _}               zero    zero    = zero
reflect! {suc (suc _)} {suc _} (suc j) zero    = suc (reflect! j zero)
reflect! {suc (suc _)} {suc _} (suc j) (suc k) = inj (reflect! j k)

reflect :
  ∀ {n i} → (j : Fin< {n} i) → (k : Fin<< (suc j)) → Fin> (inject< (inject!<< k))
reflect {suc (suc n)}               zero    zero    = zero
reflect {_}           {suc (suc _)} (suc j) zero    = suc (reflect j zero)
reflect {_}           {suc (suc _)} (suc j) (suc k) = inj (reflect j k)
