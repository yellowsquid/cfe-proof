{-# OPTIONS --without-K --safe #-}

module Cfe.Fin.Base where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; Fin′; zero; suc; inject₁)

data Fin< : ∀ {n} → Fin n → Set where
  zero : ∀ {n i} → Fin< {suc n} (suc i)
  suc  : ∀ {n i} → Fin< {n} i → Fin< (suc i)

data Fin<′ : ∀ {n i} → Fin< {n} i → Set where
  zero : ∀ {n i j} → Fin<′ {suc n} {suc i} (suc j)
  suc  : ∀ {n i j} → Fin<′ {n} {i} j → Fin<′ (suc j)

-- Fin> {n} zero    ≡ Fin n
-- Fin>     (suc i) ≡ Fin> i

data Fin> : ∀ {n} → Fin n → Set where
  zero : ∀ {n} → Fin> {suc n} zero
  suc  : ∀ {n} → Fin> {suc n} zero → Fin> {suc (suc n)} zero
  inj  : ∀ {n i} → Fin> {n} i → Fin> (suc i)

data Fin>′ : ∀ {n i} → Fin> {n} i → Set where
  zero : ∀ {n j} → Fin>′ {suc (suc n)} {zero} (suc j)
  suc  : ∀ {n j} → Fin>′ {suc n} {zero} j → Fin>′ (suc j)
  inj  : ∀ {n i j} → Fin>′ {n} {i} j → Fin>′ (inj j)

toℕ< : ∀ {n i} → Fin< {n} i → ℕ
toℕ< zero    = 0
toℕ< (suc j) = suc (toℕ< j)

toℕ> : ∀ {n i} → Fin> {n} i → ℕ
toℕ> zero    = 0
toℕ> (suc j) = suc (toℕ> j)
toℕ> (inj j) = suc (toℕ> j)

strengthen< : ∀ {n} → (i : Fin n) → Fin< (suc i)
strengthen< zero    = zero
strengthen< (suc i) = suc (strengthen< i)

inject<! : ∀ {n i} → Fin< {suc n} i → Fin n
inject<! {suc _} zero    = zero
inject<! {suc _} (suc j) = suc (inject<! j)

cast<-inject₁ : ∀ {n i} → Fin< {n} i → Fin< (inject₁ i)
cast<-inject₁ zero    = zero
cast<-inject₁ (suc j) = suc (cast<-inject₁ j)

inject<!′ : ∀ {n i j} → Fin<′ {suc n} {suc i} j → Fin< i
inject<!′ {suc _} {suc _} zero    = zero
inject<!′ {suc _} {suc _} (suc k) = suc (inject<!′ k)

inject<′ : ∀ {n i j} → Fin<′ {n} {i} j → Fin< i
inject<′ zero    = zero
inject<′ (suc k) = suc (inject<′ k)

inject<!′-inject! : ∀ {n i j} → Fin<′ {suc n} {i} j → Fin< (inject<! j)
inject<!′-inject! {suc n} {_} {suc j} zero    = zero
inject<!′-inject! {suc n} {_} {suc j} (suc k) = suc (inject<!′-inject! k)

raise> : ∀ {n i} → Fin> {n} i → Fin n
raise> {suc _} zero    = zero
raise> {suc _} (suc j) = suc (raise> j)
raise> {suc _} (inj j) = suc (raise> j)

suc> : ∀ {n i} → Fin> {n} i → Fin> (inject₁ i)
suc> zero    = suc zero
suc> (suc j) = suc (suc> j)
suc> (inj j) = inj (suc> j)

inject>!′ : ∀ {n i j} → Fin>′ {suc n} {inject₁ i} j → Fin> {n} i
inject>!′ {suc _}       {zero}          zero    = zero
inject>!′ {suc (suc _)} {zero}  {suc _} (suc k) = suc (inject>!′ k)
inject>!′ {suc _}       {suc i}         (inj k) = inj (inject>!′ k)

inject>′ : ∀ {n i j} → Fin>′ {n} {i} j → Fin> {n} i
inject>′ zero    = zero
inject>′ (suc k) = suc (inject>′ k)
inject>′ (inj k) = inj (inject>′ k)

cast>-inject<! : ∀ {n i} (j : Fin< (suc i)) → Fin> {suc n} i → Fin> (inject<! j)
cast>-inject<!         zero    zero    = zero
cast>-inject<!         zero    (suc k) = suc (cast>-inject<! zero k)
cast>-inject<! {suc n} zero    (inj k) = suc (cast>-inject<! zero k)
cast>-inject<! {suc n} (suc j) (inj k) = inj (cast>-inject<! j k)

reflect :
  ∀ {n i} → (j : Fin< {suc (suc n)} (suc i)) → (k : Fin<′ (suc j)) → Fin> (inject<! (inject<!′ k))
reflect                 zero    zero    = zero
reflect {suc n} {suc i} (suc j) zero    = suc (reflect j zero)
reflect {suc n} {suc i} (suc j) (suc k) = inj (reflect j k)
