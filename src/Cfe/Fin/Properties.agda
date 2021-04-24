{-# OPTIONS --without-K --safe #-}

module Cfe.Fin.Properties where

open import Cfe.Fin.Base
open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc; toℕ; punchIn; punchOut; inject₁)
open import Data.Nat using (suc; pred; _≤_; _<_; _≥_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective; pred-mono; module ≤-Reasoning)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Properties missing from Data.Fin.Properties
------------------------------------------------------------------------

inject₁-mono : ∀ {n i j} → toℕ {n} i ≤ toℕ {n} j → toℕ (inject₁ i) ≤ toℕ (inject₁ j)
inject₁-mono {i = zero}          i≤j       = z≤n
inject₁-mono {i = suc i} {suc j} (s≤s i≤j) = s≤s (inject₁-mono i≤j)

------------------------------------------------------------------------
-- Properties of toℕ<
------------------------------------------------------------------------

toℕ<<i : ∀ {n i} j → toℕ< {n} {i} j < toℕ i
toℕ<<i zero    = s≤s z≤n
toℕ<<i (suc j) = s≤s (toℕ<<i j)

------------------------------------------------------------------------
-- Properties of toℕ>

toℕ>≥i : ∀ {n i} j → toℕ> {n} {i} j ≥ toℕ i
toℕ>≥i zero    = z≤n
toℕ>≥i (suc j) = z≤n
toℕ>≥i (inj j) = s≤s (toℕ>≥i j)

------------------------------------------------------------------------
-- Properties of inject!<
------------------------------------------------------------------------

toℕ-inject!< : ∀ {n i} j → toℕ (inject!< {n} {i} j) ≡ toℕ< j
toℕ-inject!< {suc _} zero    = refl
toℕ-inject!< {suc _} (suc j) = cong suc (toℕ-inject!< j)

inject!<-mono :
  ∀ {m n i j k l} → toℕ< k ≤ toℕ< l → toℕ (inject!< {m} {i} k) ≤ toℕ (inject!< {n} {j} l)
inject!<-mono {k = k} {l} k≤l = begin
  toℕ (inject!< k) ≡⟨ toℕ-inject!< k ⟩
  toℕ< k           ≤⟨ k≤l ⟩
  toℕ< l           ≡˘⟨ toℕ-inject!< l ⟩
  toℕ (inject!< l) ∎
  where open ≤-Reasoning

inject!<-cong :
  ∀ {m n i j k l} → toℕ< k ≡ toℕ< l → toℕ (inject!< {m} {i} k) ≡ toℕ (inject!< {n} {j} l)
inject!<-cong {k = k} {l} k≡l = begin
  toℕ (inject!< k) ≡⟨ toℕ-inject!< k ⟩
  toℕ< k           ≡⟨ k≡l ⟩
  toℕ< l           ≡˘⟨ toℕ-inject!< l ⟩
  toℕ (inject!< l) ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of inject*<*
------------------------------------------------------------------------

inject-square : ∀ {n i j} k → inject< (inject!<< {n} {i} {j} k) ≡ inject!< (inject<< k)
inject-square {suc n} {suc i} zero    = refl
inject-square {suc n} {suc i} (suc k) = cong suc (inject-square k)

------------------------------------------------------------------------
-- Properties of strengthen<
------------------------------------------------------------------------

toℕ-strengthen< : ∀ {n} i → toℕ< (strengthen< {n} i) ≡ toℕ i
toℕ-strengthen< zero    = refl
toℕ-strengthen< (suc i) = cong suc (toℕ-strengthen< i)

strengthen<-inject!< : ∀ {n i} j → toℕ< (strengthen< (inject!< {n} {i} j)) ≡ toℕ< j
strengthen<-inject!< {suc _} zero    = refl
strengthen<-inject!< {suc _} (suc j) = cong suc (strengthen<-inject!< j)

------------------------------------------------------------------------
-- Properties of cast<
------------------------------------------------------------------------

toℕ-cast< : ∀ {m n i j} i≡j k → toℕ< (cast< {m} {n} {i} {j} i≡j k) ≡ toℕ< k
toℕ-cast< {i = suc _} {suc _} i≡j zero    = refl
toℕ-cast< {i = suc _} {suc _} i≡j (suc k) = cong suc (toℕ-cast< (cong pred i≡j) k)

------------------------------------------------------------------------
-- Properties of cast>
------------------------------------------------------------------------

toℕ-cast> : ∀ {n i j} j≤i k → toℕ> (cast> {n} {i} {j} j≤i k) ≡ toℕ> k
toℕ-cast> {_}           {zero}  {zero}  j≤i zero    = refl
toℕ-cast> {_}           {zero}  {zero}  j≤i (suc k) = cong suc (toℕ-cast> j≤i k)
toℕ-cast> {suc (suc n)} {suc i} {zero}  j≤i (inj k) = cong suc (toℕ-cast> z≤n k)
toℕ-cast> {suc (suc n)} {suc i} {suc j} j≤i (inj k) = cong suc (toℕ-cast> (pred-mono j≤i) k)

------------------------------------------------------------------------
-- Properties of raise!>
------------------------------------------------------------------------

toℕ-raise!> : ∀ {n i} j → toℕ (raise!> {n} {i} j) ≡ toℕ> j
toℕ-raise!>         zero    = refl
toℕ-raise!>         (suc j) = cong suc (toℕ-raise!> j)
toℕ-raise!> {suc n} (inj j) = cong suc (toℕ-raise!> j)

raise!>-cong : ∀ {m n i j k l} → toℕ> k ≡ toℕ> l → toℕ (raise!> {m} {i} k) ≡ toℕ (raise!> {n} {j} l)
raise!>-cong {k = k} {l} k≡l = begin
  toℕ (raise!> k) ≡⟨ toℕ-raise!> k ⟩
  toℕ> k         ≡⟨ k≡l ⟩
  toℕ> l         ≡˘⟨ toℕ-raise!> l ⟩
  toℕ (raise!> l) ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of suc>
------------------------------------------------------------------------

toℕ-suc> : ∀ {n i} j → toℕ> (suc> {n} {i} j) ≡ suc (toℕ> j)
toℕ-suc> zero    = refl
toℕ-suc> (suc j) = cong suc (toℕ-suc> j)
toℕ-suc> (inj j) = cong suc (toℕ-suc> j)

------------------------------------------------------------------------
-- Properties of predⁱ<
------------------------------------------------------------------------

toℕ-predⁱ< : ∀ {n i} j → suc (toℕ (predⁱ< {n} {i} j)) ≡ toℕ i
toℕ-predⁱ< {i = suc _} _ = refl

predⁱ<-mono :
  ∀ {n i j} k l → toℕ i ≤ toℕ j → toℕ (predⁱ< {n} {i} k) ≤ toℕ (predⁱ< {n} {j} l)
predⁱ<-mono {i = i} {j} k l i≤j = pred-mono (begin
  suc (toℕ (predⁱ< k)) ≡⟨ toℕ-predⁱ< k ⟩
  toℕ i                ≤⟨ i≤j ⟩
  toℕ j                ≡˘⟨ toℕ-predⁱ< l ⟩
  suc (toℕ (predⁱ< l)) ∎)
  where open ≤-Reasoning

predⁱ<-cong :
  ∀ {n i j} k l → toℕ i ≡ toℕ j → toℕ (predⁱ< {n} {i} k) ≡ toℕ (predⁱ< {n} {j} l)
predⁱ<-cong {i = i} {j} k l i≡j = suc-injective (begin
  suc (toℕ (predⁱ< k)) ≡⟨ toℕ-predⁱ< k ⟩
  toℕ i                ≡⟨ i≡j ⟩
  toℕ j                ≡˘⟨ toℕ-predⁱ< l ⟩
  suc (toℕ (predⁱ< l)) ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of inject₁ⁱ>
------------------------------------------------------------------------

toℕ-inject₁ⁱ> : ∀ {n i} j → toℕ (inject₁ⁱ> {n} {i} j) ≡ toℕ i
toℕ-inject₁ⁱ> {suc _} zero    = refl
toℕ-inject₁ⁱ> {suc _} (suc k) = refl
toℕ-inject₁ⁱ> {suc _} (inj k) = cong suc (toℕ-inject₁ⁱ> k)

inject₁ⁱ>-mono :
  ∀ {n i j} k l → toℕ i ≤ toℕ j → toℕ (inject₁ⁱ> {n} {i} k) ≤ toℕ (inject₁ⁱ> {n} {j} l)
inject₁ⁱ>-mono {i = i} {j} k l i≤j = begin
  toℕ (inject₁ⁱ> k) ≡⟨ toℕ-inject₁ⁱ> k ⟩
  toℕ i             ≤⟨ i≤j ⟩
  toℕ j             ≡˘⟨ toℕ-inject₁ⁱ> l ⟩
  toℕ (inject₁ⁱ> l) ∎
  where open ≤-Reasoning

inject₁ⁱ>-cong :
  ∀ {n i j} k l → toℕ i ≡ toℕ j → toℕ (inject₁ⁱ> {n} {i} k) ≡ toℕ (inject₁ⁱ> {n} {j} l)
inject₁ⁱ>-cong {i = i} {j} k l i≡j = begin
  toℕ (inject₁ⁱ> k) ≡⟨ toℕ-inject₁ⁱ> k ⟩
  toℕ i             ≡⟨ i≡j ⟩
  toℕ j             ≡˘⟨ toℕ-inject₁ⁱ> l ⟩
  toℕ (inject₁ⁱ> l) ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of punchIn>
------------------------------------------------------------------------

toℕ-punchIn> : ∀ {n i} j k → toℕ> (punchIn> {suc n} {i} j k) ≡ toℕ (punchIn (raise!> j) (raise!> k))
toℕ-punchIn> {_}     {zero}  zero    k       = sym (cong suc (toℕ-raise!> k))
toℕ-punchIn> {_}     {zero}  (suc j) zero    = refl
toℕ-punchIn> {_}     {zero}  (suc j) (suc k) = cong suc (toℕ-punchIn> j k)
toℕ-punchIn> {suc _} {suc i} (inj j) (inj k) = cong suc (toℕ-punchIn> j k)

------------------------------------------------------------------------
-- Properties of punchOut>
------------------------------------------------------------------------

toℕ-punchOut> : ∀ {n i j k} j≢k → toℕ> (punchOut> {suc n} {i} {j} {k} j≢k) ≡ toℕ (punchOut j≢k)
toℕ-punchOut> {_}     {_}           {zero}        {zero}  j≢k = ⊥-elim (j≢k refl)
toℕ-punchOut> {_}     {_}           {zero}        {suc k} j≢k = sym (toℕ-raise!> k)
toℕ-punchOut> {suc _} {_}           {suc j}       {zero}  j≢k = refl
toℕ-punchOut> {suc _} {_}           {suc zero}    {suc k} j≢k =
  cong suc (toℕ-punchOut> (j≢k ∘ cong suc))
toℕ-punchOut> {suc _} {_}           {suc (suc j)} {suc k} j≢k =
  cong suc (toℕ-punchOut> {j = suc j} (j≢k ∘ cong suc))
toℕ-punchOut> {suc _} {suc zero}    {inj j}       {inj k} j≢k =
  cong suc (toℕ-punchOut> (j≢k ∘ cong suc))
toℕ-punchOut> {suc _} {suc (suc _)} {inj j}       {inj k} j≢k =
  cong suc (toℕ-punchOut> (j≢k ∘ cong suc))

------------------------------------------------------------------------
-- Properties of reflect!
------------------------------------------------------------------------

toℕ-reflect! : ∀ {n i} j k → toℕ> (reflect! {n} {i} j k) ≡ toℕ< j
toℕ-reflect! {suc _}               zero    zero    = refl
toℕ-reflect! {suc (suc _)} {suc _} (suc j) zero    = cong suc (toℕ-reflect! j zero)
toℕ-reflect! {suc (suc _)} {suc _} (suc j) (suc k) = cong suc (toℕ-reflect! j k)

------------------------------------------------------------------------
-- Properties of reflect
------------------------------------------------------------------------

toℕ-reflect : ∀ {n i} j k → toℕ> (reflect {n} {i} j k) ≡ toℕ< j
toℕ-reflect {suc (suc _)}               zero    zero    = refl
toℕ-reflect {_}           {suc (suc _)} (suc j) zero    = cong suc (toℕ-reflect j zero)
toℕ-reflect {_}           {suc (suc _)} (suc j) (suc k) = cong suc (toℕ-reflect j k)

------------------------------------------------------------------------
-- Other properties
------------------------------------------------------------------------

inj-punchOut :
  ∀ {n i j k} → (j≢k : inject!< {suc n} {suc i} j ≢ raise!> (inj {suc n} {i} k)) →
  toℕ (punchOut j≢k) ≡ toℕ> k
inj-punchOut         {j = zero}  {k}     j≢k = toℕ-raise!> k
inj-punchOut {suc n} {j = suc j} {inj k} j≢k = cong suc (inj-punchOut (j≢k ∘ cong suc))

