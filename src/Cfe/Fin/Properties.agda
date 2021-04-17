{-# OPTIONS --without-K --safe #-}

module Cfe.Fin.Properties where

open import Cfe.Fin.Base
open import Data.Fin using (zero; suc; toℕ)
open import Data.Nat using (suc; pred)
open import Relation.Binary.PropositionalEquality

inject<!-cong : ∀ {n i j k l} → toℕ< {i = i} k ≡ toℕ< {i = j} l → inject<! {n} k ≡ inject<! l
inject<!-cong {suc _} {k = zero}  {zero}  _   = refl
inject<!-cong {suc _} {k = suc k} {suc l} k≡l = cong suc (inject<!-cong (cong pred k≡l))

raise>-cong : ∀ {n i j k l} → toℕ> {i = i} k ≡ toℕ> {i = j} l → raise> {n} k ≡ raise> l
raise>-cong {suc _} {k = zero}  {zero}  _   = refl
raise>-cong {suc _} {k = suc k} {suc l} k≡l = cong suc (raise>-cong (cong pred k≡l))
raise>-cong {suc _} {k = suc k} {inj l} k≡l = cong suc (raise>-cong (cong pred k≡l))
raise>-cong {suc _} {k = inj k} {suc l} k≡l = cong suc (raise>-cong (cong pred k≡l))
raise>-cong {suc _} {k = inj k} {inj l} k≡l = cong suc (raise>-cong (cong pred k≡l))

toℕ>-suc> : ∀ {n} j → toℕ> (suc> {suc n} j) ≡ toℕ> (suc j)
toℕ>-suc> zero    = refl
toℕ>-suc> (suc j) = cong suc (toℕ>-suc> j)

toℕ<-inject<! : ∀ {n i} j → toℕ (inject<! {n} {i} j) ≡ toℕ< j
toℕ<-inject<! {suc n} zero    = refl
toℕ<-inject<! {suc n} (suc j) = cong suc (toℕ<-inject<! j)

toℕ>-cast>-inject<! : ∀ {n i} j k → toℕ> k ≡ toℕ> (cast>-inject<! {n} {i} j k)
toℕ>-cast>-inject<!         zero    zero    = refl
toℕ>-cast>-inject<!         zero    (suc k) = cong suc (toℕ>-cast>-inject<! zero k)
toℕ>-cast>-inject<! {suc n} zero    (inj k) = cong suc (toℕ>-cast>-inject<! zero k)
toℕ>-cast>-inject<! {suc n} (suc j) (inj k) = cong suc (toℕ>-cast>-inject<! j k)
