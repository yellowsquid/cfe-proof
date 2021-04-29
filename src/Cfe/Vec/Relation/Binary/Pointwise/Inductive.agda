{-# OPTIONS --without-K --safe #-}

module Cfe.Vec.Relation.Binary.Pointwise.Inductive where

open import Data.Fin using (toℕ; zero; suc)
open import Data.Nat using (ℕ; suc; _≟_; pred)
open import Data.Vec using (Vec; insert; remove)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
open import Function using (_|>_)
open import Level using (Level)
open import Relation.Binary using (REL; Antisym)
open import Relation.Binary.PropositionalEquality using (cong)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

private
  variable
    a b ℓ : Level
    A : Set a
    B : Set b
    _∼_ : REL A B ℓ
    m n : ℕ

antisym :
  ∀ {P : REL A B ℓ} {Q : REL B A ℓ} {R : REL A B ℓ} →
  Antisym P Q R → Antisym (Pointwise P {m} {n}) (Pointwise Q) (Pointwise R)
antisym anti []       []       = []
antisym anti (x ∷ xs) (y ∷ ys) = anti x y ∷ antisym anti xs ys

Pointwise-insert :
  ∀ {xs : Vec A m} {ys : Vec B n} → ∀ i j {i≡j : True (toℕ i ≟ toℕ j)} {x y} →
  x ∼ y → Pointwise _∼_ xs ys → Pointwise _∼_ (insert xs i x) (insert ys j y)
Pointwise-insert zero    zero          x xs       = x ∷ xs
Pointwise-insert (suc i) (suc j) {i≡j} x (y ∷ xs) =
  y ∷ Pointwise-insert i j {i≡j |> toWitness |> cong pred |> fromWitness} x xs

Pointwise-remove :
  ∀ {xs : Vec A (suc m)} {ys : Vec B (suc n)} → ∀ i j {i≡j : True (toℕ i ≟ toℕ j)} →
  Pointwise _∼_ xs ys → Pointwise _∼_ (remove xs i) (remove ys j)
Pointwise-remove zero zero (_ ∷ xs) = xs
Pointwise-remove (suc i) (suc j) {i≡j} (x ∷ y ∷ xs) =
  x ∷ Pointwise-remove i j {i≡j |> toWitness |> cong pred |> fromWitness} (y ∷ xs)
