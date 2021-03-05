{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Type.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C; _≈_ to _∼_)

open import Cfe.Language over
open import Cfe.Type.Base over
open import Data.Empty
open import Data.List
open import Data.Product
open import Function

⊨-anticongˡ : ∀ {a aℓ b bℓ fℓ lℓ} {A : Language a aℓ} {B : Language b bℓ} {τ : Type fℓ lℓ} → B ≤ A → A ⊨ τ → B ⊨ τ
⊨-anticongˡ B≤A A⊨τ = record
  { n⇒n = A⊨τ.n⇒n ∘ B≤A.f
  ; f⇒f = A⊨τ.f⇒f ∘ map₂ B≤A.f
  ; l⇒l = A⊨τ.l⇒l ∘ map₂ (map₂ (map₂ B≤A.f))
  }
  where
  module B≤A = _≤_ B≤A
  module A⊨τ = _⊨_ A⊨τ

L⊨τ⊥⇒L≈∅ : ∀ {a aℓ} {L : Language a aℓ} → L ⊨ τ⊥ → L ≈ ∅
L⊨τ⊥⇒L≈∅ {L = L} L⊨τ⊥ = record
  { f = λ {l} l∈L → elim l l∈L
  ; f⁻¹ = λ ()
  ; cong₁ = λ {l} {_} {l∈L} → ⊥-elim (elim l l∈L)
  ; cong₂ = λ {_} {_} {}
  }
  where
  module L⊨τ⊥ = _⊨_ L⊨τ⊥

  elim : ∀ l (l∈L : l ∈ L) → l ∈ ∅
  elim [] []∈L = L⊨τ⊥.n⇒n []∈L
  elim (x ∷ l) xl∈L = L⊨τ⊥.f⇒f (-, xl∈L)

∅⊨τ⊥ : ∅ ⊨ τ⊥
∅⊨τ⊥ = record
  { n⇒n = λ ()
  ; f⇒f = λ ()
  ; l⇒l = λ ()
  }
