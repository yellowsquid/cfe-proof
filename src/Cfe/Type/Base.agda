{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Type.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C; _≈_ to _∼_)

open import Cfe.Language over hiding (_≤_; _≈_)
open import Data.Bool as 𝔹 hiding (_∨_) renaming (_≤_ to _≤ᵇ_)
open import Level as L renaming (suc to lsuc)
open import Relation.Unary as U
open import Relation.Binary.PropositionalEquality using (_≡_)

infix 7 _∙_
infix 6 _∨_
infix 4 _⊨_

record Type fℓ lℓ : Set (c ⊔ lsuc (fℓ ⊔ lℓ)) where
  field
    Null : Bool
    First : Pred C fℓ
    Flast : Pred C lℓ

open Type public

τ⊥ : Type 0ℓ 0ℓ
τ⊥ = record { Null = false ; First = U.∅ ; Flast = U.∅ }

τε : Type 0ℓ 0ℓ
τε = record { Null = true ; First = U.∅ ; Flast = U.∅ }

τ[_] : C → Type ℓ 0ℓ
τ[ c ] = record { Null = false ; First = c ∼_ ; Flast = U.∅ }

_∨_ : ∀ {fℓ₁ lℓ₁ fℓ₂ lℓ₂} → Type fℓ₁ lℓ₁ → Type fℓ₂ lℓ₂ → Type (fℓ₁ ⊔ fℓ₂) (lℓ₁ ⊔ lℓ₂)
τ₁ ∨ τ₂ = record
  { Null = Null τ₁ 𝔹.∨ Null τ₂
  ; First = First τ₁ ∪ First τ₂
  ; Flast = Flast τ₁ ∪ Flast τ₂
  }

_∙_ : ∀ {fℓ₁ lℓ₁ fℓ₂ lℓ₂} → Type fℓ₁ lℓ₁ → Type fℓ₂ lℓ₂ → Type (fℓ₁ ⊔ fℓ₂) (lℓ₁ ⊔ fℓ₂ ⊔ lℓ₂)
_∙_ {lℓ₁ = lℓ₁} {fℓ₂} {lℓ₂} τ₁ τ₂ = record
  { Null = Null τ₁ ∧ Null τ₂
  ; First = First τ₁ ∪ (if Null τ₁ then First τ₂ else λ x → L.Lift fℓ₂ (x U.∈ U.∅))
  ; Flast = Flast τ₂ ∪ (if Null τ₂ then First τ₂ ∪ Flast τ₁ else λ x → L.Lift (lℓ₁ ⊔ fℓ₂) (x U.∈ U.∅))
  }

record _⊨_ {a} {fℓ} {lℓ} (A : Language a) (τ : Type fℓ lℓ) : Set (c ⊔ a ⊔ fℓ ⊔ lℓ) where
  field
    n⇒n : null A → T (Null τ)
    f⇒f : first A ⊆ First τ
    l⇒l : flast A ⊆ Flast τ

record _⊛_ {fℓ₁} {lℓ₁} {fℓ₂} {lℓ₂} (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) : Set (c ⊔ lℓ₁ ⊔ fℓ₂) where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂

  field
    ∄[l₁∩f₂] : Empty (τ₁.Flast ∩ τ₂.First)
    ¬n₁ : T (not τ₁.Null)

record _#_ {fℓ₁} {lℓ₁} {fℓ₂} {lℓ₂} (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) : Set (c ⊔ fℓ₁ ⊔ fℓ₂) where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂

  field
    ∄[f₁∩f₂] : Empty (τ₁.First ∩ τ₂.First)
    ¬n₁∨¬n₂ : T (not (τ₁.Null 𝔹.∨ τ₂.Null))

record _≤_ {fℓ₁} {lℓ₁} {fℓ₂} {lℓ₂} (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) : Set (c ⊔ fℓ₁ ⊔ lℓ₁ ⊔ fℓ₂ ⊔ lℓ₂) where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂

  field
    n≤n : τ₁.Null ≤ᵇ τ₂.Null
    f⊆f : τ₁.First ⊆ τ₂.First
    l⊆l : τ₁.Flast ⊆ τ₂.Flast

record _≈_ {fℓ₁} {lℓ₁} {fℓ₂} {lℓ₂} (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) : Set (c ⊔ fℓ₁ ⊔ lℓ₁ ⊔ fℓ₂ ⊔ lℓ₂) where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂

  field
    n≡n : τ₁.Null ≡ τ₂.Null
    f₁⊆f₂ : τ₁.First ⊆ τ₂.First
    f₁⊇f₂ : τ₁.First ⊇ τ₂.First
    l₁⊆l₂ : τ₁.Flast ⊆ τ₂.Flast
    l₁⊇l₂ : τ₁.Flast ⊇ τ₂.Flast
