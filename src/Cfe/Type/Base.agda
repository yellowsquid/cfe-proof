{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (_Respects_; Setoid)

module Cfe.Type.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using (trans) renaming (Carrier to C; _≈_ to _∼_)

open import Cfe.Language over hiding (_∙_; _≈_)
open import Data.Bool renaming (_∨_ to _∨ᵇ_; _≤_ to _≤ᵇ_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; map)
open import Function using (const; flip)
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

private
  variable
    a b fℓ lℓ fℓ₁ lℓ₁ fℓ₂ lℓ₂ : Level

  union : (C → Set a) → (C → Set b) → C → Set _
  union A B c = A c ⊎ B c

  union-cong :
    ∀ {A : C → Set a} {B : C → Set b} →
    A Respects _∼_ → B Respects _∼_ → union A B Respects _∼_
  union-cong A-cong B-cong x∼y = map (A-cong x∼y) (B-cong x∼y)

  if-cong :
    ∀ {A B : C → Set a} cond →
    A Respects _∼_ → B Respects _∼_ → (if cond then A else B) Respects _∼_
  if-cong false A-cong B-cong = B-cong
  if-cong true  A-cong B-cong = A-cong

------------------------------------------------------------------------
-- Definitions

record Type fℓ lℓ : Set (c ⊔ ℓ ⊔ suc (fℓ ⊔ lℓ)) where
  field
    null       : Bool
    first      : C → Set fℓ
    flast      : C → Set lℓ
    first-cong : first Respects _∼_
    flast-cong : flast Respects _∼_

------------------------------------------------------------------------
-- Special Types

τ⊥ : Type fℓ lℓ
τ⊥ = record
  { null       = false
  ; first      = const ⊥
  ; flast      = const ⊥
  ; first-cong = λ _ ()
  ; flast-cong = λ _ ()
  }

τε : Type fℓ lℓ
τε = record
  { null       = true
  ; first      = const ⊥
  ; flast      = const ⊥
  ; first-cong = λ _ ()
  ; flast-cong = λ _ ()
  }

τ[_] : C → Type ℓ ℓ
τ[ c ] = record
  { null       = false
  ; first      = c ∼_
  ; flast      = const ⊥
  ; first-cong = flip trans
  ; flast-cong = λ _ ()
  }

------------------------------------------------------------------------
-- Type Operations

infix 7 _∙_
infix 6 _∨_

_∙_ : Type fℓ₁ lℓ₁ → Type fℓ₂ lℓ₂ → Type (fℓ₁ ⊔ fℓ₂) (lℓ₁ ⊔ fℓ₂ ⊔ lℓ₂)
τ₁ ∙ τ₂ = record
  { null       = τ₁.null ∧ τ₂.null
  ; first      = union τ₁.first (if τ₁.null then τ₂.first else const ⊥)
  ; flast      = union τ₂.flast (if τ₂.null then union τ₂.first τ₁.flast else const ⊥)
  ; first-cong = union-cong τ₁.first-cong (if-cong τ₁.null τ₂.first-cong (λ _ ()))
  ; flast-cong =
      union-cong τ₂.flast-cong (if-cong τ₂.null (union-cong τ₂.first-cong τ₁.flast-cong) (λ _ ()))
  }
  where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂

_∨_ : Type fℓ₁ lℓ₁ → Type fℓ₂ lℓ₂ → Type (fℓ₁ ⊔ fℓ₂) (lℓ₁ ⊔ lℓ₂)
τ₁ ∨ τ₂ = record
  { null       = τ₁.null ∨ᵇ τ₂.null
  ; first      = union τ₁.first τ₂.first
  ; flast      = union τ₁.flast τ₂.flast
  ; first-cong = union-cong τ₁.first-cong τ₂.first-cong
  ; flast-cong = union-cong τ₁.flast-cong τ₂.flast-cong
  }
  where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂

------------------------------------------------------------------------
-- Relations

infix 4 _≈_
infix 4 _≤_
infix 4 _⊨_
infix 4 _⊛_
infix 4 _#_

record _≈_ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) : Set (c ⊔ fℓ₁ ⊔ lℓ₁ ⊔ fℓ₂ ⊔ lℓ₂) where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂
  field
    n≡n   : τ₁.null ≡ τ₂.null
    f₁⊆f₂ : ∀ {c} → τ₁.first c → τ₂.first c
    f₁⊇f₂ : ∀ {c} → τ₁.first c → τ₂.first c
    l₁⊆l₂ : ∀ {c} → τ₁.flast c → τ₂.flast c
    l₁⊇l₂ : ∀ {c} → τ₁.flast c → τ₂.flast c

record _≤_ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) : Set (c ⊔ fℓ₁ ⊔ lℓ₁ ⊔ fℓ₂ ⊔ lℓ₂) where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂
  field
    n≤n : τ₁.null ≤ᵇ τ₂.null
    f⊆f : ∀ {c} → τ₁.first c → τ₂.first c
    l⊆l : ∀ {c} → τ₁.flast c → τ₂.flast c

record _⊨_ (A : Language a) (τ : Type fℓ lℓ) : Set (c ⊔ a ⊔ fℓ ⊔ lℓ) where
  module τ = Type τ
  field
    n⇒n : Null A → T (τ.null)
    f⇒f : ∀ {c} → First A c → τ.first c
    l⇒l : ∀ {c} → Flast A c → τ.flast c

record _⊛_ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) : Set (c ⊔ lℓ₁ ⊔ fℓ₂) where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂
  field
    ∄[l₁∩f₂] : ∀ c → ¬ (τ₁.flast c × τ₂.first c)
    ¬n₁      : ¬ T (τ₁.null)

record _#_ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) : Set (c ⊔ fℓ₁ ⊔ fℓ₂) where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂
  field
    ∄[f₁∩f₂] : ∀ c → ¬ (τ₁.first c × τ₂.first c)
    ¬n₁∨¬n₂  : ¬ (T τ₁.null × T τ₂.null)
