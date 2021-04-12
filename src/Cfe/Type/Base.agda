{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (REL; _Respects_; Setoid)

module Cfe.Type.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using (trans) renaming (Carrier to C; _≈_ to _∼_)

open import Cfe.Language over hiding (_∙_; _≈_)
open import Data.Bool renaming (_∨_ to _∨ᵇ_; _≤_ to _≤ᵇ_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; map)
open import Function
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

private
  variable
    a b fℓ lℓ fℓ₁ lℓ₁ fℓ₂ lℓ₂ : Level

------------------------------------------------------------------------
-- Definitions

infix 2 _⇒_

_⇒_ : Bool → (C → Set a) → C → Set a
false ⇒ A = const ⊥
true  ⇒ A = A

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
  ; first      = λ c → τ₁.first c ⊎ (τ₁.null ⇒ τ₂.first) c
  ; flast      = λ c → τ₂.flast c ⊎ (τ₂.null ⇒ λ c → τ₂.first c ⊎ τ₁.flast c) c
  ; first-cong = λ {c} {c′} c∼c′ →
      map
        (τ₁.first-cong c∼c′)
        (case τ₁.null
         return (λ b → (b ⇒ τ₂.first) c → (b ⇒ τ₂.first) c′)
         of λ
           { true  → τ₂.first-cong c∼c′
           ; false → id
           })
  ; flast-cong = λ {c} {c′} c∼c′ →
      map
        (τ₂.flast-cong c∼c′)
        (case τ₂.null
         return (λ b →
           (b ⇒ λ c → τ₂.first c ⊎ τ₁.flast c) c →
           (b ⇒ λ c → τ₂.first c ⊎ τ₁.flast c) c′)
         of λ
           { true  → map (τ₂.first-cong c∼c′) (τ₁.flast-cong c∼c′)
           ; false → id
           })
  }
  where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂

_∨_ : Type fℓ₁ lℓ₁ → Type fℓ₂ lℓ₂ → Type (fℓ₁ ⊔ fℓ₂) (lℓ₁ ⊔ lℓ₂)
τ₁ ∨ τ₂ = record
  { null       = τ₁.null ∨ᵇ τ₂.null
  ; first      = λ c → τ₁.first c ⊎ τ₂.first c
  ; flast      = λ c → τ₁.flast c ⊎ τ₂.flast c
  ; first-cong = λ c∼c′ → map (τ₁.first-cong c∼c′) (τ₂.first-cong c∼c′)
  ; flast-cong = λ c∼c′ → map (τ₁.flast-cong c∼c′) (τ₂.flast-cong c∼c′)
  }
  where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂

------------------------------------------------------------------------
-- Relations

infix 4 _≈_ _≤_ _≥_ _⊨_ _⊛_ _#_

record _≈_ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) : Set (c ⊔ fℓ₁ ⊔ lℓ₁ ⊔ fℓ₂ ⊔ lℓ₂) where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂
  field
    n≡n   : τ₁.null ≡ τ₂.null
    f₁⊆f₂ : ∀ {c} → τ₁.first c → τ₂.first c
    f₁⊇f₂ : ∀ {c} → τ₂.first c → τ₁.first c
    l₁⊆l₂ : ∀ {c} → τ₁.flast c → τ₂.flast c
    l₁⊇l₂ : ∀ {c} → τ₂.flast c → τ₁.flast c

record _≤_ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) : Set (c ⊔ fℓ₁ ⊔ lℓ₁ ⊔ fℓ₂ ⊔ lℓ₂) where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂
  field
    n≤n : τ₁.null ≤ᵇ τ₂.null
    f⊆f : ∀ {c} → τ₁.first c → τ₂.first c
    l⊆l : ∀ {c} → τ₁.flast c → τ₂.flast c

_≥_ : REL (Type fℓ₁ lℓ₁) (Type fℓ₂ lℓ₂) _
_≥_ = flip _≤_

record _⊨_ (A : Language a) (τ : Type fℓ lℓ) : Set (c ⊔ a ⊔ fℓ ⊔ lℓ) where
  module τ = Type τ
  field
    n⇒n : Null A → T (τ.null)
    f⇒f : ∀ {c} → First A c → τ.first c
    l⇒l : ∀ {c} → Flast A c → τ.flast c

record _⊛_ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) : Set (c ⊔ lℓ₁ ⊔ fℓ₂) where
  private
    module τ₁ = Type τ₁
    module τ₂ = Type τ₂
  field
    ∄[l₁∩f₂] : ∀ {c} → ¬ (τ₁.flast c × τ₂.first c)
    ¬n₁      : ¬ T (τ₁.null)

record _#_ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) : Set (c ⊔ fℓ₁ ⊔ fℓ₂) where
  private
    module τ₁ = Type τ₁
    module τ₂ = Type τ₂
  field
    ∄[f₁∩f₂] : ∀ {c} → ¬ (τ₁.first c × τ₂.first c)
    ¬n₁∨¬n₂  : ¬ (T τ₁.null × T τ₂.null)
