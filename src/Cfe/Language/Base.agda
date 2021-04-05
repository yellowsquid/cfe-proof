{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (REL; Setoid; _⟶_Respects_)

module Cfe.Language.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C)

open import Cfe.Function.Power
open import Data.Empty.Polymorphic using (⊥)
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Product
open import Data.Sum
open import Function
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec; ¬_)

private
  variable
    a b : Level

------------------------------------------------------------------------
-- Definition

record Language a : Set (c ⊔ ℓ ⊔ suc a) where
  field
    𝕃        : List C → Set a
    ∈-resp-≋ : 𝕃 ⟶ 𝕃 Respects _≋_

------------------------------------------------------------------------
-- Special Languages

∅ : Language a
∅ = record
  { 𝕃        = const ⊥
  ; ∈-resp-≋ = λ _ ()
  }

｛ε｝ : Language (c ⊔ a)
｛ε｝ {a} = record
  { 𝕃        = Lift a ∘ ([] ≡_)
  ; ∈-resp-≋ = λ { [] → id }
  }

｛_｝ : C → Language _
｛ c ｝ = record
  { 𝕃        = [ c ] ≋_
  ; ∈-resp-≋ = λ l₁≋l₂ l₁∈｛c｝ → ≋-trans l₁∈｛c｝ l₁≋l₂
  }

------------------------------------------------------------------------
-- Membership

infix 4 _∈_ _∉_

_∈_ : List C → Language a → Set _
_∈_ = flip Language.𝕃

_∉_ : List C → Language a → Set _
w ∉ A = ¬ w ∈ A

------------------------------------------------------------------------
-- Language Combinators

infix 8 ⋃_
infix 7 _∙_
infix 6 _∪_

_∙_ : Language a → Language b → Language _
A ∙ B = record
  { 𝕃        = λ w → ∃₂ λ w₁ w₂ → w₁ ∈ A × w₂ ∈ B × w₁ ++ w₂ ≋ w
  ; ∈-resp-≋ = λ w≋w′ (_ , _ , w₁∈A , w₂∈B , eq) → -, -, w₁∈A , w₂∈B , ≋-trans eq w≋w′
  }

_∪_ : Language a → Language b → Language _
A ∪ B = record
  { 𝕃        = λ w → w ∈ A ⊎ w ∈ B
  ; ∈-resp-≋ = uncurry Data.Sum.map ∘ < Language.∈-resp-≋ A , Language.∈-resp-≋ B >
  }

Sup : (Language a → Language a) → Language a → Language _
Sup F A = record
  { 𝕃        = λ w → ∃[ n ] w ∈ (F ^ n) A
  ; ∈-resp-≋ = λ w≋w′ (n , w∈FⁿA) → n , Language.∈-resp-≋ ((F ^ n) A) w≋w′ w∈FⁿA
  }

⋃_ : (Language a → Language a) → Language _
⋃ F = Sup F ∅

------------------------------------------------------------------------
-- Relations

infix 4 _⊆_ _≈_

data _⊆_ {a b} : REL (Language a) (Language b) (c ⊔ ℓ ⊔ suc (a ⊔ b)) where
  sub : ∀ {A : Language a} {B : Language b} → (∀ {w} → w ∈ A → w ∈ B) → A ⊆ B

_⊇_ : REL (Language a) (Language b) _
_⊇_ = flip _⊆_

_≈_ : REL (Language a) (Language b) _
A ≈ B = A ⊆ B × B ⊆ A

_≉_ : REL (Language a) (Language b) _
A ≉ B = ¬ A ≈ B

------------------------------------------------------------------------
-- Membership Properties

-- Contains empty string

Null : ∀ {a} → Language a → Set a
Null A = [] ∈ A

-- Characters that start strings

First : ∀ {a} → Language a → C → Set (c ⊔ a)
First A c = ∃[ w ] c ∷ w ∈ A

-- Characters that can follow a string to make another string in the language

Flast : ∀ {a} → Language a → C → Set (c ⊔ a)
Flast A c = ∃₂ λ c′ w → (c′ ∷ w ∈ A × ∃[ w′ ] c′ ∷ w ++ c ∷ w′ ∈ A)

------------------------------------------------------------------------
-- Proof Properties

-- Membership is decidable

Decidable : Language a → Set _
Decidable A = ∀ w → Dec (w ∈ A)

-- Membership proofs are irrelevant

Irrelevant : Language a → Set _
Irrelevant A = ∀ {w} → (p q : w ∈ A) → p ≡ q

-- Membership proofs are recomputable

Recomputable : Language a → Set _
Recomputable A = ∀ {w} → .(w ∈ A) → w ∈ A
