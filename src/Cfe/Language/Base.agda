{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Language.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C)

open import Algebra
open import Data.Empty
open import Data.List hiding (null)
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Product
open import Data.Unit using (⊤; tt)
open import Function hiding (_⟶_)
open import Level as L hiding (Lift)
open import Relation.Binary.PropositionalEquality

infix 4 _∈_
infix 4 _∉_

record Language a : Set (c ⊔ ℓ ⊔ suc a) where
  field
    𝕃 : List C → Set a
    ∈-resp-≋ : 𝕃 ⟶ 𝕃 Respects _≋_

∅ : Language 0ℓ
∅ = record
  { 𝕃 = const ⊥
  ; ∈-resp-≋ = λ _ ()
  }

｛ε｝ : Language c
｛ε｝ = record
  { 𝕃 = [] ≡_
  ; ∈-resp-≋ = λ { [] refl → refl}
  }

Lift : ∀ {a} → (b : Level) → Language a → Language (a ⊔ b)
Lift b A = record
  { 𝕃 = L.Lift b ∘ A.𝕃
  ; ∈-resp-≋ = λ { eq (lift l∈A) → lift (A.∈-resp-≋ eq l∈A)}
  }
  where
  module A = Language A

_∈_ : ∀ {a} → List C → Language a → Set a
_∈_ = flip Language.𝕃

_∉_ : ∀ {a} → List C → Language a → Set a
l ∉ A = l ∈ A → ⊥

record _≤_ {a b} (A : Language a) (B : Language b) : Set (c ⊔ a ⊔ b) where
  field
    f : ∀ {l} → l ∈ A → l ∈ B

record _≈_ {a b} (A : Language a) (B : Language b) : Set (c ⊔ ℓ ⊔ a ⊔ b) where
  field
    f : ∀ {l} → l ∈ A → l ∈ B
    f⁻¹ : ∀ {l} → l ∈ B → l ∈ A

null : ∀ {a} → Language a → Set a
null A = [] ∈ A

first : ∀ {a} → Language a → C → Set (c ⊔ a)
first A x = ∃[ l ] x ∷ l ∈ A

flast : ∀ {a} → Language a → C → Set (c ⊔ a)
flast A x = ∃[ l ] (l ≢ [] × l ∈ A × ∃[ l′ ] l ++ x ∷ l′ ∈ A)
