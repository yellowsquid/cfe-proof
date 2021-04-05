{-# OPTIONS --without-K --safe #-}

module Cfe.Function.Power where

open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; _×_)
open import Function using (id; _∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary.PropositionalEquality using (cong; _≡_)

private
  variable
    a : Level
    A : Set a

infix 10 _^_

------------------------------------------------------------------------
-- Definition

_^_ : (A → A) → ℕ → A → A
f ^ ℕ.zero = id
f ^ ℕ.suc n = f ∘ f ^ n

------------------------------------------------------------------------
-- Properties

f∼g⇒fⁿ∼gⁿ :
  ∀ {a b ℓ} {A : Set a} {B : Set b} (_∼_ : REL A B ℓ) {f g 0A 0B} →
  0A ∼ 0B → (∀ {x y} → x ∼ y → f x ∼ g y) → ∀ n → (f ^ n) 0A ∼ (g ^ n) 0B
f∼g⇒fⁿ∼gⁿ _ refl ext    ℕ.zero = refl
f∼g⇒fⁿ∼gⁿ ∼ refl ext (ℕ.suc n) = ext (f∼g⇒fⁿ∼gⁿ ∼ refl ext n)

fⁿf≡fⁿ⁺¹ : ∀ (f : A → A) n → (f ^ n) ∘ f ≡ f ^ (ℕ.suc n)
fⁿf≡fⁿ⁺¹ f    ℕ.zero = _≡_.refl
fⁿf≡fⁿ⁺¹ f (ℕ.suc n) = cong (f ∘_) (fⁿf≡fⁿ⁺¹ f n)
