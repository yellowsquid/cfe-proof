{-# OPTIONS --without-K --safe #-}

open import Relation.Binary as B using (Setoid)

module Cfe.Language.Indexed.Construct.Iterate
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C)

open import Cfe.Language over as L
open import Cfe.Language.Indexed.Homogeneous over
open import Data.List
open import Data.Nat as ℕ hiding (_⊔_; _≤_)
open import Data.Product as Product
open import Function
open import Level hiding (Lift) renaming (suc to lsuc)
open import Relation.Binary.Indexed.Heterogeneous
open import Relation.Binary.PropositionalEquality as ≡

open IndexedLanguage

iter : ∀ {a} {A : Set a} → (A → A) → ℕ → A → A
iter f ℕ.zero = id
iter f (ℕ.suc n) = f ∘ iter f n

f-fn-x≡fn-f-x : ∀ {a} {A : Set a} (f : A → A) n x → f (iter f n x) ≡ iter f n (f x)
f-fn-x≡fn-f-x f ℕ.zero x = refl
f-fn-x≡fn-f-x f (suc n) x = ≡.cong f (f-fn-x≡fn-f-x f n x)

module _
  {a aℓ} (A : B.Setoid a aℓ)
  where

  module A = B.Setoid A

  f≈g⇒fn≈gn : {f g : A.Carrier → A.Carrier} → (∀ {x y} → x A.≈ y → f x A.≈ g y) → ∀ n x → iter f n x A.≈ iter g n x
  f≈g⇒fn≈gn f≈g ℕ.zero x = A.refl
  f≈g⇒fn≈gn f≈g (suc n) x = f≈g (f≈g⇒fn≈gn f≈g n x)

module _
  {a aℓ₁ aℓ₂} (A : B.Poset a aℓ₁ aℓ₂)
  where

  module A′ = B.Poset A

  f≤g⇒fn≤gn : {f g : A′.Carrier → A′.Carrier} → (∀ {x y} → x A′.≤ y → f x A′.≤ g y) → ∀ n x → iter f n x A′.≤ iter g n x
  f≤g⇒fn≤gn f≤g ℕ.zero x = A′.refl
  f≤g⇒fn≤gn f≤g (suc n) x = f≤g (f≤g⇒fn≤gn f≤g n x)

module _
  {a}
  where
  Iterate : (Language a → Language a) → IndexedLanguage 0ℓ 0ℓ a
  Iterate f = record
    { Carrierᵢ = ℕ
    ; _≈ᵢ_ = ≡._≡_
    ; isEquivalenceᵢ = ≡.isEquivalence
    ; F = λ n → iter f n (Lift a ∅)
    ; cong = λ {≡.refl → ≈-refl}
    }

  ⋃ : (Language a → Language a) → Language a
  ⋃ f = record
    { 𝕃 = Iter.Tagged
    ; ∈-resp-≋ = λ { l₁≋l₂ (i , l₁∈fi) → i , Language.∈-resp-≋ (Iter.F i) l₁≋l₂ l₁∈fi }
    }
    where
    module Iter = IndexedLanguage (Iterate f)

  ⋃-cong : ∀ {f g} → (∀ {x y} → x ≈ y → f x ≈ g y) → ⋃ f ≈ ⋃ g
  ⋃-cong f≈g = record
    { f = λ { (n , l∈fn) → n , _≈_.f (f≈g⇒fn≈gn (L.setoid a) f≈g n (Lift a ∅)) l∈fn}
    ; f⁻¹ = λ { (n , l∈gn) → n , _≈_.f⁻¹ (f≈g⇒fn≈gn (L.setoid a) f≈g n (Lift a ∅)) l∈gn}
    }

  ⋃-mono : ∀ {f g} → (∀ {x y} → x ≤ y → f x ≤ g y) → ⋃ f ≤ ⋃ g
  ⋃-mono f≤g = record
    { f = λ { (n , l∈fn) → n , _≤_.f (f≤g⇒fn≤gn (poset a) f≤g n (Lift a ∅)) l∈fn }
    }
