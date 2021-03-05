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
  {a aℓ}
  where
  Iterate : (Language a aℓ → Language a aℓ) → IndexedLanguage 0ℓ 0ℓ a aℓ
  Iterate f = record
    { Carrierᵢ = ℕ
    ; _≈ᵢ_ = ≡._≡_
    ; isEquivalenceᵢ = ≡.isEquivalence
    ; F = λ n → iter f n (Lift a aℓ ∅)
    ; cong = λ {≡.refl → ≈-refl}
    }

  ≈ᵗ-refl : (g : Language a aℓ → Language a aℓ) →
            Reflexive (Tagged (Iterate g)) (_≈ᵗ_ (Iterate g))
  ≈ᵗ-refl g {_} {n , _} = refl , (≈ᴸ-refl (Iter.F n))
    where
    module Iter = IndexedLanguage (Iterate g)

  ≈ᵗ-sym : (g : Language a aℓ → Language a aℓ) →
           Symmetric (Tagged (Iterate g)) (_≈ᵗ_ (Iterate g))
  ≈ᵗ-sym g {_} {_} {n , _} (refl , x∈Fn≈y∈Fn) =
    refl , (≈ᴸ-sym (Iter.F n) x∈Fn≈y∈Fn)
    where
    module Iter = IndexedLanguage (Iterate g)

  ≈ᵗ-trans : (g : Language a aℓ → Language a aℓ) →
             Transitive (Tagged (Iterate g)) (_≈ᵗ_ (Iterate g))
  ≈ᵗ-trans g {_} {_} {_} {n , _} (refl , x∈Fn≈y∈Fn) (refl , y∈Fn≈z∈Fn) =
    refl , (≈ᴸ-trans (Iter.F n) x∈Fn≈y∈Fn y∈Fn≈z∈Fn)
    where
    module Iter = IndexedLanguage (Iterate g)

  ⋃ : (Language a aℓ → Language a aℓ) → Language a aℓ
  ⋃ f = record
    { Carrier = Iter.Tagged
    ; _≈_ = Iter._≈ᵗ_
    ; isEquivalence = record
      { refl = ≈ᵗ-refl f
      ; sym = ≈ᵗ-sym f
      ; trans = ≈ᵗ-trans f
      }
    }
    where
    module Iter = IndexedLanguage (Iterate f)

  ⋃-cong : ∀ {f g : Language a aℓ → Language a aℓ} → (∀ {x y} → x ≈ y → f x ≈ g y) → ⋃ f ≈ ⋃ g
  ⋃-cong f≈g = record
    { f = λ { (n , l∈fn) → n , _≈_.f (f≈g⇒fn≈gn (L.setoid a aℓ) f≈g n (Lift a aℓ ∅)) l∈fn}
    ; f⁻¹ = λ { (n , l∈gn) → n , _≈_.f⁻¹ (f≈g⇒fn≈gn (L.setoid a aℓ) f≈g n (Lift a aℓ ∅)) l∈gn}
    ; cong₁ = λ {_} {_} {(i , _)} → λ { (refl , l₁≈l₂) → refl , _≈_.cong₁ (f≈g⇒fn≈gn (L.setoid a aℓ) f≈g i (Lift a aℓ ∅)) l₁≈l₂}
    ; cong₂ = λ {_} {_} {(i , _)} → λ { (refl , l₁≈l₂) → refl , _≈_.cong₂ (f≈g⇒fn≈gn (L.setoid a aℓ) f≈g i (Lift a aℓ ∅)) l₁≈l₂}
    }

  ⋃-monotone : ∀ {f g : Language a aℓ → Language a aℓ} → (∀ {x y} → x ≤ y → f x ≤ g y) → ⋃ f ≤ ⋃ g
  ⋃-monotone f≤g = record
    { f = λ { (n , l∈fn) → n , _≤_.f (f≤g⇒fn≤gn (poset a aℓ) f≤g n (Lift a aℓ ∅)) l∈fn }
    ; cong = λ {_} {_} {(i , _)} → λ { (refl , l₁≈l₂) → refl , _≤_.cong (f≤g⇒fn≤gn (poset a aℓ) f≤g i (Lift a aℓ ∅)) l₁≈l₂ }
    }
