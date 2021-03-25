{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Language.Construct.Concatenate
  {c ℓ} (over : Setoid c ℓ)
  where

open import Algebra
open import Cfe.Language over as 𝕃
open import Data.Empty
open import Data.List hiding (null)
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.List.Properties
open import Data.Product as Product
open import Data.Unit using (⊤)
open import Function
open import Level
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Nullary
open import Relation.Unary hiding (_∈_)
import Relation.Binary.Indexed.Heterogeneous as I

open Setoid over using () renaming (Carrier to C; _≈_ to _∼_; refl to ∼-refl; sym to ∼-sym; trans to ∼-trans)

module _
  {a b}
  (A : Language a)
  (B : Language b)
  where

  private
    module A = Language A
    module B = Language B

  infix 7 _∙_

  Concat : List C → Set (c ⊔ ℓ ⊔ a ⊔ b)
  Concat l = ∃[ l₁ ] l₁ ∈ A × ∃[ l₂ ] l₂ ∈ B × l₁ ++ l₂ ≋ l

  _∙_ : Language (c ⊔ ℓ ⊔ a ⊔ b)
  _∙_ = record
    { 𝕃 = Concat
    ; ∈-resp-≋ = λ { l≋l′ (_ , l₁∈A , _ , l₂∈B , eq) → -, l₁∈A , -, l₂∈B , ≋-trans eq l≋l′
      }
    }

isMonoid : ∀ {a} → IsMonoid 𝕃._≈_ _∙_ (𝕃.Lift (ℓ ⊔ a) ｛ε｝)
isMonoid {a} = record
  { isSemigroup = record
    { isMagma = record
      { isEquivalence = ≈-isEquivalence
      ; ∙-cong = λ X≈Y U≈V → record
        { f = λ { (_ , l₁∈X , _ , l₂∈U , eq) → -, _≈_.f X≈Y l₁∈X , -, _≈_.f U≈V l₂∈U , eq }
        ; f⁻¹ = λ { (_ , l₁∈Y , _ , l₂∈V , eq) → -, _≈_.f⁻¹ X≈Y l₁∈Y , -, _≈_.f⁻¹ U≈V l₂∈V , eq }
        }
      }
    ; assoc = λ X Y Z → record
      { f = λ {l} → λ { (l₁₂ , (l₁ , l₁∈X , l₂ , l₂∈Y , eq₁) , l₃ , l₃∈Z , eq₂) →
        -, l₁∈X , -, (-, l₂∈Y , -, l₃∈Z , ≋-refl) , (begin
          l₁ ++ l₂ ++ l₃ ≡˘⟨ ++-assoc l₁ l₂ l₃ ⟩
          (l₁ ++ l₂) ++ l₃ ≈⟨ ++⁺ eq₁ ≋-refl ⟩
          l₁₂ ++ l₃ ≈⟨ eq₂ ⟩
          l ∎) }
      ; f⁻¹ = λ {l} → λ { (l₁ , l₁∈X , l₂₃ , (l₂ , l₂∈Y , l₃ , l₃∈Z , eq₁) , eq₂) →
        -, (-, l₁∈X , -, l₂∈Y , ≋-refl) , -, l₃∈Z , (begin
          (l₁ ++ l₂) ++ l₃ ≡⟨ ++-assoc l₁ l₂ l₃ ⟩
          l₁ ++ l₂ ++ l₃ ≈⟨ ++⁺ ≋-refl eq₁ ⟩
          l₁ ++ l₂₃ ≈⟨ eq₂ ⟩
          l ∎) }
      }
    }
  ; identity = (λ X → record
    { f = λ { ([] , _ , _ , l₂∈X , eq) → Language.∈-resp-≋ X eq l₂∈X }
    ; f⁻¹ = λ l∈X → -, lift refl , -, l∈X , ≋-refl
    }) , (λ X → record
    { f = λ { (l₁ , l₁∈X , [] , _ , eq) → Language.∈-resp-≋ X (≋-trans (≋-reflexive (sym (++-identityʳ l₁))) eq) l₁∈X }
    ; f⁻¹ = λ {l} l∈X → -, l∈X , -, lift refl , ≋-reflexive (++-identityʳ l)
    })
  }
  where
  open import Relation.Binary.Reasoning.Setoid ≋-setoid

∙-mono : ∀ {a b} → _∙_ Preserves₂ _≤_ {a} ⟶ _≤_ {b} ⟶ _≤_
∙-mono X≤Y U≤V = record
  { f = λ {(_ , l₁∈X , _ , l₂∈U , eq) → -, X≤Y.f l₁∈X , -, U≤V.f l₂∈U , eq}
  }
  where
  module X≤Y = _≤_ X≤Y
  module U≤V = _≤_ U≤V

private
  data Compare : List C → List C → List C → List C → Set (c ⊔ ℓ) where
    -- left : ∀ {ws₁ w ws₂ xs ys z zs₁ zs₂} → (ws₁≋ys : ws₁ ≋ ys) → (w∼z : w ∼ z) → (ws₂≋zs₁ : ws₂ ≋ zs₁) → (xs≋zs₂ : xs ≋ zs₂) → Compare (ws₁ ++ w ∷ ws₂) xs ys (z ∷ zs₁ ++ zs₂)
    -- right : ∀ {ws x xs₁ xs₂ ys₁ y ys₂ zs} → (ws≋ys₁ : ws ≋ ys₁) → (x∼y : x ∼ y) → (xs₁≋ys₂ : xs₁ ≋ ys₂) → (xs₂≋zs : xs₂ ≋ zs) → Compare ws (x ∷ xs₁ ++ xs₂) (ys₁ ++ y ∷ ys₂) zs
    back : ∀ {xs zs} → (xs≋zs : xs ≋ zs) → Compare [] xs [] zs
    left : ∀ {w ws xs z zs} → Compare ws xs [] zs → (w∼z : w ∼ z) → Compare (w ∷ ws) xs [] (z ∷ zs)
    right : ∀ {x xs y ys zs} → Compare [] xs ys zs → (x∼y : x ∼ y) → Compare [] (x ∷ xs) (y ∷ ys) zs
    front : ∀ {w ws xs y ys zs} → Compare ws xs ys zs → (w∼y : w ∼ y) → Compare (w ∷ ws) xs (y ∷ ys) zs

  isLeft : ∀ {ws xs ys zs} → Compare ws xs ys zs → Set
  isLeft (back xs≋zs) = ⊥
  isLeft (left cmp w∼z) = ⊤
  isLeft (right cmp x∼y) = ⊥
  isLeft (front cmp w∼y) = isLeft cmp

  isRight : ∀ {ws xs ys zs} → Compare ws xs ys zs → Set
  isRight (back xs≋zs) = ⊥
  isRight (left cmp w∼z) = ⊥
  isRight (right cmp x∼y) = ⊤
  isRight (front cmp w∼y) = isRight cmp

  isEqual : ∀ {ws xs ys zs} → Compare ws xs ys zs → Set
  isEqual (back xs≋zs) = ⊤
  isEqual (left cmp w∼z) = ⊥
  isEqual (right cmp x∼y) = ⊥
  isEqual (front cmp w∼y) = isEqual cmp

  <?> : ∀ {ws xs ys zs} → (cmp : Compare ws xs ys zs) → Tri (isLeft cmp) (isEqual cmp) (isRight cmp)
  <?> (back xs≋zs) = tri≈ id _ id
  <?> (left cmp w∼z) = tri< _ id id
  <?> (right cmp x∼y) = tri> id id _
  <?> (front cmp w∼y) = <?> cmp

  compare : ∀ ws xs ys zs → ws ++ xs ≋ ys ++ zs → Compare ws xs ys zs
  compare [] xs [] zs eq = back eq
  compare [] (x ∷ xs) (y ∷ ys) zs (x∼y ∷ eq) = right (compare [] xs ys zs eq) x∼y
  compare (w ∷ ws) xs [] (z ∷ zs) (w∼z ∷ eq) = left (compare ws xs [] zs eq) w∼z
  compare (w ∷ ws) xs (y ∷ ys) zs (w∼y ∷ eq) = front (compare ws xs ys zs eq) w∼y

  left-split : ∀ {ws xs ys zs} → (cmp : Compare ws xs ys zs) → isLeft cmp → ∃[ w ] ∃[ ws′ ] ws ≋ ys ++ w ∷ ws′ × w ∷ ws′ ++ xs ≋ zs
  left-split (left (back xs≋zs) w∼z) _ = -, -, ≋-refl , w∼z ∷ xs≋zs
  left-split (left (left cmp w′∼z′) w∼z) _ with left-split (left cmp w′∼z′) _
  ... | (_ , _ , eq₁ , eq₂) = -, -, ∼-refl ∷ eq₁ , w∼z ∷ eq₂
  left-split (front cmp w∼y) l with left-split cmp l
  ... | (_ , _ , eq₁ , eq₂) = -, -, w∼y ∷ eq₁ , eq₂

  right-split : ∀ {ws xs ys zs} → (cmp : Compare ws xs ys zs) → isRight cmp → ∃[ y ] ∃[ ys′ ] ws ++ y ∷ ys′ ≋ ys × xs ≋ y ∷ ys′ ++ zs
  right-split (right (back xs≋zs) x∼y) _ = -, -, ≋-refl , x∼y ∷ xs≋zs
  right-split (right (right cmp x′∼y′) x∼y) _ with right-split (right cmp x′∼y′) _
  ... | (_ , _ , eq₁ , eq₂) = -, -, ∼-refl ∷ eq₁ , x∼y ∷ eq₂
  right-split (front cmp w∼y) r with right-split cmp r
  ... | (_ , _ , eq₁ , eq₂) = -, -, w∼y ∷ eq₁ , eq₂

  eq-split : ∀ {ws xs ys zs} → (cmp : Compare ws xs ys zs) → isEqual cmp → ws ≋ ys
  eq-split (back xs≋zs) e = []
  eq-split (front cmp w∼y) e = w∼y ∷ eq-split cmp e

∙-unique-prefix : ∀ {a b} (A : Language a) (B : Language b) → Empty (flast A ∩ first B) → ¬ (null A) → ∀ {l} → (l∈A∙B l∈A∙B′ : l ∈ A ∙ B) → proj₁ l∈A∙B ≋ proj₁ l∈A∙B′
∙-unique-prefix _ _ _ ¬n₁ ([] , l₁∈A , _) _ = ⊥-elim (¬n₁ l₁∈A)
∙-unique-prefix _ _ _ ¬n₁ (_ ∷ _ , _) ([] , l₁′∈A , _) = ⊥-elim (¬n₁ l₁′∈A)
∙-unique-prefix A B ∄[l₁∩f₂] _ (c ∷ l₁ , l₁∈A , l₂ , l₂∈B , eq₁) (c′ ∷ l₁′ , l₁′∈A , l₂′ , l₂′∈B , eq₂) with compare (c ∷ l₁) l₂ (c′ ∷ l₁′) l₂′ (≋-trans eq₁ (≋-sym eq₂))
... | cmp with <?> cmp
... | tri< l _ _ = ⊥-elim (∄[l₁∩f₂] w ((-, (λ ()) , l₁′∈A , -, A.∈-resp-≋ eq₃ l₁∈A) , (-, B.∈-resp-≋ (≋-sym eq₄) l₂′∈B)))
  where
  module A = Language A
  module B = Language B
  lsplit = left-split cmp l
  w = proj₁ lsplit
  eq₃ = (proj₁ ∘ proj₂ ∘ proj₂) lsplit
  eq₄ = (proj₂ ∘ proj₂ ∘ proj₂) lsplit
... | tri≈ _ e _ = eq-split cmp e
... | tri> _ _ r = ⊥-elim (∄[l₁∩f₂] w ((-, (λ ()) , l₁∈A , -, A.∈-resp-≋ (≋-sym eq₃) l₁′∈A) , (-, (B.∈-resp-≋ eq₄ l₂∈B))))
  where
  module A = Language A
  module B = Language B
  rsplit = right-split cmp r
  w = proj₁ rsplit
  eq₃ = (proj₁ ∘ proj₂ ∘ proj₂) rsplit
  eq₄ = (proj₂ ∘ proj₂ ∘ proj₂) rsplit
