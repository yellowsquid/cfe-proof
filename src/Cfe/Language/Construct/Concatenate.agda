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
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Nullary
open import Relation.Unary hiding (_∈_)
import Relation.Binary.Indexed.Heterogeneous as I

open Setoid over using () renaming (Carrier to C; _≈_ to _∼_; refl to ∼-refl; sym to ∼-sym; trans to ∼-trans)

module Compare where
  data Compare : List C → List C → List C → List C → Set (c ⊔ ℓ) where
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

  eq-split : ∀ {ws xs ys zs} → (cmp : Compare ws xs ys zs) → isEqual cmp → ws ≋ ys × xs ≋ zs
  eq-split (back xs≋zs) e = [] , xs≋zs
  eq-split (front cmp w∼y) e = map₁ (w∼y ∷_) (eq-split cmp e)

module _
  {a b}
  (A : Language a)
  (B : Language b)
  where

  private
    module A = Language A
    module B = Language B

  infix 7 _∙_

  record Concat (l : List C) : Set (c ⊔ ℓ ⊔ a ⊔ b) where
    field
      l₁ : List C
      l₂ : List C
      l₁∈A : l₁ ∈ A
      l₂∈B : l₂ ∈ B
      eq : l₁ ++ l₂ ≋ l

  _∙_ : Language (c ⊔ ℓ ⊔ a ⊔ b)
  _∙_ = record
    { 𝕃 = Concat
    ; ∈-resp-≋ = λ
      { l≋l′ record { l₁ = _ ; l₂ = _ ; l₁∈A = l₁∈A ; l₂∈B = l₂∈B ; eq = eq } → record
        { l₁∈A = l₁∈A ; l₂∈B = l₂∈B ; eq = ≋-trans eq l≋l′ }
      }
    }

∙-cong : ∀ {a} → Congruent₂ _≈_ (_∙_ {c ⊔ ℓ ⊔ a})
∙-cong X≈Y U≈V = record
  { f = λ
    { record { l₁∈A = l₁∈X ; l₂∈B = l₂∈Y ; eq = eq } → record
      { l₁∈A = X≈Y.f l₁∈X
      ; l₂∈B = U≈V.f l₂∈Y
      ; eq = eq
      }
    }
  ; f⁻¹ = λ
    { record { l₁∈A = l₁∈Y ; l₂∈B = l₂∈V ; eq = eq } → record
      { l₁∈A = X≈Y.f⁻¹ l₁∈Y
      ; l₂∈B = U≈V.f⁻¹ l₂∈V
      ; eq = eq
      }
    }
  }
  where
  module X≈Y = _≈_ X≈Y
  module U≈V = _≈_ U≈V

∙-assoc : ∀ {a b c} (A : Language a) (B : Language b) (C : Language c) →
          (A ∙ B) ∙ C ≈ A ∙ (B ∙ C)
∙-assoc A B C = record
  { f = λ
    { record
      { l₂ = l₃
      ; l₁∈A = record { l₁ = l₁ ; l₂ = l₂ ; l₁∈A = l₁∈A ; l₂∈B = l₂∈B ; eq = eq₁ }
      ; l₂∈B = l₃∈C
      ; eq = eq₂
      } → record
      { l₁∈A = l₁∈A
      ; l₂∈B = record
        { l₁∈A = l₂∈B
        ; l₂∈B = l₃∈C
        ; eq = ≋-refl
        }
      ; eq = ≋-trans (≋-sym (≋-reflexive (++-assoc l₁ l₂ l₃))) (≋-trans (++⁺ eq₁ ≋-refl) eq₂)
      }
    }
  ; f⁻¹ = λ
    { record
      { l₁ = l₁
      ; l₁∈A = l₁∈A
      ; l₂∈B = record { l₁ = l₂ ; l₂ = l₃ ; l₁∈A = l₂∈B ; l₂∈B = l₃∈C ; eq = eq₁ }
      ; eq = eq₂
      } → record
      { l₁∈A = record
        { l₁∈A = l₁∈A
        ; l₂∈B = l₂∈B
        ; eq = ≋-refl
        }
      ; l₂∈B = l₃∈C
      ; eq = ≋-trans (≋-reflexive (++-assoc l₁ l₂ l₃)) (≋-trans (++⁺ ≋-refl eq₁) eq₂)
      }
    }
  }

∙-identityˡ : ∀ {a} → LeftIdentity _≈_ (𝕃.Lift (ℓ ⊔ a) ｛ε｝) _∙_
∙-identityˡ X = record
  { f = λ
    { record { l₁ = [] ; l₂∈B = l∈X ; eq = eq } → X.∈-resp-≋ eq l∈X
    }
  ; f⁻¹ = λ l∈X → record
    { l₁∈A = lift ≡.refl
    ; l₂∈B = l∈X
    ; eq = ≋-refl
    }
  }
  where
  module X = Language X

∙-unique-prefix : ∀ {a b} (A : Language a) (B : Language b) → Empty (flast A ∩ first B) → ¬ (null A) → ∀ {l} → (l∈A∙B l∈A∙B′ : l ∈ A ∙ B) → Concat.l₁ l∈A∙B ≋ Concat.l₁ l∈A∙B′ × Concat.l₂ l∈A∙B ≋ Concat.l₂ l∈A∙B′
∙-unique-prefix A B ∄[l₁∩f₂] ¬n₁ l∈A∙B l∈A∙B′ with Compare.compare (Concat.l₁ l∈A∙B) (Concat.l₂ l∈A∙B) (Concat.l₁ l∈A∙B′) (Concat.l₂ l∈A∙B′) (≋-trans (Concat.eq l∈A∙B) (≋-sym (Concat.eq l∈A∙B′)))
... | cmp with Compare.<?> cmp
... | tri< l _ _ = ⊥-elim (∄[l₁∩f₂] w ((-, (λ { ≡.refl → ¬n₁ (Concat.l₁∈A l∈A∙B′)}) , (Concat.l₁∈A l∈A∙B′) , -, A.∈-resp-≋ eq₃ (Concat.l₁∈A l∈A∙B)) , (-, B.∈-resp-≋ (≋-sym eq₄) (Concat.l₂∈B l∈A∙B′))))
  where
  module A = Language A
  module B = Language B
  lsplit = Compare.left-split cmp l
  w = proj₁ lsplit
  eq₃ = (proj₁ ∘ proj₂ ∘ proj₂) lsplit
  eq₄ = (proj₂ ∘ proj₂ ∘ proj₂) lsplit
... | tri≈ _ e _ = Compare.eq-split cmp e
... | tri> _ _ r = ⊥-elim (∄[l₁∩f₂] w ((-, (λ { ≡.refl → ¬n₁ (Concat.l₁∈A l∈A∙B)}) , (Concat.l₁∈A l∈A∙B) , -, A.∈-resp-≋ (≋-sym eq₃) (Concat.l₁∈A l∈A∙B′)) , (-, (B.∈-resp-≋ eq₄ (Concat.l₂∈B l∈A∙B)))))
  where
  module A = Language A
  module B = Language B
  rsplit = Compare.right-split cmp r
  w = proj₁ rsplit
  eq₃ = (proj₁ ∘ proj₂ ∘ proj₂) rsplit
  eq₄ = (proj₂ ∘ proj₂ ∘ proj₂) rsplit

∙-identityʳ : ∀ {a} → RightIdentity _≈_ (𝕃.Lift (ℓ ⊔ a) ｛ε｝) _∙_
∙-identityʳ X = record
  { f = λ
    { record { l₁ = l₁ ; l₂ = [] ; l₁∈A = l∈X ; eq = eq } → X.∈-resp-≋ (≋-trans (≋-sym (≋-reflexive (++-identityʳ l₁))) eq) l∈X
    }
  ; f⁻¹ = λ {l} l∈X → record
    { l₁∈A = l∈X
    ; l₂∈B = lift ≡.refl
    ; eq = ≋-reflexive (++-identityʳ l)
    }
  }
  where
  module X = Language X

isMagma : ∀ {a} → IsMagma _≈_ (_∙_ {c ⊔ ℓ ⊔ a})
isMagma {a} = record
  { isEquivalence = ≈-isEquivalence
  ; ∙-cong = ∙-cong {a}
  }

isSemigroup : ∀ {a} → IsSemigroup _≈_ (_∙_ {c ⊔ ℓ ⊔ a})
isSemigroup {a} = record
  { isMagma = isMagma {a}
  ; assoc = ∙-assoc
  }

isMonoid : ∀ {a} → IsMonoid _≈_ _∙_ (𝕃.Lift (ℓ ⊔ a) ｛ε｝)
isMonoid {a} = record
  { isSemigroup = isSemigroup {a}
  ; identity = ∙-identityˡ {a} , ∙-identityʳ {a}
  }
