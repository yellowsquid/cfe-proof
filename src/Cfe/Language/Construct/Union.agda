{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Language.Construct.Union
  {c ℓ} (over : Setoid c ℓ)
  where

open import Algebra
open import Data.Empty
open import Data.List
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Product as Product
open import Data.Sum as Sum
open import Function
open import Level
open import Cfe.Language over as 𝕃 hiding (Lift)

open Setoid over renaming (Carrier to C)

module _
  {a b}
  (A : Language a)
  (B : Language b)
  where

  private
    module A = Language A
    module B = Language B

  infix 6 _∪_

  Union : List C → Set (a ⊔ b)
  Union l = l ∈ A ⊎ l ∈ B

  _∪_ : Language (a ⊔ b)
  _∪_ = record
    { 𝕃 = Union
    ; ∈-resp-≋ = λ l₁≋l₂ → Sum.map (A.∈-resp-≋ l₁≋l₂) (B.∈-resp-≋ l₁≋l₂)
    }

isCommutativeMonoid : ∀ {a} → IsCommutativeMonoid 𝕃._≈_ _∪_ (𝕃.Lift a ∅)
isCommutativeMonoid = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = ≈-isEquivalence
        ; ∙-cong = λ X≈Y U≈V → record
          { f = Sum.map (_≈_.f X≈Y) (_≈_.f U≈V)
          ; f⁻¹ = Sum.map (_≈_.f⁻¹ X≈Y) (_≈_.f⁻¹ U≈V)
          }
        }
      ; assoc = λ A B C → record
        { f = Sum.assocʳ
        ; f⁻¹ = Sum.assocˡ
        }
      }
    ; identity = (λ A → record
      { f = λ { (inj₂ x) → x }
      ; f⁻¹ = inj₂
      }) , (λ A → record
      { f = λ { (inj₁ x) → x }
      ; f⁻¹ = inj₁
      })
    }
  ; comm = λ A B → record
    { f = Sum.swap
    ; f⁻¹ = Sum.swap
    }
  }

∪-idem : ∀ {a} → Idempotent 𝕃._≈_ (_∪_ {a})
∪-idem A = record
  { f = [ id , id ]′
  ; f⁻¹ = inj₁
  }

∪-mono : ∀ {a b} → _∪_ Preserves₂ _≤_ {a} ⟶ _≤_ {b} ⟶ _≤_
∪-mono X≤Y U≤V = record
  { f = Sum.map X≤Y.f U≤V.f
  }
  where
  module X≤Y = _≤_ X≤Y
  module U≤V = _≤_ U≤V

∪-unique : ∀ {a b} {A : Language a} {B : Language b} → (∀ x → first A x → first B x → ⊥) → (𝕃.null A → 𝕃.null B → ⊥) → ∀ {l} → l ∈ A ∪ B → (l ∈ A × l ∉ B) ⊎ (l ∉ A × l ∈ B)
∪-unique fA∩fB≡∅ ¬nA∨¬nB {[]}    (inj₁ []∈A) = inj₁ ([]∈A , ¬nA∨¬nB []∈A)
∪-unique fA∩fB≡∅ ¬nA∨¬nB {x ∷ l} (inj₁ xl∈A) = inj₁ (xl∈A , (λ xl∈B → fA∩fB≡∅ x (-, xl∈A) (-, xl∈B)))
∪-unique fA∩fB≡∅ ¬nA∨¬nB {[]}    (inj₂ []∈B) = inj₂ (flip ¬nA∨¬nB []∈B , []∈B)
∪-unique fA∩fB≡∅ ¬nA∨¬nB {x ∷ l} (inj₂ xl∈B) = inj₂ ((λ xl∈A → fA∩fB≡∅ x (-, xl∈A) (-, xl∈B)) , xl∈B)
