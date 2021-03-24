{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Type.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C; _≈_ to _∼_)

open import Cfe.Language over
open import Cfe.Language.Construct.Concatenate over renaming (_∙_ to _∙ˡ_)
open import Cfe.Language.Construct.Single over
open import Cfe.Type.Base over
open import Data.Bool hiding (_≤_)
open import Data.Bool.Properties
open import Data.Empty
open import Data.List hiding (null)
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Product as Product
open import Data.Sum as Sum
open import Data.Unit hiding (_≤_)
open import Function
open import Relation.Binary.PropositionalEquality

⊨-anticongˡ : ∀ {a b fℓ lℓ} {A : Language a} {B : Language b} {τ : Type fℓ lℓ} → B ≤ A → A ⊨ τ → B ⊨ τ
⊨-anticongˡ B≤A A⊨τ = record
  { n⇒n = A⊨τ.n⇒n ∘ B≤A.f
  ; f⇒f = A⊨τ.f⇒f ∘ Product.map₂ B≤A.f
  ; l⇒l = A⊨τ.l⇒l ∘ Product.map₂ (Product.map₂ (Product.map₂ B≤A.f))
  }
  where
  module B≤A = _≤_ B≤A
  module A⊨τ = _⊨_ A⊨τ

L⊨τ⊥⇒L≈∅ : ∀ {a} {L : Language a} → L ⊨ τ⊥ → L ≈ ∅
L⊨τ⊥⇒L≈∅ {L = L} L⊨τ⊥ = record
  { f = λ {l} → elim l
  ; f⁻¹ = λ ()
  }
  where
  module L⊨τ⊥ = _⊨_ L⊨τ⊥

  elim : ∀ l (l∈L : l ∈ L) → l ∈ ∅
  elim [] []∈L = L⊨τ⊥.n⇒n []∈L
  elim (x ∷ l) xl∈L = L⊨τ⊥.f⇒f (-, xl∈L)

∅⊨τ⊥ : ∅ ⊨ τ⊥
∅⊨τ⊥ = record
  { n⇒n = λ ()
  ; f⇒f = λ ()
  ; l⇒l = λ ()
  }

L⊨τε⇒L≤｛ε｝ : ∀ {a} {L : Language a} → L ⊨ τε → L ≤ ｛ε｝
L⊨τε⇒L≤｛ε｝{L = L} L⊨τε = record
  { f = λ {l} → elim l
  }
  where
  module L⊨τε = _⊨_ L⊨τε

  elim : ∀ l → l ∈ L → l ∈ ｛ε｝
  elim [] []∈L = refl
  elim (x ∷ l) xl∈L = ⊥-elim (L⊨τε.f⇒f (-, xl∈L))

｛ε｝⊨τε : ｛ε｝ ⊨ τε
｛ε｝⊨τε = record
  { n⇒n = const tt
  ; f⇒f = λ ()
  ; l⇒l = λ { ([] , ()) ; (_ ∷ _ , ())}
  }
  where
  open import Data.Unit

｛c｝⊨τ[c] : ∀ c → ｛ c ｝ ⊨ τ[ c ]
｛c｝⊨τ[c] c = record
  { n⇒n = λ ()
  ; f⇒f = λ {x} → λ {([] , (c∼x ∷ []≋[])) → c∼x}
  ; l⇒l = λ {x} → λ
    { ([] , []≢[] , _) → ⊥-elim ([]≢[] refl)
    ; (y ∷ [] , _ , l′ , y∷x∷l′∈｛c｝) → ⊥-elim (xy∉｛c｝ c y x l′ y∷x∷l′∈｛c｝)
    ; (y ∷ z ∷ l , _ , l′ , y∷z∷l++x∷l′∈｛c｝) → ⊥-elim (xy∉｛c｝ c y z (l ++ x ∷ l′) y∷z∷l++x∷l′∈｛c｝)
    }
  }
  where

∙-⊨ : ∀ {a b fℓ₁ lℓ₁ fℓ₂ lℓ₂} {A : Language a} {B : Language b} {τ₁ : Type fℓ₁ lℓ₁} {τ₂ : Type fℓ₂ lℓ₂} →
      A ⊨ τ₁ → B ⊨ τ₂ → τ₁ ⊛ τ₂ → A ∙ˡ B ⊨ τ₁ ∙ τ₂
∙-⊨ {A = A} {B} {τ₁} {τ₂} A⊨τ₁ B⊨τ₂ τ₁⊛τ₂ = record
  { n⇒n = λ { ([] , l∈A , _) → ⊥-elim (¬n₁ l∈A) }
  ; f⇒f = λ
    { (_ , [] , l∈A , l′ , l′∈B , _) → ⊥-elim (¬n₁ l∈A)
    ; (_ , x ∷ l , l∈A , l′ , l′∈B , x≈x ∷ _) → inj₁ (A⊨τ₁.f⇒f (l , A.∈-resp-≋ (x≈x ∷ ≋-refl) l∈A))
    }
  ; l⇒l = {!!}
  }
  where
  module A = Language A
  module A⊨τ₁ = _⊨_ A⊨τ₁
  module B⊨τ₂ = _⊨_ B⊨τ₂
  module τ₁⊛τ₂ = _⊛_ τ₁⊛τ₂

  ¬n₁ : null A → ⊥
  ¬n₁ ε∈A = case ∃[ b ] ((null A → T b) × T (not b)) ∋ Null τ₁ , A⊨τ₁.n⇒n , τ₁⊛τ₂.¬n₁ of λ
    { (false , n⇒n , _) → n⇒n ε∈A
    }
