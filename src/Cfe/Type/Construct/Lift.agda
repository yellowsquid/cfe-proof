{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Type.Construct.Lift
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Type over
open import Cfe.Language over using (Language)
open import Level as L hiding (Lift)
open import Function

Lift : ∀ {fℓ₁ lℓ₁} fℓ₂ lℓ₂ → Type fℓ₁ lℓ₁ → Type (fℓ₁ ⊔ fℓ₂) (lℓ₁ ⊔ lℓ₂)
Lift fℓ₂ lℓ₂ τ = record
  { Null = τ.Null
  ; First = L.Lift fℓ₂ ∘ τ.First
  ; Flast = L.Lift lℓ₂ ∘ τ.Flast
  }
  where
  module τ = Type τ

⊨-liftʳ : ∀ {a fℓ₁ lℓ₁} {L : Language a} {τ : Type fℓ₁ lℓ₁} fℓ₂ lℓ₂ → L ⊨ τ → L ⊨ Lift fℓ₂ lℓ₂ τ
⊨-liftʳ _ _ L⊨τ = record
  { n⇒n = n⇒n
  ; f⇒f = lift ∘ f⇒f
  ; l⇒l = lift ∘ l⇒l
  }
  where
  open _⊨_ L⊨τ
