{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Parse.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over renaming (Carrier to C)

open import Cfe.Context over
open import Cfe.Expression over
open import Cfe.Language over
open import Cfe.Language.Indexed.Construct.Iterate over
open import Cfe.Judgement over
open import Cfe.Parse.Base over
open import Cfe.Type over using (_⊛_; _⊨_)
open import Data.Bool using (T; not; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin as F hiding (_<_)
open import Data.List hiding (null)
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Nat as ℕ hiding (_<_; _⊔_; _^_)
open import Data.Product
open import Data.Sum
open import Data.Vec using ([]; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
open import Data.Vec.Relation.Binary.Pointwise.Extensional
open import Function
open import Level as L renaming (suc to lsuc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡ hiding (subst₂; setoid)

l∈⟦e⟧⇒e⤇l : ∀ {e τ} → ∙,∙ ⊢ e ∶ τ → ∀ {l} → l ∈ ⟦ e ⟧ [] → e ⤇ l
l∈⟦e⟧⇒e⤇l Eps (lift refl) = Eps
l∈⟦e⟧⇒e⤇l (Char c) (lift (c∼y ∷ [])) = Char c∼y
l∈⟦e⟧⇒e⤇l {μ e} (Fix ∙,τ⊢e∶τ) (suc n , l∈⟦e⟧ⁿ⁺¹) = Fix (l∈⟦e⟧⇒e⤇l (subst₂ z≤n ∙,τ⊢e∶τ (Fix ∙,τ⊢e∶τ)) l∈⟦e[μe]⟧)
  where
  open import Relation.Binary.Reasoning.PartialOrder (poset (c ⊔ ℓ))
  ⟦e⟧ⁿ⁺¹≤⟦e[μe]⟧ = begin
    ⟦ e ⟧ (((λ X → ⟦ e ⟧ (X ∷ [])) ^ n) (⟦ ⊥ ⟧ []) ∷ []) ≤⟨ mono e ((fⁿ≤⋃f (λ X → ⟦ e ⟧ (X ∷ [])) n) ∷ []) ⟩
    ⟦ e ⟧ (⋃ (λ X → ⟦ e ⟧ (X ∷ [])) ∷ [])                ≡⟨⟩
    ⟦ e ⟧ (⟦ μ e ⟧ [] ∷ [])                              ≈˘⟨ subst-fun e (μ e) F.zero [] ⟩
    ⟦ e [ μ e / F.zero ] ⟧ []                            ∎
  l∈⟦e[μe]⟧ = _≤_.f ⟦e⟧ⁿ⁺¹≤⟦e[μe]⟧ l∈⟦e⟧ⁿ⁺¹
l∈⟦e⟧⇒e⤇l (Cat ∙,∙⊢e₁∶τ₁ ∙,∙⊢e₂∶τ₂ τ₁⊛τ₂) record { l₁∈A = l₁∈⟦e₁⟧ ; l₂∈B = l₂∈⟦e₂⟧ ; eq = eq } =
  Cat (l∈⟦e⟧⇒e⤇l ∙,∙⊢e₁∶τ₁ l₁∈⟦e₁⟧) (l∈⟦e⟧⇒e⤇l ∙,∙⊢e₂∶τ₂ l₂∈⟦e₂⟧) eq
l∈⟦e⟧⇒e⤇l (Vee ∙,∙⊢e₁∶τ₁ ∙,∙⊢e₂∶τ₂ τ₁#τ₂) (inj₁ l∈⟦e₁⟧) = Veeˡ (l∈⟦e⟧⇒e⤇l ∙,∙⊢e₁∶τ₁ l∈⟦e₁⟧)
l∈⟦e⟧⇒e⤇l (Vee ∙,∙⊢e₁∶τ₁ ∙,∙⊢e₂∶τ₂ τ₁#τ₂) (inj₂ l∈⟦e₂⟧) = Veeʳ (l∈⟦e⟧⇒e⤇l ∙,∙⊢e₂∶τ₂ l∈⟦e₂⟧)

e⤇l→l∈⟦e⟧ : ∀ {e τ} → ∙,∙ ⊢ e ∶ τ → ∀ {l} → e ⤇ l → l ∈ ⟦ e ⟧ []
e⤇l→l∈⟦e⟧ ∙,∙⊢e∶τ Eps = L.lift ≡.refl
e⤇l→l∈⟦e⟧ ∙,∙⊢e∶τ (Char y∼c) = L.lift (y∼c ∷ [])
e⤇l→l∈⟦e⟧ (Cat ∙,∙⊢e₁∶τ₁ ∙,∙⊢e₂∶τ₂ _) (Cat e₁⤇l₁ e₂⤇l₂ eq) = record
  { l₁∈A = e⤇l→l∈⟦e⟧ ∙,∙⊢e₁∶τ₁ e₁⤇l₁
  ; l₂∈B = e⤇l→l∈⟦e⟧ ∙,∙⊢e₂∶τ₂ e₂⤇l₂
  ; eq = eq
  }
e⤇l→l∈⟦e⟧ (Vee ∙,∙⊢e∶τ _ _) (Veeˡ e⤇l) = inj₁ (e⤇l→l∈⟦e⟧ ∙,∙⊢e∶τ e⤇l)
e⤇l→l∈⟦e⟧ (Vee _ ∙,∙⊢e∶τ _) (Veeʳ e⤇l) = inj₂ (e⤇l→l∈⟦e⟧ ∙,∙⊢e∶τ e⤇l)
e⤇l→l∈⟦e⟧ ∙,∙⊢e∶τ (Fix e⤇l) = {!!}
