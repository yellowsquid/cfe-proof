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
open import Data.Fin as F
open import Data.List hiding (null)
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Nat as ℕ hiding (_⊔_; _^_)
open import Data.Product
open import Data.Sum
open import Data.Vec
open import Data.Vec.Relation.Binary.Pointwise.Inductive
open import Data.Vec.Relation.Binary.Pointwise.Extensional
open import Function
open import Level
open import Relation.Binary.PropositionalEquality hiding (subst₂; setoid)

private
  data Ranked : ℕ → ℕ → Set c where
    ⊥ : ∀ {n} → Ranked 0 n
    ε : ∀ {n} → Ranked 0 n
    Char : ∀ {n} → C → Ranked 0 n
    _∨_ : ∀ {r s n} → Ranked r n → Ranked s n → Ranked (ℕ.suc (r ℕ.+ s)) n
    _∙_ : ∀ {r s n} → Ranked r n → Ranked s n → Ranked (ℕ.suc r) n
    Var : ∀ {n} → Fin n → Ranked 0 n
    μ : ∀ {r n} → Ranked r (ℕ.suc n) → Ranked (ℕ.suc r) n

  fromRanked : ∀ {r n} → Ranked r n → Expression n
  fromRanked ⊥ = ⊥
  fromRanked ε = ε
  fromRanked (Char x) = Char x
  fromRanked (r₁ ∨ r₂) = fromRanked r₁ ∨ fromRanked r₂
  fromRanked (r₁ ∙ r₂) = fromRanked r₁ ∙ fromRanked r₂
  fromRanked (Var x) = Var x
  fromRanked (μ r) = μ (fromRanked r)

  toRanked : ∀ {n} → (e : Expression n) → Ranked (rank e) n
  toRanked ⊥ = ⊥
  toRanked ε = ε
  toRanked (Char x) = Char x
  toRanked (e₁ ∨ e₂) = toRanked e₁ ∨ toRanked e₂
  toRanked (e₁ ∙ e₂) = toRanked e₁ ∙ toRanked e₂
  toRanked (Var x) = Var x
  toRanked (μ e) = μ (toRanked e)
  
  l∈⟦e⟧⇒e⤇l′ : ∀ {l r e τ} → ∙,∙ ⊢ fromRanked {r} e ∶ τ → l ∈ ⟦ fromRanked e ⟧ [] → fromRanked e ⤇ l
  l∈⟦e⟧⇒e⤇l′ {[]} {ℕ.zero} {ε} ∙,∙⊢e∶τ l∈⟦e⟧ = Eps
  l∈⟦e⟧⇒e⤇l′ {[]} {ℕ.suc _} {e₁ ∨ e₂} (Vee ∙,∙⊢e₁∶τ₁ ∙,∙⊢e₂∶τ₂ τ₁#τ₂) (inj₁ l∈⟦e₁⟧) = Veeˡ (l∈⟦e⟧⇒e⤇l′ ∙,∙⊢e₁∶τ₁ l∈⟦e₁⟧)
  l∈⟦e⟧⇒e⤇l′ {[]} {ℕ.suc _} {e₁ ∨ e₂} (Vee ∙,∙⊢e₁∶τ₁ ∙,∙⊢e₂∶τ₂ τ₁#τ₂) (inj₂ l∈⟦e₂⟧) = Veeʳ (l∈⟦e⟧⇒e⤇l′ ∙,∙⊢e₂∶τ₂ l∈⟦e₂⟧)
  l∈⟦e⟧⇒e⤇l′ {[]} {ℕ.suc r} {e₁ ∙ e₂} (Cat ∙,∙⊢e₁∶τ₁ ∙,∙⊢e₂∶τ₂ τ₁⊛τ₂) record { l₁ = [] ; l₁∈A = l∈⟦e₁⟧ } =
    case ∃[ b ] (T (not b) × (null (⟦ fromRanked e₁ ⟧ []) → T b)) ∋ τ₁⊛τ₂.τ₁.Null , τ₁⊛τ₂.¬n₁ , ⟦e₁⟧⊨τ₁.n⇒n of λ
      { (false , _ , n⇒n) → ⊥-elim (n⇒n l∈⟦e₁⟧)
      ; (true , ¬n₁ , _) → ⊥-elim ¬n₁
      }
    where
    module τ₁⊛τ₂ = _⊛_ τ₁⊛τ₂
    module ⟦e₁⟧⊨τ₁ = _⊨_ (soundness ∙,∙⊢e₁∶τ₁ [] (ext (λ ())))
  l∈⟦e⟧⇒e⤇l′ {[]} {ℕ.suc r} {μ e} ∙,∙⊢e∶τ l∈⟦e⟧ = Fix {!l∈⟦e⟧⇒e⤇l′!}
  l∈⟦e⟧⇒e⤇l′ {x ∷ l} {r} {e} ∙,∙⊢e∶τ l∈⟦e⟧ = {!!}

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
