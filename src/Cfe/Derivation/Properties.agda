{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Derivation.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over renaming (Carrier to C)

open import Cfe.Context over hiding (_≋_)
open import Cfe.Expression over hiding (_≋_)
open import Cfe.Language over hiding (≤-refl)
open import Cfe.Language.Construct.Concatenate over using (Concat)
open import Cfe.Language.Indexed.Construct.Iterate over
open import Cfe.Judgement over
open import Cfe.Derivation.Base over
open import Cfe.Type over using (_⊛_; _⊨_)
open import Data.Bool using (T; not; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin as F hiding (_<_)
open import Data.List hiding (null)
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Nat as ℕ hiding (_⊔_; _^_; _<_)
open import Data.Nat.Properties using (≤-step; m≤m+n; m≤n+m; ≤-refl; n<1+n; module ≤-Reasoning)
open import Data.Nat.Induction using () renaming (<-wellFounded to <ⁿ-wellFounded)
open import Data.Product as Product
open import Data.Product.Relation.Binary.Lex.Strict
open import Data.Sum as Sum
open import Data.Vec hiding (length; _++_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
open import Data.Vec.Relation.Binary.Pointwise.Extensional
open import Function
open import Induction.WellFounded
open import Level
open import Relation.Binary
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality as ≡ hiding (subst₂; setoid)

private
  infix 4 _<_
  _<_ : Rel (List C × Expression 0) _
  _<_ = ×-Lex _≡_ ℕ._<_ ℕ._<_ on (Product.map length rank)

  <-wellFounded : WellFounded _<_
  <-wellFounded = On.wellFounded (Product.map length rank) (×-wellFounded <ⁿ-wellFounded <ⁿ-wellFounded)

l∈⟦e⟧⇒e⤇l : ∀ {e τ} → ∙,∙ ⊢ e ∶ τ → ∀ {l} → l ∈ ⟦ e ⟧ [] → e ⤇ l
l∈⟦e⟧⇒e⤇l {e} {τ} ∙,∙⊢e∶τ {l} l∈⟦e⟧ = All.wfRec <-wellFounded _ Pred go (l , e) ∙,∙⊢e∶τ l∈⟦e⟧
  where
  Pred : List C × Expression 0 → Set _
  Pred (l , e) = ∀ {τ} → ∙,∙ ⊢ e ∶ τ → l ∈ ⟦ e ⟧ [] → e ⤇ l

  e[μe/0]<μe : ∀ {e τ} l → ∙,∙ ⊢ μ e ∶ τ → (l , e [ μ e / F.zero ]) < (l , μ e)
  e[μe/0]<μe {e} l (Fix ∙,τ⊢e∶τ)= inj₂ (≡.refl , (begin-strict
    rank (e [ μ e / F.zero ]) ≡⟨ subst-preserves-rank z≤n ∙,τ⊢e∶τ (Fix ∙,τ⊢e∶τ) ⟩
    rank e                    <⟨ n<1+n (rank e) ⟩
    ℕ.suc (rank e)            ≡⟨⟩
    rank (μ e)                ∎))
    where
    open ≤-Reasoning

  l₁++l₂≋l⇒∣l₁∣≤∣l∣ : ∀ {l₂ l} l₁ → l₁ ++ l₂ ≋ l → (length l₁ ℕ.< length l) ⊎ (length l₁ ≡ length l)
  l₁++l₂≋l⇒∣l₁∣≤∣l∣ [] [] = inj₂ ≡.refl
  l₁++l₂≋l⇒∣l₁∣≤∣l∣ [] (_ ∷ _) = inj₁ (s≤s z≤n)
  l₁++l₂≋l⇒∣l₁∣≤∣l∣ (_ ∷ l₁) (_ ∷ eq) = Sum.map s≤s (cong ℕ.suc) (l₁++l₂≋l⇒∣l₁∣≤∣l∣ l₁ eq)

  l₁++l₂≋l⇒∣l₂∣≤∣l∣ : ∀ {l₂ l} l₁ → l₁ ++ l₂ ≋ l → (length l₂ ℕ.< length l) ⊎ (length l₁ ≡ 0)
  l₁++l₂≋l⇒∣l₂∣≤∣l∣ [] _ = inj₂ ≡.refl
  l₁++l₂≋l⇒∣l₂∣≤∣l∣ (_ ∷ []) (_ ∷ []) = inj₁ (s≤s z≤n)
  l₁++l₂≋l⇒∣l₂∣≤∣l∣ (x ∷ []) (x∼y ∷ _ ∷ eq) = inj₁ ([ s≤s , (λ ()) ]′ (l₁++l₂≋l⇒∣l₂∣≤∣l∣ (x ∷ []) (x∼y ∷ eq)))
  l₁++l₂≋l⇒∣l₂∣≤∣l∣ (_ ∷ x ∷ l₁) (_ ∷ eq) = inj₁ ([ ≤-step , (λ ()) ]′ (l₁++l₂≋l⇒∣l₂∣≤∣l∣ (x ∷ l₁) eq))

  e₁<e₁∙e₂ : ∀ {l e₁} e₂ → (l∈⟦e₁∙e₂⟧ : l ∈ ⟦ e₁ ∙ e₂ ⟧ []) → (Concat.l₁ l∈⟦e₁∙e₂⟧ , e₁) < (l , e₁ ∙ e₂)
  e₁<e₁∙e₂ _ l∈⟦e₁∙e₂⟧ with l₁++l₂≋l⇒∣l₁∣≤∣l∣ (Concat.l₁ l∈⟦e₁∙e₂⟧) (Concat.eq l∈⟦e₁∙e₂⟧)
  ... | inj₁ ∣l₁∣<∣l∣ = inj₁ ∣l₁∣<∣l∣
  ... | inj₂ ∣l₁∣≡∣l∣ = inj₂ (∣l₁∣≡∣l∣ , ≤-refl)

  e₂<e₁∙e₂ : ∀ {l e₁ e₂ τ} → ∙,∙ ⊢ e₁ ∙ e₂ ∶ τ → (l∈⟦e₁∙e₂⟧ : l ∈ ⟦ e₁ ∙ e₂ ⟧ []) → (Concat.l₂ l∈⟦e₁∙e₂⟧ , e₂) < (l , e₁ ∙ e₂)
  e₂<e₁∙e₂ (Cat ∙,∙⊢e₁∶τ₁ _ τ₁⊛τ₂) l∈⟦e₁∙e₂⟧ with l₁++l₂≋l⇒∣l₂∣≤∣l∣ (Concat.l₁ l∈⟦e₁∙e₂⟧) (Concat.eq l∈⟦e₁∙e₂⟧)
  ... | inj₁ ∣l₂∣<∣l∣ = inj₁ ∣l₂∣<∣l∣
  ... | inj₂ ∣l₁∣≡0 with Concat.l₁ l∈⟦e₁∙e₂⟧ | Concat.l₁∈A l∈⟦e₁∙e₂⟧ | (_⊛_.τ₁.Null τ₁⊛τ₂) | _⊛_.¬n₁ τ₁⊛τ₂ | _⊨_.n⇒n (soundness ∙,∙⊢e₁∶τ₁ [] (ext (λ ()))) | ∣l₁∣≡0
  ... | [] | ε∈A | false | _ | n⇒n | refl = ⊥-elim (n⇒n ε∈A)

  e₁<e₁∨e₂ : ∀ l e₁ e₂ → (l , e₁) < (l , e₁ ∨ e₂)
  e₁<e₁∨e₂ _ e₁ e₂ = inj₂ (≡.refl , (begin-strict
    rank e₁                     ≤⟨ m≤m+n (rank e₁) (rank e₂) ⟩
    rank e₁ ℕ.+ rank e₂         <⟨ n<1+n (rank e₁ ℕ.+ rank e₂ ) ⟩
    ℕ.suc (rank e₁ ℕ.+ rank e₂) ≡⟨⟩
    rank (e₁ ∨ e₂)              ∎))
    where
    open ≤-Reasoning

  e₂<e₁∨e₂ : ∀ l e₁ e₂ → (l , e₂) < (l , e₁ ∨ e₂)
  e₂<e₁∨e₂ _ e₁ e₂ = inj₂ (≡.refl , (begin-strict
    rank e₂                     ≤⟨ m≤n+m (rank e₂) (rank e₁) ⟩
    rank e₁ ℕ.+ rank e₂         <⟨ n<1+n (rank e₁ ℕ.+ rank e₂ ) ⟩
    ℕ.suc (rank e₁ ℕ.+ rank e₂) ≡⟨⟩
    rank (e₁ ∨ e₂)              ∎))
    where
    open ≤-Reasoning

  l∈⟦e⟧ⁿ⇒l∈⟦e[μe/0]⟧ : ∀ {l} e n → l ∈ ((λ X → ⟦ e ⟧ (X ∷ [])) ^ n) (⟦ ⊥ ⟧ []) → l ∈ ⟦ e [ μ e / F.zero ] ⟧ []
  l∈⟦e⟧ⁿ⇒l∈⟦e[μe/0]⟧ e (suc n) l∈⟦e⟧ⁿ = _≤_.f
    (begin
      ((λ X → ⟦ e ⟧ (X ∷ [])) ^ (ℕ.suc n)) (⟦ ⊥ ⟧ [])      ≡⟨⟩
      ⟦ e ⟧ (((λ X → ⟦ e ⟧ (X ∷ [])) ^ n) (⟦ ⊥ ⟧ []) ∷ []) ≤⟨ mono e (fⁿ≤⋃f (λ X → ⟦ e ⟧ (X ∷ [])) n ∷ []) ⟩
      ⟦ e ⟧ (⋃ (λ X → ⟦ e ⟧ (X ∷ [])) ∷ [])                ≡⟨⟩
      ⟦ e ⟧ (⟦ μ e ⟧ [] ∷ [])                              ≈˘⟨ subst-fun e (μ e) F.zero [] ⟩
      ⟦ e [ μ e / F.zero ] ⟧ []                            ∎)
    l∈⟦e⟧ⁿ
    where
    open import Relation.Binary.Reasoning.PartialOrder (poset _)

  go : ∀ l,e → WfRec _<_ Pred l,e → Pred l,e
  go (l , e) rec Eps (lift refl) = Eps
  go (l , e) rec (Char c) (lift (c∼y ∷ [])) = Char c∼y
  go (l , μ e) rec (Fix ∙,τ⊢e∶τ) (n , l∈⟦e⟧ⁿ) =
    Fix (rec
      (l , e [ μ e / F.zero ])
      (e[μe/0]<μe l (Fix ∙,τ⊢e∶τ))
      (subst₂ z≤n ∙,τ⊢e∶τ (Fix ∙,τ⊢e∶τ))
      (l∈⟦e⟧ⁿ⇒l∈⟦e[μe/0]⟧ e n l∈⟦e⟧ⁿ))
  go (l , e₁ ∙ e₂) rec (∙,∙⊢e₁∙e₂∶τ @ (Cat ∙,∙⊢e₁∶τ₁ ∙,∙⊢e₂∶τ₂ _)) l∈⟦e⟧ =
    Cat
      (rec (l∈⟦e⟧.l₁ , e₁) (e₁<e₁∙e₂ e₂ l∈⟦e⟧) ∙,∙⊢e₁∶τ₁ l∈⟦e⟧.l₁∈A)
      (rec (l∈⟦e⟧.l₂ , e₂) (e₂<e₁∙e₂ ∙,∙⊢e₁∙e₂∶τ  l∈⟦e⟧) ∙,∙⊢e₂∶τ₂ l∈⟦e⟧.l₂∈B)
      l∈⟦e⟧.eq
    where
    module l∈⟦e⟧ = Concat l∈⟦e⟧
  go (l , e₁ ∨ e₂) rec (Vee ∙,∙⊢e₁∶τ₁ _ _) (inj₁ l∈⟦e₁⟧) = Veeˡ (rec (l , e₁) (e₁<e₁∨e₂ l e₁ e₂) ∙,∙⊢e₁∶τ₁ l∈⟦e₁⟧)
  go (l , e₁ ∨ e₂) rec (Vee _ ∙,∙⊢e₂∶τ₂ _) (inj₂ l∈⟦e₂⟧) = Veeʳ (rec (l , e₂) (e₂<e₁∨e₂ l e₁ e₂) ∙,∙⊢e₂∶τ₂ l∈⟦e₂⟧)
