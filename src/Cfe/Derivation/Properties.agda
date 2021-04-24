{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Derivation.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C)

open import Cfe.Context over using (∙,∙)
open import Cfe.Derivation.Base over
open import Cfe.Expression over
open import Cfe.Fin using (zero)
open import Cfe.Judgement over
open import Cfe.Language over hiding (_∙_)
open import Cfe.Type over using (_⊛_; _⊨_)
open import Data.Fin using (zero)
open import Data.List using (List; []; length)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.Nat.Properties using (n<1+n; module ≤-Reasoning)
open import Data.Product using (_×_; _,_; -,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using ([]; [_])
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)
open import Function using (_∘_)
open import Induction.WellFounded
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (refl)
import Relation.Binary.Reasoning.PartialOrder (⊆-poset {c ⊔ ℓ}) as ⊆-Reasoning
open import Relation.Nullary using (¬_)

w∈⟦e⟧⇒e⤇w : ∀ {e τ} → ∙,∙ ⊢ e ∶ τ → ∀ {w} → w ∈ ⟦ e ⟧ [] → e ⤇ w
w∈⟦e⟧⇒e⤇w {e = e} ctx⊢e∶τ {w} w∈⟦e⟧ = All.wfRec <ₗₑₓ-wellFounded _ Pred go (w , e) ctx⊢e∶τ w∈⟦e⟧
  where
  Pred : (List C × Expression 0) → Set _
  Pred (w , e) = ∀ {τ} → ∙,∙ ⊢ e ∶ τ → w ∈ ⟦ e ⟧ [] → e ⤇ w

  go : ∀ w,e → WfRec _<ₗₑₓ_ Pred w,e → Pred w,e
  go ([] , ε)       rec Eps      w∈⟦e⟧      = Eps
  go (w  , Char c)  rec (Char c) (c∼y ∷ []) = Char c∼y
  go (w  , μ e)     rec (Fix ctx⊢e∶τ) w∈⟦e⟧ =
    Fix (rec
      (w , e [ μ e / zero ])
      w,e[μe/0]<ₗₑₓw,μe
      (subst₂ ctx⊢e∶τ zero (Fix ctx⊢e∶τ))
      (∈-resp-⊆ ⟦μe⟧⊆⟦e[μe/0]⟧ w∈⟦e⟧))
    where
    w,e[μe/0]<ₗₑₓw,μe : (w , e [ μ e / zero ]) <ₗₑₓ (w , μ e)
    w,e[μe/0]<ₗₑₓw,μe = inj₂ (refl , (begin-strict
      rank (e [ μ e / zero ]) ≡⟨ subst₂-pres-rank ctx⊢e∶τ zero (Fix ctx⊢e∶τ) ⟩
      rank e                  <⟨ rank-μ e ⟩
      rank (μ e)              ∎))
      where open ≤-Reasoning

    ⟦μe⟧⊆⟦e[μe/0]⟧ : ⟦ μ e ⟧ [] ⊆ ⟦ e [ μ e / zero ] ⟧ []
    ⟦μe⟧⊆⟦e[μe/0]⟧ = begin
      ⟦ μ e ⟧ []              ≤⟨ ⋃-unroll (⟦⟧-mono-env e ∘ (_∷ [])) ⟩
      ⟦ e ⟧ [ ⟦ μ e ⟧ [] ]    ≈˘⟨ subst-cong e (μ e) zero [] ⟩
      ⟦ e [ μ e / zero ] ⟧ [] ∎
      where open ⊆-Reasoning
  go (w  , e₁ ∙ e₂) rec (Cat ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁⊛τ₂) (w₁ , w₂ , w₁∈⟦e₁⟧ , w₂∈⟦e₂⟧ , eq) =
    Cat
      (rec (w₁ , e₁) (lex-∙ˡ e₁ e₂ []        (-, -, w₁∈⟦e₁⟧ , w₂∈⟦e₂⟧ , eq)) ctx⊢e₁∶τ₁ w₁∈⟦e₁⟧)
      (rec (w₂ , e₂) (lex-∙ʳ e₁ e₂ [] ε∉⟦e₁⟧ (-, -, w₁∈⟦e₁⟧ , w₂∈⟦e₂⟧ , eq)) ctx⊢e₂∶τ₂ w₂∈⟦e₂⟧)
      eq
    where
    open _⊛_ τ₁⊛τ₂ using (¬n₁)
    ε∉⟦e₁⟧ : ¬ Null (⟦ e₁ ⟧ [])
    ε∉⟦e₁⟧ = ¬n₁ ∘ _⊨_.n⇒n (soundness ctx⊢e₁∶τ₁ [] [])
  go (w , e₁ ∨ e₂) rec (Vee ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁#τ₂) (inj₁ w∈⟦e₁⟧) =
    Veeˡ (rec (w , e₁) (inj₂ (refl , rank-∨ˡ e₁ e₂)) ctx⊢e₁∶τ₁ w∈⟦e₁⟧)
  go (w , e₁ ∨ e₂) rec (Vee ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁#τ₂) (inj₂ w∈⟦e₂⟧) =
    Veeʳ (rec (w , e₂) (inj₂ (refl , rank-∨ʳ e₁ e₂)) ctx⊢e₂∶τ₂ w∈⟦e₂⟧)
