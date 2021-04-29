{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid)

module Cfe.Derivation.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C)

open import Cfe.Context over using (_⊐_; Γ,Δ; ∙,∙; remove₁) renaming (wkn₂ to wkn₂ᶜ)
open import Cfe.Derivation.Base over
open import Cfe.Expression over
open import Cfe.Fin using (zero; inj; raise!>; cast>)
open import Cfe.Judgement over
open import Cfe.Language over hiding (_∙_)
  renaming (_≈_ to _≈ˡ_; ≈-refl to ≈ˡ-refl; ≈-reflexive to ≈ˡ-reflexive; ≈-sym to ≈ˡ-sym)
open import Cfe.Type over using (_⊛_; _⊨_)
open import Cfe.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise-insert)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc; _≟_; punchOut; punchIn)
open import Data.Fin.Properties using (punchIn-punchOut)
open import Data.List using (List; []; length; _++_)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Binary.Equality.Setoid over using (_≋_; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise-length)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _+_) renaming (_≤_ to _≤ⁿ_)
open import Data.Nat.Properties using (n<1+n; m≤m+n; m≤n+m; m≤n⇒m<n∨m≡n; module ≤-Reasoning)
open import Data.Product using (_×_; _,_; -,_; ∃-syntax; map₂; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Vec using ([]; _∷_; [_]; lookup; insert)
open import Data.Vec.Properties using (insert-lookup; insert-punchIn)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as Pw using ([]; _∷_)
open import Function using (_∘_; _|>_; _on_; flip)
open import Induction.WellFounded
open import Level using (_⊔_; lift)
open import Relation.Binary.Construct.On using () renaming (wellFounded to on-wellFounded)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary
open import Relation.Nullary.Decidable using (fromWitness)

parse : ∀ {e τ} → ∙,∙ ⊢ e ∶ τ → ∀ {w} → w ∈ ⟦ e ⟧ [] → e ⤇ w
parse {e = e} ctx⊢e∶τ {w} w∈⟦e⟧ = All.wfRec <ₗₑₓ-wellFounded _ Pred go (w , e) ctx⊢e∶τ w∈⟦e⟧
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
      ⟦ μ e ⟧ []              ⊆⟨  ⋃-unroll (⟦⟧-mono-env e ∘ (_∷ [])) ⟩
      ⟦ e ⟧ [ ⟦ μ e ⟧ [] ]    ≈˘⟨ ⟦⟧-subst e (μ e) zero [] ⟩
      ⟦ e [ μ e / zero ] ⟧ [] ∎
      where open ⊆-Reasoning
  go (w  , e₁ ∙ e₂) rec (Cat ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁⊛τ₂) (w₁ , w₂ , w₁∈⟦e₁⟧ , w₂∈⟦e₂⟧ , eq) =
    Cat
      (rec (w₁ , e₁) (lex-∙ˡ e₁ e₂ w₁ eq) ctx⊢e₁∶τ₁ w₁∈⟦e₁⟧)
      (rec (w₂ , e₂) (lex-∙ʳ e₁ e₂ [] ε∉⟦e₁⟧ w₁∈⟦e₁⟧ eq) ctx⊢e₂∶τ₂ w₂∈⟦e₂⟧)
      eq
    where
    open _⊛_ τ₁⊛τ₂ using (¬n₁)
    ε∉⟦e₁⟧ : ¬ Null (⟦ e₁ ⟧ [])
    ε∉⟦e₁⟧ = ¬n₁ ∘ _⊨_.n⇒n (soundness ctx⊢e₁∶τ₁ [] [])
  go (w , e₁ ∨ e₂) rec (Vee ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁#τ₂) (inj₁ w∈⟦e₁⟧) =
    Veeˡ (rec (w , e₁) (inj₂ (refl , rank-∨ˡ e₁ e₂)) ctx⊢e₁∶τ₁ w∈⟦e₁⟧)
  go (w , e₁ ∨ e₂) rec (Vee ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁#τ₂) (inj₂ w∈⟦e₂⟧) =
    Veeʳ (rec (w , e₂) (inj₂ (refl , rank-∨ʳ e₁ e₂)) ctx⊢e₂∶τ₂ w∈⟦e₂⟧)

generate : ∀ {e τ} → ∙,∙ ⊢ e ∶ τ → ∀ {w} → e ⤇ w → w ∈ ⟦ e ⟧ []
generate {e = e} ctx⊢e∶τ {w} e⤇w = All.wfRec <ₗₑₓ-wellFounded _ Pred go (w , e) ctx⊢e∶τ e⤇w
  where
  Pred : (List C × Expression 0) → Set _
  Pred (w , e) = ∀ {τ} → ∙,∙ ⊢ e ∶ τ → e ⤇ w → w ∈ ⟦ e ⟧ []

  go : ∀ w,e → WfRec _<ₗₑₓ_ Pred w,e → Pred w,e
  go (w , ε)       rec Eps      Eps = lift refl
  go (w , Char c)  rec (Char c) (Char c∼y) = c∼y ∷ []
  go (w , μ e)     rec (Fix ctx⊢e∶τ) (Fix e[μe/0]⤇w) = ∈-resp-≈ (μ-roll e []) w∈⟦e[μe/0]⟧
    where
    w,e[μe/0]<ₗₑₓw,μe : (w , e [ μ e / zero ]) <ₗₑₓ (w , μ e)
    w,e[μe/0]<ₗₑₓw,μe = inj₂ (refl , (begin-strict
      rank (e [ μ e / zero ]) ≡⟨ subst₂-pres-rank ctx⊢e∶τ zero (Fix ctx⊢e∶τ) ⟩
      rank e                  <⟨ rank-μ e ⟩
      rank (μ e)              ∎))
      where open ≤-Reasoning

    w∈⟦e[μe/0]⟧ : w ∈ ⟦ e [ μ e / zero ] ⟧ []
    w∈⟦e[μe/0]⟧ = rec (w , e [ μ e / zero ]) w,e[μe/0]<ₗₑₓw,μe (subst₂ ctx⊢e∶τ zero (Fix ctx⊢e∶τ)) e[μe/0]⤇w
  go (w , e₁ ∙ e₂) rec (Cat ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁⊛τ₂) (Cat {w₁ = w₁} {w₂} e₁⤇w₁ e₂⤇w₂ eq) =
    w₁ , w₂ , w₁∈⟦e₁⟧ , w₂∈⟦e₂⟧ , eq
    where
    open _⊛_ τ₁⊛τ₂ using (¬n₁)
    ε∉⟦e₁⟧ : ¬ Null (⟦ e₁ ⟧ [])
    ε∉⟦e₁⟧ = ¬n₁ ∘ _⊨_.n⇒n (soundness ctx⊢e₁∶τ₁ [] [])

    w₁∈⟦e₁⟧ = rec (w₁ , e₁) (lex-∙ˡ e₁ e₂ w₁ eq) ctx⊢e₁∶τ₁ e₁⤇w₁
    w₂∈⟦e₂⟧ = rec (w₂ , e₂) (lex-∙ʳ e₁ e₂ [] ε∉⟦e₁⟧ w₁∈⟦e₁⟧ eq) ctx⊢e₂∶τ₂ e₂⤇w₂
  go (w , e₁ ∨ e₂) rec (Vee ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁#τ₂) (Veeˡ e₁⤇w) =
    inj₁ (rec (w , e₁) (inj₂ (refl , rank-∨ˡ e₁ e₂)) ctx⊢e₁∶τ₁ e₁⤇w)
  go (w , e₁ ∨ e₂) rec (Vee ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁#τ₂) (Veeʳ e₂⤇w) =
    inj₂ (rec (w , e₂) (inj₂ (refl , rank-∨ʳ e₁ e₂)) ctx⊢e₂∶τ₂ e₂⤇w)
