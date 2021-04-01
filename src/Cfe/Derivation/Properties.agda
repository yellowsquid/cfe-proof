{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Derivation.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over renaming (Carrier to C; _≈_ to _∼_)

open import Cfe.Context over hiding (_≋_) renaming (≋-sym to ≋ᶜ-sym)
open import Cfe.Expression over hiding (_≋_)
open import Cfe.Language over hiding (≤-refl; _<_) renaming (_≈_ to _≈ˡ_)
open import Cfe.Language.Construct.Concatenate over using (Concat)
open import Cfe.Language.Indexed.Construct.Iterate over
open import Cfe.Judgement over renaming (wkn₁ to wkn₁ⱼ; shift≤ to shift≤ⱼ)
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
open import Data.Vec.Relation.Binary.Pointwise.Extensional as PW
open import Function
open import Induction.WellFounded
open import Level hiding (Lift)
open import Relation.Binary
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality as ≡ hiding (subst₂; setoid)

private
  infix 4 _<_
  _<_ : ∀ {m n} → REL (List C × Expression m) (List C × Expression n) _
  (l , e) < (l′ , e′) = length l ℕ.< length l′ ⊎ length l ≡ length l′ × e <ᵣₐₙₖ e′

  <-wellFounded : ∀ {n} → WellFounded (_<_ {n})
  <-wellFounded = On.wellFounded (Product.map₁ length) (×-wellFounded <ⁿ-wellFounded <ᵣₐₙₖ-wellFounded)

unroll₁ : ∀ {n} {Γ,Δ : Context n} {e e′ τ τ′ i} (i≥m : toℕ i ℕ.≥ _) →
          wkn₁ Γ,Δ i≥m τ′ ⊢ e ∶ τ → Γ,Δ ⊢ μ e′ ∶ τ′ →
          ∀ {l} γ → PW.Pointwise _⊨_ γ (toVec Γ,Δ) →
          l ∈ ⟦ e ⟧ (insert γ i (⟦ μ e′ ⟧ γ)) →
          ∃[ n ] l ∈ ⟦ e ⟧ (insert γ i (((λ X → ⟦ e′ ⟧ (X ∷ γ)) ^ n) (Lift _ ∅)))
unroll₁ {e = e} i≥m Γ,Δ⊢e∶τ Γ,Δ⊢e′∶τ′ {l = l} γ γ⊨Γ,Δ l∈⟦e⟧ =
  All.wfRec <-wellFounded _ Pred go (l , e) i≥m Γ,Δ⊢e∶τ Γ,Δ⊢e′∶τ′ γ γ⊨Γ,Δ l∈⟦e⟧
  where
  Pred : ∀ {n} → List C × Expression (ℕ.suc n) → Set _
  Pred {n} (l , e) =
    ∀ {Γ,Δ : Context n} {e′ τ τ′ i} (i≥m : toℕ i ℕ.≥ _) →
    wkn₁ Γ,Δ i≥m τ′ ⊢ e ∶ τ → Γ,Δ ⊢ μ e′ ∶ τ′ →
    ∀ γ → PW.Pointwise _⊨_ γ (toVec Γ,Δ) →
    l ∈ ⟦ e ⟧ (insert γ i (⟦ μ e′ ⟧ γ)) →
    ∃[ n ] l ∈ ⟦ e ⟧ (insert γ i (((λ X → ⟦ e′ ⟧ (X ∷ γ)) ^ n) (⟦ ⊥ ⟧ γ)))

  go : ∀ {n} l,e → WfRec _<_ (Pred {n}) l,e → Pred l,e
  go (l , ε) rec i≥m Γ,Δ⊢e∶τ Γ,Δ⊢e′∶τ′ γ γ⊨Γ,Δ l∈⟦e⟧ = 1 , l∈⟦e⟧
  go (l , Char x) rec i≥m Γ,Δ⊢e∶τ Γ,Δ⊢e′∶τ′ γ γ⊨Γ,Δ l∈⟦e⟧ = 1 , l∈⟦e⟧
  go (l , (e₁ ∨ e₂)) rec i≥m (Vee Γ,Δ⊢e₁∶τ₁ _ _) Γ,Δ⊢e′∶τ′ γ γ⊨Γ,Δ (inj₁ l∈⟦e₁⟧) =
    Product.map₂ inj₁ (rec (l , e₁) {!!} i≥m Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e′∶τ′ γ γ⊨Γ,Δ l∈⟦e₁⟧)
  go (l , (e₁ ∨ e₂)) rec i≥m (Vee _ Γ,Δ⊢e₂∶τ₂ _) Γ,Δ⊢e′∶τ′ γ γ⊨Γ,Δ (inj₂ l∈⟦e₂⟧) =
    Product.map₂ inj₂ (rec (l , e₂) {!!} i≥m Γ,Δ⊢e₂∶τ₂ Γ,Δ⊢e′∶τ′ γ γ⊨Γ,Δ l∈⟦e₂⟧)
  go (l , (e₁ ∙ e₂)) rec {Γ,Δ} {τ′ = τ′} i≥m (Γ,Δ⊢e∶τ @ (Cat Γ,Δ⊢e₁∶τ₁ Δ++Γ,∙⊢e₂∶τ₂ _)) Γ,Δ⊢e′∶τ′ γ γ⊨Γ,Δ l∈⟦e⟧ =
    Product.zip ℕ._+_ (λ l₁∈⟦e₁⟧ l₂∈⟦e₂⟧ → record { l₁∈A = {!fⁿ≤fⁿ⁺ᵐ!} ; l₂∈B = {!!} ; eq = l∈⟦e⟧.eq }) l₁∈⟦e₁⟧′ l₂∈⟦e₂⟧′
    where
    module l∈⟦e⟧ = Concat l∈⟦e⟧
    l₁∈⟦e₁⟧′ = rec (l∈⟦e⟧.l₁ , e₁) {!!} i≥m Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e′∶τ′ γ γ⊨Γ,Δ l∈⟦e⟧.l₁∈A
    l₂∈⟦e₂⟧′ = rec (l∈⟦e⟧.l₂ , e₂) {!!} z≤n (congᶜ (shift≤-wkn₁-comm Γ,Δ z≤n i≥m τ′) Δ++Γ,∙⊢e₂∶τ₂) (shift≤ⱼ Γ,Δ⊢e′∶τ′ z≤n) γ (subst (PW.Pointwise _⊨_ γ) (≡.sym (shift≤-toVec Γ,Δ z≤n)) γ⊨Γ,Δ) l∈⟦e⟧.l₂∈B
  go (l , Var x) rec i≥m Γ,Δ⊢e∶τ Γ,Δ⊢e′∶τ′ γ γ⊨Γ,Δ l∈⟦e⟧ = {!!}
  go (l , μ e) rec {e′ = e′} {i = i} i≥m Γ,Δ⊢e∶τ Γ,Δ⊢e′∶τ′ γ γ⊨Γ,Δ (n , l∈⟦e⟧) =
    m , n , _≈ˡ_.f⁻¹ (⟦e⟧ᵐ≈⟦expand[e,m]⟧ e n (insert γ i (((λ X → ⟦ e′ ⟧ (X ∷ γ)) ^ m) (⟦ ⊥ ⟧ γ)))) (proj₂ recced)
    where
    l∈⟦expand⟧ = _≈ˡ_.f (⟦e⟧ᵐ≈⟦expand[e,m]⟧ e n (insert γ i (⟦ μ e′ ⟧ γ))) l∈⟦e⟧
    recced = rec (l , expand e n) (inj₂ (≡.refl , expand-smaller-rank Γ,Δ⊢e∶τ n)) i≥m {!!} Γ,Δ⊢e′∶τ′ γ γ⊨Γ,Δ l∈⟦expand⟧
    m = proj₁ recced
    l∈⟦expand⟧′ = proj₂ recced

l∈⟦e⟧⇒e⤇l : ∀ {e τ} → ∙,∙ ⊢ e ∶ τ → ∀ {l} → l ∈ ⟦ e ⟧ [] → e ⤇ l
l∈⟦e⟧⇒e⤇l {e} {τ} ∙,∙⊢e∶τ {l} l∈⟦e⟧ = All.wfRec <-wellFounded _ Pred go (l , e) ∙,∙⊢e∶τ l∈⟦e⟧
  where
  Pred : List C × Expression 0 → Set _
  Pred (l , e) = ∀ {τ} → ∙,∙ ⊢ e ∶ τ → l ∈ ⟦ e ⟧ [] → e ⤇ l

  e[μe/0]<μe : ∀ {e τ} l → ∙,∙ ⊢ μ e ∶ τ → (l , e [ μ e / F.zero ]) < (l , μ e)
  e[μe/0]<μe {e} l (Fix ∙,τ⊢e∶τ)= inj₂ (≡.refl , (begin-strict
    rank (e [ μ e / F.zero ]) ≡⟨ subst-preserves-rank z≤n ∙,τ⊢e∶τ ⟩
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
  go (l , e₁ ∨ e₂) rec (Vee ∙,∙⊢e₁∶τ₁ _ _) (inj₁ l∈⟦e₁⟧) =
    Veeˡ (rec (l , e₁) (inj₂ (≡.refl , e₁<ᵣₐₙₖe₁∨e₂ e₁ e₂)) ∙,∙⊢e₁∶τ₁ l∈⟦e₁⟧)
  go (l , e₁ ∨ e₂) rec (Vee _ ∙,∙⊢e₂∶τ₂ _) (inj₂ l∈⟦e₂⟧) =
    Veeʳ (rec (l , e₂) (inj₂ (≡.refl , e₂<ᵣₐₙₖe₁∨e₂ e₁ e₂)) ∙,∙⊢e₂∶τ₂ l∈⟦e₂⟧)

e⤇l⇒l∈⟦e⟧ : ∀ {e τ} → ∙,∙ ⊢ e ∶ τ → ∀ {l} → e ⤇ l → l ∈ ⟦ e ⟧ []
e⤇l⇒l∈⟦e⟧ {e} ∙,∙⊢e∶τ {l} e⤇l = All.wfRec <-wellFounded _ Pred go (l , e) ∙,∙⊢e∶τ e⤇l
  where
  Pred : List C × Expression 0 → Set _
  Pred (l , e) = ∀ {τ} → ∙,∙ ⊢ e ∶ τ → e ⤇ l → l ∈ ⟦ e ⟧ []

  go : ∀ l,e → WfRec _<_ Pred l,e → Pred l,e
  go (l , ε) rec ∙,∙⊢e∶τ Eps = Level.lift ≡.refl
  go (l , (Char _)) rec ∙,∙⊢e∶τ (Char c∼y) = Level.lift (c∼y ∷ [])
  go (l , (e₁ ∙ e₂)) rec (∙,∙⊢e₁∙e₂∶τ @ (Cat ∙,∙⊢e₁∶τ₁ ∙,∙⊢e₂∶τ₂ _)) (Cat {l₁ = l₁} {l₂ = l₂} e₁⤇l₁ e₂⤇l₂ eq) = record
    { l₁∈A = rec (l₁ , e₁) {!!} ∙,∙⊢e₁∶τ₁ e₁⤇l₁
    ; l₂∈B = rec (l₂ , e₂) {!!} ∙,∙⊢e₂∶τ₂ e₂⤇l₂
    ; eq = eq
    }
  go (l , (e₁ ∨ e₂)) rec ∙,∙⊢e∶τ (Veeˡ e₁⤇l) = inj₁ (rec {!!} {!!} {!!} e₁⤇l)
  go (l , (e₁ ∨ e₂)) rec ∙,∙⊢e∶τ (Veeʳ e₂⤇l) = inj₂ (rec {!!} {!!} {!!} e₂⤇l)
  go (l , (μ e)) rec ∙,∙⊢e∶τ (Fix e⤇l) = {!e!}

derivation-unique : ∀ {e τ} → ∙,∙ ⊢ e ∶ τ → ∀ {l} → l ∈ ⟦ e ⟧ [] → (e⤇l e⤇l′ : e ⤇ l) → e⤇l ≈ e⤇l′
derivation-unique {e} ∙,∙⊢e∶τ {l} l∈⟦e⟧ e⤇l e⤇l′ = All.wfRec <-wellFounded _ Pred {!!} (l , e) ∙,∙⊢e∶τ l∈⟦e⟧ e⤇l e⤇l′
  where
  Pred : List C × Expression 0 → Set _
  Pred (l , e) = ∀ {τ} → ∙,∙ ⊢ e ∶ τ → l ∈ ⟦ e ⟧ [] → (e⤇l e⤇l′ : e ⤇ l) → e⤇l ≈ e⤇l′

  go : ∀ l,e → WfRec _<_ Pred l,e → Pred l,e
  go (l , e) rec ∙,∙⊢e∶τ l∈⟦e⟧ Eps Eps = Eps
  go (l , e) rec ∙,∙⊢e∶τ l∈⟦e⟧ (Char c∼y) (Char c∼y′) = Char c∼y c∼y′
  go (l , e) rec ∙,∙⊢e∶τ l∈⟦e⟧ (Cat e₁⤇l₁ e₂⤇l₂ eq) (Cat e₁⤇l₁′ e₂⤇l₂′ eq′) = {!!}
  go (l , e₁ ∨ e₂) rec (Vee ∙,∙⊢e₁∶τ₁ _ _) (inj₁ l∈⟦e₁⟧) (Veeˡ e₁⤇l) (Veeˡ e₁⤇l′) =
    Veeˡ (rec (l , e₁) (inj₂ (≡.refl , e₁<ᵣₐₙₖe₁∨e₂ e₁ e₂)) ∙,∙⊢e₁∶τ₁ l∈⟦e₁⟧ e₁⤇l e₁⤇l′)
  go ([] , e₁ ∨ e₂) rec (Vee ∙,∙⊢e₁∶τ₁ ∙,∙⊢e₂∶τ₂ τ₁#τ₂) (inj₁ l∈⟦e⟧) (Veeˡ e₁⤇l) (Veeʳ e₂⤇l′) =
    ⊥-elim {!!}
  go (x ∷ l , e₁ ∨ e₂) rec (Vee ∙,∙⊢e₁∶τ₁ ∙,∙⊢e₂∶τ₂ τ₁#τ₂) (inj₁ l∈⟦e⟧) (Veeˡ e₁⤇l) (Veeʳ e₂⤇l′) =
    ⊥-elim {!!}
  go (l , e₁ ∨ e₂) rec (Vee ∙,∙⊢e₁∶τ₁ ∙,∙⊢e₂∶τ₂ τ₁#τ₂) (inj₂ l∈⟦e⟧) (Veeˡ e₁⤇l) _ = {!!}
  go (l , e₁ ∨ e₂) rec ∙,∙⊢e∶τ l∈⟦e⟧ (Veeʳ e₂⤇l) (Veeˡ e₁⤇l′) = {!!}
  go (l , e₁ ∨ e₂) rec ∙,∙⊢e∶τ l∈⟦e⟧ (Veeʳ e₂⤇l) (Veeʳ e₂⤇l′) = {!!}
  go (l , e) rec ∙,∙⊢e∶τ l∈⟦e⟧ (Fix e⤇l) e⤇l′ = {!!}
