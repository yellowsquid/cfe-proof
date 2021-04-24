{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Judgement.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Context over renaming (wkn₁ to wkn₁ᶜ; wkn₂ to wkn₂ᶜ; shift to shiftᶜ)
open import Cfe.Fin
open import Cfe.Expression over
open import Cfe.Judgement.Base over
open import Cfe.Language over using (⊆-refl)
open import Cfe.Type over
  using (Type; τ⊥; _⊨_; ⊨-min; ⊨-fix; ｛ε｝⊨τε; ｛c｝⊨τ[c]; ⊛⇒∙-pres-⊨; #⇒∨-pres-⊨)
  renaming (_≈_ to _≈ᵗ_; ≈-refl to ≈ᵗ-refl)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc; toℕ; inject₁; punchIn; punchOut) renaming (_≤_ to _≤ᶠ_)
open import Data.Fin.Properties using (_≟_; toℕ-injective; toℕ-inject₁)
open import Data.Nat using (ℕ; suc; z≤n; _+_) renaming (_≤_ to _≤ⁿ_)
open import Data.Nat.Properties using (pred-mono; <⇒≤pred; <⇒≢; module ≤-Reasoning)
open import Data.Vec using (Vec; _∷_; lookup; insert; remove)
open import Data.Vec.Properties using (insert-punchIn; remove-punchOut)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as Pw using (Pointwise; _∷_)
open import Function using (_|>_; _∘_; _∘₂_; flip)
open import Relation.Binary.PropositionalEquality as ≡ hiding (subst₂)
open import Relation.Nullary

private
  variable
    n : ℕ
    ctx ctx₁ ctx₂ : Context n
    τ τ′ : Type ℓ ℓ

  punchIn< : ∀ {n i j} → toℕ i ≤ⁿ toℕ j → punchIn {n} i j ≡ suc j
  punchIn< {i = zero} {j} i≤j = refl
  punchIn< {i = suc i} {suc j} i≤j = cong suc (punchIn< (pred-mono i≤j))

wkn₁ : ∀ {e} → ctx ⊢ e ∶ τ → ∀ i τ′ → wkn₁ᶜ ctx i τ′ ⊢ wkn e (raise!> i) ∶ τ
wkn₁ Eps      i τ′ = Eps
wkn₁ (Char c) i τ′ = Char c
wkn₁ Bot      i τ′ = Bot
wkn₁ {ctx = Γ,Δ ⊐ g} (Var j) i τ′ =
  ≡.subst₂ (wkn₁ᶜ (Γ,Δ ⊐ g) i τ′ ⊢_∶_) (cong Var eqⁱ) eqᵗ (Var (punchIn> i j))
  where
  open ≡-Reasoning
  lookup′ = lookup (insert Γ,Δ (raise!> i) τ′)
  eqⁱ = toℕ-injective (begin
    toℕ (raise!> (punchIn> i j))         ≡⟨ toℕ-raise!> (punchIn> i j) ⟩
    toℕ> (punchIn> i j)                 ≡⟨ toℕ-punchIn> i j ⟩
    toℕ (punchIn (raise!> i) (raise!> j)) ∎)
  eqᵗ = begin
    lookup′ (raise!> (punchIn> i j))         ≡⟨ cong (lookup (insert Γ,Δ (raise!> i) τ′)) eqⁱ ⟩
    lookup′ (punchIn (raise!> i) (raise!> j)) ≡⟨ insert-punchIn Γ,Δ (raise!> i) τ′ (raise!> j) ⟩
    lookup Γ,Δ (raise!> j)                   ∎
wkn₁ {ctx = ctx} {τ} {μ e} (Fix ctx⊢e∶τ) i τ′ =
  Fix (subst
    (_⊢ wkn e (suc (raise!> i)) ∶ τ)
    (sym (wkn₁-wkn₂-comm ctx i zero τ′ τ))
    (wkn₁ ctx⊢e∶τ (inj i) τ′))
wkn₁ {ctx = ctx} {e = _ ∙ e₂} (Cat {τ₂ = τ₂} ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁⊛τ₂) i τ′ =
  Cat
    (wkn₁ ctx⊢e₁∶τ₁ i τ′)
    (≡.subst₂
      (_⊢_∶ τ₂)
      (sym (shift-wkn₁-comm ctx zero i τ′))
      (toℕ-cast> z≤n i |> raise!>-cong |> toℕ-injective |> cong (wkn e₂))
      (wkn₁ ctx⊢e₂∶τ₂ (cast> z≤n i) τ′))
    τ₁⊛τ₂
wkn₁ (Vee ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁#τ₂) i τ′ = Vee (wkn₁ ctx⊢e₁∶τ₁ i τ′) (wkn₁ ctx⊢e₂∶τ₂ i τ′) τ₁#τ₂

wkn₂ : ∀ {e} → ctx ⊢ e ∶ τ → ∀ i τ′ → wkn₂ᶜ ctx i τ′ ⊢ wkn e (inject!< i) ∶ τ
wkn₂ Eps      i τ′ = Eps
wkn₂ (Char c) i τ′ = Char c
wkn₂ Bot      i τ′ = Bot
wkn₂ {ctx = Γ,Δ ⊐ g} (Var j) i τ′ =
  ≡.subst₂ (wkn₂ᶜ (Γ,Δ ⊐ g) i τ′ ⊢_∶_) (cong Var eqⁱ) eqᵗ (Var (inj j))
  where
  lookup′ = lookup (insert Γ,Δ (inject!< i) τ′)
  eqⁱ = sym (punchIn< (begin
    toℕ (inject!< i)  ≡⟨ toℕ-inject!< i ⟩
    toℕ< i            ≤⟨ <⇒≤pred (toℕ<<i i) ⟩
    toℕ g             ≤⟨ toℕ>≥i j ⟩
    toℕ> j            ≡˘⟨ toℕ-raise!> j ⟩
    toℕ (raise!> j)    ∎))
    where open ≤-Reasoning
  eqᵗ = begin
    lookup′ (raise!> (inj j))                  ≡⟨ cong lookup′ eqⁱ ⟩
    lookup′ (punchIn (inject!< i) (raise!> j)) ≡⟨ insert-punchIn Γ,Δ (inject!< i) τ′ (raise!> j) ⟩
    lookup Γ,Δ (raise!> j)                     ∎
    where open ≡-Reasoning
wkn₂ {ctx = ctx} {τ} {μ e} (Fix ctx⊢e∶τ) i τ′ =
  Fix (subst
    (_⊢ wkn e (inject!< (suc i)) ∶ τ)
    (wkn₂-comm ctx i zero τ′ τ)
    (wkn₂ ctx⊢e∶τ (suc i) τ′))
wkn₂ {ctx = ctx} {e = _ ∙ e₂} (Cat {τ₂ = τ₂} ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁⊛τ₂) i τ′ =
  Cat
    (wkn₂ ctx⊢e₁∶τ₁ i τ′)
    (≡.subst₂
      (_⊢_∶ τ₂)
      (sym (shift-wkn₁-wkn₂-comm ctx i zero τ′))
      (cong (wkn e₂) (toℕ-injective (begin
        toℕ (raise!> (reflect! i zero)) ≡⟨ toℕ-raise!> (reflect! i zero) ⟩
        toℕ> (reflect! i zero)          ≡⟨ toℕ-reflect! i zero ⟩
        toℕ< i                          ≡˘⟨ toℕ-inject!< i ⟩
        toℕ (inject!< i)                ∎)))
      (wkn₁ ctx⊢e₂∶τ₂ (reflect! i zero) τ′))
    τ₁⊛τ₂
  where open ≡-Reasoning
wkn₂ (Vee ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁#τ₂) i τ′ = Vee (wkn₂ ctx⊢e₁∶τ₁ i τ′) (wkn₂ ctx⊢e₂∶τ₂ i τ′) τ₁#τ₂

shift : ∀ {e} → ctx ⊢ e ∶ τ → ∀ i → shiftᶜ ctx i ⊢ e ∶ τ
shift Eps      i = Eps
shift (Char c) i = Char c
shift Bot      i = Bot
shift {ctx = Γ,Δ ⊐ g} {τ} (Var j) i =
  ≡.subst₂
    (Γ,Δ ⊐ inject!< i ⊢_∶_)
    (toℕ-cast> i≤g j |> raise!>-cong |> toℕ-injective |> cong Var)
    (toℕ-cast> i≤g j |> raise!>-cong |> toℕ-injective |> cong (lookup Γ,Δ))
    (Var (cast> i≤g j))
  where
  i≤g : inject!< i ≤ᶠ g
  i≤g = begin
    toℕ (inject!< i) ≡⟨ toℕ-inject!< i ⟩
    toℕ< i           ≤⟨ <⇒≤pred (toℕ<<i i) ⟩
    toℕ g            ∎
    where open ≤-Reasoning
shift {ctx = ctx} {τ} {μ e} (Fix ctx⊢e∶τ) i =
  Fix (subst (_⊢ e ∶ τ) (shift-wkn₂-comm ctx i zero τ) (shift ctx⊢e∶τ (suc i)))
shift {ctx = ctx} {_} {_ ∙ e₂} (Cat {τ₂ = τ₂} ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁⊛τ₂) i =
  Cat
    (shift ctx⊢e₁∶τ₁ i)
    (subst (_⊢ e₂ ∶ τ₂) (sym (shift-trans ctx i zero)) ctx⊢e₂∶τ₂)
    τ₁⊛τ₂
shift (Vee ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁#τ₂) i = Vee (shift ctx⊢e₁∶τ₁ i) (shift ctx⊢e₂∶τ₂ i) τ₁#τ₂

subst₁ :
  ∀ {e} → ctx ⊢ e ∶ τ →
  ∀ i {e′} → remove₁ ctx i ⊢ e′ ∶ lookup (Γ,Δ ctx) (raise!> i) →
  remove₁ ctx i ⊢ e [ e′ / raise!> i ] ∶ τ
subst₁ Eps      i ctx⊢e′∶τ′ = Eps
subst₁ (Char c) i ctx⊢e′∶τ′ = Char c
subst₁ Bot      i ctx⊢e′∶τ′ = Bot
subst₁ {ctx = Γ,Δ ⊐ g} (Var j) i {e′} ctx⊢e′∶τ′ with raise!> i ≟ raise!> j
... | yes i≡j = subst (remove₁ (Γ,Δ ⊐ g) i ⊢ e′ ∶_) (cong (lookup Γ,Δ) i≡j) ctx⊢e′∶τ′
... | no i≢j  = ≡.subst₂ (remove₁ (Γ,Δ ⊐ g) i ⊢_∶_ ) (cong Var eqⁱ) eqᵗ (Var (punchOut> i≢j))
  where
  open ≡-Reasoning
  lookup′ = lookup (remove Γ,Δ (raise!> i))
  eqⁱ = toℕ-injective (begin
    toℕ (raise!> (punchOut> i≢j)) ≡⟨ toℕ-raise!> (punchOut> i≢j) ⟩
    toℕ> (punchOut> i≢j)          ≡⟨ toℕ-punchOut> i≢j ⟩
    toℕ (punchOut i≢j)            ∎)

  eqᵗ = begin
    lookup′ (raise!> (punchOut> i≢j)) ≡⟨ cong lookup′ eqⁱ ⟩
    lookup′ (punchOut i≢j)            ≡⟨ remove-punchOut Γ,Δ i≢j ⟩
    lookup Γ,Δ (raise!> j)            ∎
subst₁ {ctx = ctx} {τ} {μ e} (Fix ctx⊢e∶τ) i {e′} ctx⊢e′∶τ′ =
  Fix (subst
    (_⊢ e [ wkn e′ zero / suc (raise!> i) ] ∶ τ)
    (remove₁-wkn₂-comm ctx i zero τ)
    (subst₁
      ctx⊢e∶τ
      (inj i)
      (subst
        (_⊢ wkn e′ zero ∶ lookup (Γ,Δ ctx) (raise!> i))
        (sym (remove₁-wkn₂-comm ctx i zero τ))
        (wkn₂ ctx⊢e′∶τ′ zero τ))))
subst₁ {ctx = ctx} {_} {_ ∙ e₂} (Cat {τ₂ = τ₂} ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁⊛τ₂) i {e′} ctx⊢e′∶τ′ =
  Cat
    (subst₁ ctx⊢e₁∶τ₁ i ctx⊢e′∶τ′)
    (≡.subst₂
      (_⊢_∶ τ₂ )
      (remove₁-shift-comm ctx zero i)
      (toℕ-cast> z≤n i |> raise!>-cong |> toℕ-injective |> cong (e₂ [ e′ /_]))
      (subst₁
        ctx⊢e₂∶τ₂
        (cast> z≤n i)
        (≡.subst₂ (_⊢ e′ ∶_)
          (sym (remove₁-shift-comm ctx zero i))
          (toℕ-cast> z≤n i |> raise!>-cong |> toℕ-injective |> cong (lookup (Γ,Δ ctx)) |> sym)
          (shift ctx⊢e′∶τ′ zero))))
    τ₁⊛τ₂
subst₁ (Vee ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁#τ₂) i ctx⊢e′∶τ′ =
  Vee (subst₁ ctx⊢e₁∶τ₁ i ctx⊢e′∶τ′) (subst₁ ctx⊢e₂∶τ₂ i ctx⊢e′∶τ′) τ₁#τ₂

subst₂ :
  ∀ {e} → ctx ⊢ e ∶ τ →
  ∀ i {e′} → shiftᶜ (remove₂ ctx i) zero ⊢ e′ ∶ lookup (Γ,Δ ctx) (inject!< i) →
  remove₂ ctx i ⊢ e [ e′ / inject!< i ] ∶ τ
subst₂ Eps      i ctx⊢e′∶τ′ = Eps
subst₂ (Char c) i ctx⊢e′∶τ′ = Char c
subst₂ Bot      i ctx⊢e′∶τ′ = Bot
subst₂ {ctx = Γ,Δ ⊐ suc g} (Var (inj j)) i ctx⊢e′∶τ′ with inject!< i ≟ raise!> (inj j)
... | yes i≡j = ⊥-elim (flip <⇒≢ (cong toℕ i≡j) (begin-strict
  toℕ (inject!< i) ≡⟨ toℕ-inject!< i ⟩
  toℕ< i           <⟨ toℕ<<i i ⟩
  toℕ (suc g)      ≤⟨ toℕ>≥i (inj j) ⟩
  toℕ> (inj j)     ≡˘⟨ toℕ-raise!> (inj j) ⟩
  toℕ (raise!> (inj j))  ∎))
  where open ≤-Reasoning
... | no i≢j  = ≡.subst₂ (remove₂ (Γ,Δ ⊐ suc g) i ⊢_∶_ ) (cong Var eqⁱ) eqᵗ (Var j)
  where
  open ≡-Reasoning
  lookup′ = lookup (remove Γ,Δ (inject!< i))
  eqⁱ = trans (inj-punchOut i≢j) (sym (toℕ-raise!> j)) |> toℕ-injective |> sym
  eqᵗ = begin
    lookup′ (raise!> j)          ≡⟨ cong lookup′ eqⁱ ⟩
    lookup′ (punchOut i≢j)       ≡⟨ remove-punchOut Γ,Δ i≢j ⟩
    lookup Γ,Δ (raise!> (inj j)) ∎
subst₂ {n} {ctx = ctx @ (Γ,Δ ⊐ suc g)} {τ} {μ e} (Fix ctx⊢e∶τ) i {e′} ctx⊢e′∶τ′ =
  Fix (subst
    (_⊢ e [ wkn e′ zero / suc (inject!< i) ] ∶ τ)
    (remove₂-wkn₂-comm ctx i zero τ)
    (subst₂
      ctx⊢e∶τ
      (suc i)
      (subst
        (_⊢ wkn e′ zero ∶ lookup Γ,Δ (inject!< i))
        (begin
          wkn₁ᶜ (shiftᶜ (remove₂ ctx i) zero) zero τ       ≡˘⟨ shift-wkn₁-wkn₂-comm (remove₂ ctx i) zero zero τ ⟩
          shiftᶜ (wkn₂ᶜ (remove₂ ctx i) zero τ) zero       ≡˘⟨ shift-cong-≡ zero zero (remove₂-wkn₂-comm ctx i zero τ) ⟩
          shiftᶜ (remove₂ (wkn₂ᶜ ctx zero τ) (suc i)) zero ∎)
        (wkn₁ ctx⊢e′∶τ′ zero τ))))
  where open ≡-Reasoning
subst₂ {ctx = Γ,Δ ⊐ suc g} {_} {_ ∙ e₂} (Cat {τ₂ = τ₂} ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁⊛τ₂) i {e′} ctx⊢e′∶τ′ =
  Cat
    (subst₂ ctx⊢e₁∶τ₁ i ctx⊢e′∶τ′)
    (≡.subst₂
      (_⊢_∶ τ₂)
      (remove₁-remove₂-shift-comm (Γ,Δ ⊐ suc g) i zero)
      (eqⁱ |> cong (e₂ [ e′ /_]))
      (subst₁
        ctx⊢e₂∶τ₂
        (cast> z≤n (reflect i zero))
        (≡.subst₂
          (_⊢ e′ ∶_)
          (sym (remove₁-remove₂-shift-comm (Γ,Δ ⊐ suc g) i zero))
          (eqⁱ |> cong (lookup Γ,Δ) |> sym)
          (shift ctx⊢e′∶τ′ zero))))
    τ₁⊛τ₂
  where
  open ≡-Reasoning
  eqⁱ = toℕ-injective (begin
    toℕ (raise!> (cast> _ (reflect i zero))) ≡⟨ toℕ-raise!> (cast> _ (reflect i zero)) ⟩
    toℕ> (cast> _ (reflect i zero))          ≡⟨ toℕ-cast> z≤n (reflect i zero) ⟩
    toℕ> (reflect i zero)                    ≡⟨ toℕ-reflect i zero ⟩
    toℕ< i                                   ≡˘⟨ toℕ-inject!< i ⟩
    toℕ (inject!< i)                         ∎)
subst₂ (Vee ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁#τ₂) i ctx⊢e′∶τ′ =
  Vee (subst₂ ctx⊢e₁∶τ₁ i ctx⊢e′∶τ′) (subst₂ ctx⊢e₂∶τ₂ i ctx⊢e′∶τ′) τ₁#τ₂

soundness : ∀ {e} → ctx ⊢ e ∶ τ → ∀ γ → Pointwise _⊨_ γ (Γ,Δ ctx) → ⟦ e ⟧ γ ⊨ τ
soundness           Eps                             γ γ⊨Γ,Δ = ｛ε｝⊨τε
soundness           (Char c)                        γ γ⊨Γ,Δ = ｛c｝⊨τ[c] c
soundness           Bot                             γ γ⊨Γ,Δ = ⊨-min τ⊥
soundness           (Var j)                         γ γ⊨Γ,Δ = Pw.lookup γ⊨Γ,Δ (raise!> j)
soundness {e = μ e} (Fix ctx⊢e∶τ)                   γ γ⊨Γ,Δ =
  ⊨-fix
    (λ X⊆Y → ⟦⟧-mono-env e (X⊆Y ∷ Pw.refl ⊆-refl))
    (λ {A} A⊨τ → soundness ctx⊢e∶τ (A ∷ γ) (A⊨τ ∷ γ⊨Γ,Δ))
soundness           (Cat ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁⊛τ₂) γ γ⊨Γ,Δ =
  ⊛⇒∙-pres-⊨ τ₁⊛τ₂ (soundness ctx⊢e₁∶τ₁ γ γ⊨Γ,Δ) (soundness ctx⊢e₂∶τ₂ γ γ⊨Γ,Δ)
soundness           (Vee ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ τ₁#τ₂) γ γ⊨Γ,Δ =
  #⇒∨-pres-⊨ τ₁#τ₂ (soundness ctx⊢e₁∶τ₁ γ γ⊨Γ,Δ) (soundness ctx⊢e₂∶τ₂ γ γ⊨Γ,Δ)

subst₂-pres-rank :
  ∀ {e} → ctx ⊢ e ∶ τ →
  ∀ i {e′} → shiftᶜ (remove₂ ctx i) zero ⊢ e′ ∶ lookup (Γ,Δ ctx) (inject!< i) →
  rank (e [ e′ / inject!< i ]) ≡ rank e
subst₂-pres-rank Eps      i ctx⊢e′∶τ′ = refl
subst₂-pres-rank (Char c) i ctx⊢e′∶τ′ = refl
subst₂-pres-rank Bot      i ctx⊢e′∶τ′ = refl
subst₂-pres-rank {ctx = _ ⊐ g} (Var j)  i ctx⊢e′∶τ′ with inject!< i ≟ raise!> j
... | yes i≡j = ⊥-elim (flip <⇒≢ (cong toℕ i≡j) (begin-strict
  toℕ (inject!< i) ≡⟨ toℕ-inject!< i ⟩
  toℕ< i           <⟨ toℕ<<i i ⟩
  toℕ g            ≤⟨ toℕ>≥i j ⟩
  toℕ> j           ≡˘⟨ toℕ-raise!> j ⟩
  toℕ (raise!> j)  ∎))
  where open ≤-Reasoning
... | no i≢j  = refl
subst₂-pres-rank {ctx = ctx @ (Γ,Δ ⊐ suc g)} {τ} (Fix ctx⊢e∶τ) i {e′} ctx⊢e′∶τ′ =
  cong suc
    (subst₂-pres-rank ctx⊢e∶τ (suc i)
      (subst
        (_⊢ wkn e′ zero ∶ lookup Γ,Δ (inject!< i))
        (begin
          wkn₁ᶜ (shiftᶜ (remove₂ ctx i) zero) zero τ       ≡˘⟨ shift-wkn₁-wkn₂-comm (remove₂ ctx i) zero zero τ ⟩
          shiftᶜ (wkn₂ᶜ (remove₂ ctx i) zero τ) zero       ≡˘⟨ shift-cong-≡ zero zero (remove₂-wkn₂-comm ctx i zero τ) ⟩
          shiftᶜ (remove₂ (wkn₂ᶜ ctx zero τ) (suc i)) zero ∎)
        (wkn₁ ctx⊢e′∶τ′ zero τ)))
  where open ≡-Reasoning
subst₂-pres-rank (Cat ctx⊢e₁∶τ₁ _ _) i ctx⊢e′∶τ′ = cong suc (subst₂-pres-rank ctx⊢e₁∶τ₁ i ctx⊢e′∶τ′)
subst₂-pres-rank (Vee ctx⊢e₁∶τ₁ ctx⊢e₂∶τ₂ _) i ctx⊢e′∶τ′ =
  cong₂
    (ℕ.suc ∘₂ _+_)
    (subst₂-pres-rank ctx⊢e₁∶τ₁ i ctx⊢e′∶τ′)
    (subst₂-pres-rank ctx⊢e₂∶τ₂ i ctx⊢e′∶τ′)
