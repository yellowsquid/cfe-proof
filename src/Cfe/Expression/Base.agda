{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (REL; Setoid)

module Cfe.Expression.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C)

open import Cfe.Language over renaming (_∙_ to _∙ˡ_; _≈_ to _≈ˡ_)
open import Data.Fin hiding (_+_; _<_)
open import Data.Nat hiding (_≟_; _⊔_)
open import Data.Vec
open import Function using (_on_)
open import Relation.Nullary using (yes; no)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Definition

infix 8 μ_
infix 7 _∙_
infix 6 _∨_

data Expression : ℕ → Set c where
  ⊥    : Expression n
  ε    : Expression n
  Char : (c : C) → Expression n
  _∨_  : Expression n → Expression n → Expression n
  _∙_  : Expression n → Expression n → Expression n
  Var  : (j : Fin n) → Expression n
  μ_   : Expression (suc n) → Expression n

------------------------------------------------------------------------
-- Semantics

infix 4 _≈_

⟦_⟧ : Expression n → Vec (Language _) n → Language _
⟦ ⊥ ⟧       _ = ∅
⟦ ε ⟧       _ = ｛ε｝ {ℓ}
⟦ Char x ⟧  _ = ｛ x ｝
⟦ e₁ ∨ e₂ ⟧ γ = ⟦ e₁ ⟧ γ ∪ ⟦ e₂ ⟧ γ
⟦ e₁ ∙ e₂ ⟧ γ = ⟦ e₁ ⟧ γ ∙ˡ ⟦ e₂ ⟧ γ
⟦ Var n ⟧   γ = lookup γ n
⟦ μ e ⟧     γ = ⋃ (λ X → ⟦ e ⟧ (X ∷ γ))

_≈_ : {n : ℕ} → Expression n → Expression n → Set _
e₁ ≈ e₂ = ∀ γ → ⟦ e₁ ⟧ γ ≈ˡ ⟦ e₂ ⟧ γ

------------------------------------------------------------------------
-- Syntax manipulation

infix 10 _[_/_]

wkn : Expression n → Fin (suc n) → Expression (suc n)
wkn ⊥         i = ⊥
wkn ε         i = ε
wkn (Char c)  i = Char c
wkn (e₁ ∨ e₂) i = wkn e₁ i ∨ wkn e₂ i
wkn (e₁ ∙ e₂) i = wkn e₁ i ∙ wkn e₂ i
wkn (Var j)   i = Var (punchIn i j)
wkn (μ e)     i = μ wkn e (suc i)

_[_/_] : Expression (suc n) → Expression n → Fin (suc n) → Expression n
⊥         [ e′ / i ] = ⊥
ε         [ e′ / i ] = ε
Char x    [ e′ / i ] = Char x
(e₁ ∨ e₂) [ e′ / i ] = e₁ [ e′ / i ] ∨ e₂ [ e′ / i ]
(e₁ ∙ e₂) [ e′ / i ] = e₁ [ e′ / i ] ∙ e₂ [ e′ / i ]
Var j     [ e′ / i ] with i ≟ j
...                     | yes i≡j = e′
...                     | no  i≢j = Var (punchOut i≢j)
(μ e)     [ e′ / i ] = μ e [ wkn e′ zero / suc i ]

------------------------------------------------------------------------
-- Syntax properties

infix 4 _<ᵣₐₙₖ_

rank : Expression n → ℕ
rank ⊥         = 0
rank ε         = 0
rank (Char _)  = 0
rank (e₁ ∨ e₂) = suc (rank e₁ + rank e₂)
rank (e₁ ∙ _)  = suc (rank e₁)
rank (Var _)   = 0
rank (μ e)     = suc (rank e)

_<ᵣₐₙₖ_ : REL (Expression m) (Expression n) _
e <ᵣₐₙₖ e′ = rank e < rank e′
