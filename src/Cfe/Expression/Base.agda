{-# OPTIONS --without-K --safe #-}

open import Function
open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡

module Cfe.Expression.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over renaming (Carrier to C)

open import Cfe.Language over as 𝕃
open import Cfe.Language.Construct.Concatenate over renaming (_∙_ to _∙ₗ_)
open import Cfe.Language.Construct.Single over
open import Cfe.Language.Construct.Union over
open import Cfe.Language.Indexed.Construct.Iterate over
open import Data.Fin as F hiding (_≤_; cast)
open import Data.Nat as ℕ hiding (_≤_; _⊔_)
open import Data.Product
open import Data.Vec
open import Level renaming (suc to lsuc) hiding (Lift)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

infix 10 _[_/_]
infix 7 _∙_
infix 6 _∨_
infix 4 _≋_
infix 4 _<ᵣₐₙₖ_

data Expression : ℕ → Set c where
  ⊥ : ∀ {n} → Expression n
  ε : ∀ {n} → Expression n
  Char : ∀ {n} → C → Expression n
  _∨_ : ∀ {n} → Expression n → Expression n → Expression n
  _∙_ : ∀ {n} → Expression n → Expression n → Expression n
  Var : ∀ {n} → Fin n → Expression n
  μ : ∀ {n} → Expression (suc n) → Expression n

cast : ∀ {m n} → .(_ : m ≡ n) → Expression m → Expression n
cast eq ⊥ = ⊥
cast eq ε = ε
cast eq (Char x) = Char x
cast eq (e₁ ∨ e₂) = cast eq e₁ ∨ cast eq e₂
cast eq (e₁ ∙ e₂) = cast eq e₁ ∙ cast eq e₂
cast eq (Var i) = Var (F.cast eq i)
cast eq (μ e) = μ (cast (cong suc eq) e)

wkn : ∀ {n} → Expression n → Fin (suc n) → Expression (suc n)
wkn ⊥ i = ⊥
wkn ε i = ε
wkn (Char x) i = Char x
wkn (e₁ ∨ e₂) i = wkn e₁ i ∨ wkn e₂ i
wkn (e₁ ∙ e₂) i = wkn e₁ i ∙ wkn e₂ i
wkn (Var x) i = Var (punchIn i x)
wkn (μ e) i = μ (wkn e (suc i))

_[_/_] : ∀ {n} → Expression (suc n) → Expression n → Fin (suc n) → Expression n
⊥ [ e′ / i ] = ⊥
ε [ e′ / i ] = ε
Char x [ e′ / i ] = Char x
(e₁ ∨ e₂) [ e′ / i ] = e₁ [ e′ / i ] ∨ e₂ [ e′ / i ]
(e₁ ∙ e₂) [ e′ / i ] = e₁ [ e′ / i ] ∙ e₂ [ e′ / i ]
Var j [ e′ / i ] with i F.≟ j
... | yes i≡j = e′
... | no i≢j = Var (punchOut i≢j)
μ e [ e′ / i ] = μ (e [ wkn e′ F.zero / suc i ])

rotate : ∀ {n} → Expression n → (i j : Fin n) → .(_ : i F.≤ j) → Expression n
rotate ⊥ _ _ _ = ⊥
rotate ε _ _ _ = ε
rotate (Char x) _ _ _ = Char x
rotate (e₁ ∨ e₂) i j i≤j = rotate e₁ i j i≤j ∨ rotate e₂ i j i≤j
rotate (e₁ ∙ e₂) i j i≤j = rotate e₁ i j i≤j ∙ rotate e₂ i j i≤j
rotate {suc n} (Var k) i j _ with i F.≟ k
... | yes i≡k = Var j
... | no i≢k = Var (punchIn j (punchOut i≢k))
rotate (μ e) i j i≤j = μ (rotate e (suc i) (suc j) (s≤s i≤j))

⟦_⟧ : ∀ {n : ℕ} → Expression n → Vec (Language (c ⊔ ℓ)) n → Language (c ⊔ ℓ)
⟦ ⊥ ⟧ _ = Lift (c ⊔ ℓ) ∅
⟦ ε ⟧ _ = Lift ℓ ｛ε｝
⟦ Char x ⟧ _ = Lift ℓ ｛ x ｝
⟦ e₁ ∨ e₂ ⟧ γ = ⟦ e₁ ⟧ γ ∪ ⟦ e₂ ⟧ γ
⟦ e₁ ∙ e₂ ⟧ γ = ⟦ e₁ ⟧ γ ∙ₗ ⟦ e₂ ⟧ γ
⟦ Var n ⟧ γ = lookup γ n
⟦ μ e ⟧ γ = ⋃ (λ X → ⟦ e ⟧ (X ∷ γ))

_≋_ : {n : ℕ} → Expression n → Expression n → Set (lsuc (c ⊔ ℓ))
e₁ ≋ e₂ = ∀ γ → ⟦ e₁ ⟧ γ 𝕃.≈ ⟦ e₂ ⟧ γ

rank : {n : ℕ} → Expression n → ℕ
rank ⊥ = 0
rank ε = 0
rank (Char _) = 0
rank (e₁ ∨ e₂) = suc (rank e₁ ℕ.+ rank e₂)
rank (e₁ ∙ _) = suc (rank e₁)
rank (Var _) = 0
rank (μ e) = suc (rank e)

_<ᵣₐₙₖ_ : ∀ {m n} → REL (Expression m) (Expression n) _
e <ᵣₐₙₖ e′ = rank e ℕ.< rank e′

expand : {n : ℕ} → Expression (suc n) → ℕ → Expression n
expand e ℕ.zero = ⊥
expand e (suc m) = e [ expand e m / F.zero ]
