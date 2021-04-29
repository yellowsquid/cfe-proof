{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Expression.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C; _≈_ to _∼_)

open import Algebra
open import Cfe.Expression.Base over
open import Cfe.Language over
  hiding
    ( ≈-isPartialEquivalence; partialSetoid
    ; ∙-isMagma; ∙-isSemigroup; ∙-isMonoid; ∙-magma; ∙-semigroup; ∙-monoid
    )
  renaming
  ( _≈_ to _≈ˡ_
  ; ≈-refl to ≈ˡ-refl
  ; ≈-sym to ≈ˡ-sym
  ; ≈-trans to ≈ˡ-trans
  ; ≈-isEquivalence to ≈ˡ-isEquivalence
  ; setoid to setoidˡ
  ; _∙_ to _∙ˡ_
  ; ∙-cong to ∙ˡ-cong
  ; ∙-assoc to ∙ˡ-assoc
  ; ∙-identityˡ to ∙ˡ-identityˡ
  ; ∙-identityʳ to ∙ˡ-identityʳ
  ; ∙-identity to ∙ˡ-identity
  ; ∙-zeroˡ to ∙ˡ-zeroˡ
  ; ∙-zeroʳ to ∙ˡ-zeroʳ
  ; ∙-zero to ∙ˡ-zero
  )
open import Cfe.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise-insert)
open import Data.Empty using (⊥-elim)
open import Data.Fin hiding (_+_; _≤_; _<_)
open import Data.Fin.Properties using (punchIn-punchOut)
open import Data.List using (List; length; _++_)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Binary.Equality.Setoid over using (_≋_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise-length)
open import Data.Nat hiding (_≟_; _⊔_; _^_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product
open import Data.Product.Relation.Binary.Lex.Strict using (×-wellFounded)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Vec hiding (length; map; _++_)
open import Data.Vec.Properties
open import Data.Vec.Relation.Binary.Pointwise.Inductive as Pw
  hiding (refl; sym; trans; setoid; lookup; map)
open import Function using (_∘_; _|>_; id)
open import Induction.WellFounded using (WellFounded)
open import Level using (_⊔_)
open import Relation.Binary.Construct.On using () renaming (wellFounded to on-wellFounded)
open import Relation.Binary.PropositionalEquality hiding (setoid)
open import Relation.Nullary
open import Relation.Nullary.Decidable using (fromWitness)

private
  variable
    k m n : ℕ

  ≈ˡ-reflexive = IsEquivalence.reflexive (≈ˡ-isEquivalence {c ⊔ ℓ})

------------------------------------------------------------------------
-- Properties of ⟦_⟧
------------------------------------------------------------------------
-- Algebraic properties of ⟦_⟧

⟦⟧-mono-env : ∀ (e : Expression n) {γ γ′} → Pointwise _⊆_ γ γ′ → ⟦ e ⟧ γ ⊆ ⟦ e ⟧ γ′
⟦⟧-mono-env ⊥         mono = ⊆-refl
⟦⟧-mono-env ε         mono = ⊆-refl
⟦⟧-mono-env (Char _)  mono = ⊆-refl
⟦⟧-mono-env (e₁ ∨ e₂) mono = ∪-mono (⟦⟧-mono-env e₁ mono) (⟦⟧-mono-env e₂ mono)
⟦⟧-mono-env (e₁ ∙ e₂) mono = ∙-mono (⟦⟧-mono-env e₁ mono) (⟦⟧-mono-env e₂ mono)
⟦⟧-mono-env (Var j)   mono = Pw.lookup mono j
⟦⟧-mono-env (μ e)     mono = ⋃-mono λ A⊆B → ⟦⟧-mono-env e (A⊆B ∷ mono)

⟦⟧-cong-env : ∀ (e : Expression n) {γ γ′} → Pointwise _≈ˡ_ γ γ′ → ⟦ e ⟧ γ ≈ˡ ⟦ e ⟧ γ′
⟦⟧-cong-env ⊥         cong = ≈ˡ-refl
⟦⟧-cong-env ε         cong = ≈ˡ-refl
⟦⟧-cong-env (Char _)  cong = ≈ˡ-refl
⟦⟧-cong-env (e₁ ∨ e₂) cong = ∪-cong (⟦⟧-cong-env e₁ cong) (⟦⟧-cong-env e₂ cong)
⟦⟧-cong-env (e₁ ∙ e₂) cong = ∙ˡ-cong (⟦⟧-cong-env e₁ cong) (⟦⟧-cong-env e₂ cong)
⟦⟧-cong-env (Var j)   cong = Pw.lookup cong j
⟦⟧-cong-env (μ e)     cong = ⋃-cong λ A≈B → ⟦⟧-cong-env e (A≈B ∷ cong)

------------------------------------------------------------------------
-- Properties of _≈_
------------------------------------------------------------------------
-- Relational properties

≈-refl : Reflexive (_≈_ {n})
≈-refl _ = ≈ˡ-refl

≈-sym : Symmetric (_≈_ {n})
≈-sym e≈e′ γ = ≈ˡ-sym (e≈e′ γ)

≈-trans : Transitive (_≈_ {n})
≈-trans e≈e′ e′≈e′′ γ = ≈ˡ-trans (e≈e′ γ) (e′≈e′′ γ)

------------------------------------------------------------------------
-- Structures

≈-isPartialEquivalence : IsPartialEquivalence (_≈_ {n})
≈-isPartialEquivalence {n} = record
  { sym   = λ {e} {e′} → ≈-sym {n} {e} {e′}
  ; trans = λ {e} {e′} {e′′} → ≈-trans {n} {e} {e′} {e′′}
  }

≈-isEquivalence : IsEquivalence (_≈_ {n})
≈-isEquivalence {n} = record
  { refl  = λ {e} → ≈-refl {n} {e}
  ; sym   = λ {e} {e′} → ≈-sym {n} {e} {e′}
  ; trans = λ {e} {e′} {e′′} → ≈-trans {n} {e} {e′} {e′′}
  }

------------------------------------------------------------------------
-- Bundles

partialSetoid : ∀ {n} → PartialSetoid _ _
partialSetoid {n} = record { isPartialEquivalence = ≈-isPartialEquivalence {n} }

setoid : ∀ {n} → Setoid _ _
setoid {n} = record { isEquivalence = ≈-isEquivalence {n} }

------------------------------------------------------------------------
-- Properties of _<ᵣₐₙₖ_
------------------------------------------------------------------------
-- Definitions

infix 4 _<ₗₑₓ_
infix 4 _<ₕₑₜ_

_<ₗₑₓ_ : REL (List C × Expression m) (List C × Expression n) _
(w , e) <ₗₑₓ (w′ , e′) = length w < length w′ ⊎ length w ≡ length w′ × e <ᵣₐₙₖ e′

_<ₕₑₜ_ : Rel (List C × ∃[ m ] Expression m) _
(w , _ , e) <ₕₑₜ (w′ , _ , e′) = (w , e) <ₗₑₓ (w′ , e′)

------------------------------------------------------------------------
-- Relational properties

<ᵣₐₙₖ-trans : Trans (_<ᵣₐₙₖ_ {k}) (_<ᵣₐₙₖ_ {m} {n}) _<ᵣₐₙₖ_
<ᵣₐₙₖ-trans = <-trans

<ᵣₐₙₖ-asym : Asymmetric (_<ᵣₐₙₖ_ {n})
<ᵣₐₙₖ-asym = <-asym

<ₗₑₓ-trans : Trans (_<ₗₑₓ_ {k}) (_<ₗₑₓ_ {m} {n}) _<ₗₑₓ_
<ₗₑₓ-trans (inj₁ ∣w₁∣<∣w₂∣)           (inj₁ ∣w₂∣<∣w₃∣)           =
  inj₁ (<-trans ∣w₁∣<∣w₂∣ ∣w₂∣<∣w₃∣)
<ₗₑₓ-trans (inj₁ ∣w₁∣<∣w₂∣)           (inj₂ (∣w₂∣≡∣w₃∣ , _))     =
  inj₁ (<-transˡ ∣w₁∣<∣w₂∣ (≤-reflexive ∣w₂∣≡∣w₃∣))
<ₗₑₓ-trans (inj₂ (∣w₁∣≡∣w₂∣ , _))     (inj₁ ∣w₂∣<∣w₃∣)           =
  inj₁ (<-transʳ (≤-reflexive ∣w₁∣≡∣w₂∣) ∣w₂∣<∣w₃∣)
<ₗₑₓ-trans (inj₂ (∣w₁∣≡∣w₂∣ , r₁<r₂)) (inj₂ (∣w₂∣≡∣w₃∣ , r₂<r₃)) =
  inj₂ (trans ∣w₁∣≡∣w₂∣ ∣w₂∣≡∣w₃∣ , <ᵣₐₙₖ-trans r₁<r₂ r₂<r₃)

<ₗₑₓ-asym : Asymmetric (_<ₗₑₓ_ {n})
<ₗₑₓ-asym (inj₁ ∣w₁∣<∣w₂∣)       (inj₁ ∣w₂∣<∣w₁|)       = <-asym ∣w₁∣<∣w₂∣ ∣w₂∣<∣w₁|
<ₗₑₓ-asym (inj₁ ∣w₁∣<∣w₂∣)       (inj₂ (∣w₂∣≡∣w₁∣ , _)) = <-irrefl (sym ∣w₂∣≡∣w₁∣) ∣w₁∣<∣w₂∣
<ₗₑₓ-asym (inj₂ (∣w₁∣≡∣w₂∣ , _)) (inj₁ ∣w₂∣<∣w₁|)       = <-irrefl (sym ∣w₁∣≡∣w₂∣) ∣w₂∣<∣w₁|
<ₗₑₓ-asym (inj₂ (_ , r₁<r₂))      (inj₂ (_ , r₂<r₁))    = <ᵣₐₙₖ-asym r₁<r₂ r₂<r₁

------------------------------------------------------------------------
-- Induction properties

<ᵣₐₙₖ-wellFounded : WellFounded (_<ᵣₐₙₖ_ {n})
<ᵣₐₙₖ-wellFounded = on-wellFounded rank <-wellFounded

<ₗₑₓ-wellFounded : WellFounded (_<ₗₑₓ_ {n})
<ₗₑₓ-wellFounded = on-wellFounded (map₁ length) (×-wellFounded <-wellFounded <ᵣₐₙₖ-wellFounded)

<ₕₑₜ-wellFounded : WellFounded _<ₕₑₜ_
<ₕₑₜ-wellFounded =
  on-wellFounded (map length (rank ∘ proj₂)) (×-wellFounded <-wellFounded <-wellFounded)

------------------------------------------------------------------------
-- Other properties

rank-∨ˡ : ∀ (e₁ e₂ : Expression n) → e₁ <ᵣₐₙₖ e₁ ∨ e₂
rank-∨ˡ e₁ e₂ = begin-strict
  rank e₁           ≤⟨ m≤m+n (rank e₁) (rank e₂) ⟩
  rank e₁ + rank e₂ <⟨ n<1+n (rank e₁ + rank e₂) ⟩
  rank (e₁ ∨ e₂)    ∎
  where open ≤-Reasoning

rank-∨ʳ : ∀ (e₁ e₂ : Expression n) → e₂ <ᵣₐₙₖ e₁ ∨ e₂
rank-∨ʳ e₁ e₂ = begin-strict
  rank e₂           ≤⟨ m≤n+m (rank e₂) (rank e₁) ⟩
  rank e₁ + rank e₂ <⟨ n<1+n (rank e₁ + rank e₂) ⟩
  rank (e₁ ∨ e₂)    ∎
  where open ≤-Reasoning

rank-∙ˡ : ∀ (e₁ e₂ : Expression n) → e₁ <ᵣₐₙₖ e₁ ∙ e₂
rank-∙ˡ e₁ _ = n<1+n (rank e₁)

lex-∙ˡ : ∀ (e₁ e₂ : Expression n) → ∀ w₁ {w₂ w} → w₁ ++ w₂ ≋ w → (w₁ , e₁) <ₗₑₓ (w , e₁ ∙ e₂)
lex-∙ˡ e₁ e₂ w₁ {w₂} {w} eq with m≤n⇒m<n∨m≡n ∣w₁∣≤∣w∣
  where
  open ≤-Reasoning
  ∣w₁∣≤∣w∣ : length w₁ ≤ length w
  ∣w₁∣≤∣w∣ = begin
    length w₁             ≤⟨ m≤m+n (length w₁) (length w₂) ⟩
    length w₁ + length w₂ ≡˘⟨ length-++ w₁ ⟩
    length (w₁ ++ w₂)     ≡⟨ Pointwise-length eq ⟩
    length w              ∎
... | inj₁ ∣w₁∣<∣w∣ = inj₁ ∣w₁∣<∣w∣
... | inj₂ ∣w₁∣≡∣w∣ = inj₂ (∣w₁∣≡∣w∣ , rank-∙ˡ e₁ e₂)

lex-∙ʳ :
  ∀ (e₁ e₂ : Expression n) γ → ¬ Null (⟦ e₁ ⟧ γ) →
  ∀ {w₁ w₂ w} → w₁ ∈ ⟦ e₁ ⟧ γ → w₁ ++ w₂ ≋ w →
  (w₂ , e₂) <ₗₑₓ (w , e₁ ∙ e₂)
lex-∙ʳ e₁ _ γ ε∉⟦e₁⟧ {w₁} {w₂} {w} w₁∈⟦e₁⟧ eq with m≤n⇒m<n∨m≡n ∣w₂∣≤∣w∣
  where
  open ≤-Reasoning
  ∣w₂∣≤∣w∣ : length w₂ ≤ length w
  ∣w₂∣≤∣w∣ = begin
    length w₂             ≤⟨ m≤n+m (length w₂) (length w₁) ⟩
    length w₁ + length w₂ ≡˘⟨ length-++ w₁ ⟩
    length (w₁ ++ w₂)     ≡⟨ Pointwise-length eq ⟩
    length w              ∎
... | inj₁ ∣w₂∣<∣w∣ = inj₁ ∣w₂∣<∣w∣
... | inj₂ ∣w₂∣≡∣w∣ = ⊥-elim (ε∉⟦e₁⟧ (∣w∣≡0+w∈A⇒ε∈A {A = ⟦ e₁ ⟧ γ} ∣w₁∣≡0 w₁∈⟦e₁⟧))
  where
    open ≤-Reasoning
    ∣w₁∣≡0 : length w₁ ≡ 0
    ∣w₁∣≡0 = +-cancelʳ-≡ (length w₁) 0 (begin-equality
      length w₁ + length w₂ ≡˘⟨ length-++ w₁ ⟩
      length (w₁ ++ w₂)     ≡⟨ Pointwise-length eq ⟩
      length w              ≡˘⟨ ∣w₂∣≡∣w∣ ⟩
      length w₂             ∎)

rank-μ : ∀ (e : Expression (suc n)) → e <ᵣₐₙₖ μ e
rank-μ e = n<1+n (rank e)

------------------------------------------------------------------------
-- Properties of Char
------------------------------------------------------------------------
-- Functional properties

Char-cong : ∀ {c c′} → c ∼ c′ → Char {n} c ≈ Char c′
Char-cong c∼c′ _ = ｛｝-cong c∼c′

Char-inj : ∀ {c c′} → Char {n} c ≈ Char c′ → c ∼ c′
Char-inj c≈c′ = ｛｝-inj (c≈c′ (replicate ∅))

------------------------------------------------------------------------
-- Properties of Var
------------------------------------------------------------------------
-- Functional properties

Var-cong : ∀ {j k} → j ≡ k → Var {n} j ≈ Var k
Var-cong {n} {j} refl = ≈-refl {n} {Var j}

Var-inj : ∀ {j k} → Var {n} j ≈ Var k → j ≡ k
Var-inj {.(suc _)} {zero}  {zero}  j≈k = refl
Var-inj {.(suc _)} {zero}  {suc k} j≈k = ⊥-elim (ε∉∅ (Null-resp-≈ ｛ε｝≈∅ ε∈｛ε｝))
  where
  open ⊆-Reasoning
  ｛ε｝≈∅ : ｛ε｝ {ℓ} ≈ˡ ∅ {c ⊔ ℓ}
  ｛ε｝≈∅ = begin-equality
    ｛ε｝                  ≈⟨ j≈k (｛ε｝ ∷ replicate ∅) ⟩
    lookup (replicate ∅) k ≡⟨ lookup-replicate k ∅ ⟩
    ∅                      ∎
Var-inj {.(suc _)} {suc j} {zero}  j≈k = ⊥-elim (ε∉∅ (Null-resp-≈ ｛ε｝≈∅ ε∈｛ε｝))
  where
  open ⊆-Reasoning
  ｛ε｝≈∅ = begin-equality
    ｛ε｝ {ℓ}                  ≡˘⟨ lookup-replicate j ｛ε｝ ⟩
    lookup (replicate ｛ε｝) j ≈⟨ j≈k (∅ ∷ replicate ｛ε｝) ⟩
    ∅                          ∎
Var-inj {.(suc _)} {suc j} {suc k} j≈k = cong suc (Var-inj λ γ → j≈k (∅ ∷ γ))

------------------------------------------------------------------------
-- Properties of _∙_
------------------------------------------------------------------------
-- Algebraic properties

∙-cong : Congruent₂ (_≈_ {n}) _∙_
∙-cong e₁≈e₁′ e₂≈e₂′ γ = ∙ˡ-cong (e₁≈e₁′ γ) (e₂≈e₂′ γ)

∙-assoc : Associative (_≈_ {n}) _∙_
∙-assoc e₁ e₂ e₃ γ = ∙ˡ-assoc (⟦ e₁ ⟧ γ) (⟦ e₂ ⟧ γ) (⟦ e₃ ⟧ γ)

∙-identityˡ : LeftIdentity (_≈_ {n}) ε _∙_
∙-identityˡ e γ = ∙ˡ-identityˡ (⟦ e ⟧ γ)

∙-identityʳ : RightIdentity (_≈_ {n}) ε _∙_
∙-identityʳ e γ = ∙ˡ-identityʳ (⟦ e ⟧ γ)

∙-identity : Identity (_≈_ {n}) ε _∙_
∙-identity = ∙-identityˡ , ∙-identityʳ

∙-zeroˡ : LeftZero (_≈_ {n}) ⊥ _∙_
∙-zeroˡ e γ = ∙ˡ-zeroˡ (⟦ e ⟧ γ)

∙-zeroʳ : RightZero (_≈_ {n}) ⊥ _∙_
∙-zeroʳ e γ = ∙ˡ-zeroʳ (⟦ e ⟧ γ)

∙-zero : Zero (_≈_ {n}) ⊥ _∙_
∙-zero = ∙-zeroˡ , ∙-zeroʳ

-- Structures

∙-isMagma : IsMagma (_≈_ {n}) _∙_
∙-isMagma {n} = record
  { isEquivalence = ≈-isEquivalence
  ; ∙-cong = λ {e₁} {e₁′} {e₂} {e₂′} → ∙-cong {n} {e₁} {e₁′} {e₂} {e₂′}
  }

∙-isSemigroup : IsSemigroup (_≈_ {n}) _∙_
∙-isSemigroup = record
  { isMagma = ∙-isMagma
  ; assoc   = ∙-assoc
  }

∙-isMonoid : IsMonoid (_≈_ {n}) _∙_ ε
∙-isMonoid = record
  { isSemigroup = ∙-isSemigroup
  ; identity    = ∙-identity
  }

-- Bundles

∙-magma : ∀ {n : ℕ} → Magma _ _
∙-magma {n} = record { isMagma = ∙-isMagma {n} }

∙-semigroup : ∀ {n : ℕ} → Semigroup _ _
∙-semigroup {n} = record { isSemigroup = ∙-isSemigroup {n} }

∙-monoid : ∀ {n : ℕ} → Monoid _ _
∙-monoid {n} = record { isMonoid = ∙-isMonoid {n} }

------------------------------------------------------------------------
-- Properties of _∨_
------------------------------------------------------------------------
-- Algebraic properties

∨-cong : Congruent₂ (_≈_ {n}) _∨_
∨-cong e₁≈e₁′ e₂≈e₂′ γ = ∪-cong (e₁≈e₁′ γ) (e₂≈e₂′ γ)

∨-assoc : Associative (_≈_ {n}) _∨_
∨-assoc e₁ e₂ e₃ γ = ∪-assoc (⟦ e₁ ⟧ γ) (⟦ e₂ ⟧ γ) (⟦ e₃ ⟧ γ)

∨-comm : Commutative (_≈_ {n}) _∨_
∨-comm e₁ e₂ γ = ∪-comm (⟦ e₁ ⟧ γ) (⟦ e₂ ⟧ γ)

∨-identityˡ : LeftIdentity (_≈_ {n}) ⊥ _∨_
∨-identityˡ e γ = ∪-identityˡ (⟦ e ⟧ γ)

∨-identityʳ : RightIdentity (_≈_ {n}) ⊥ _∨_
∨-identityʳ e γ = ∪-identityʳ (⟦ e ⟧ γ)

∨-identity : Identity (_≈_ {n}) ⊥ _∨_
∨-identity = ∨-identityˡ , ∨-identityʳ

∙-distribˡ-∨ : _DistributesOverˡ_ (_≈_ {n}) _∙_ _∨_
∙-distribˡ-∨ e₁ e₂ e₃ γ = ∙-distribˡ-∪ (⟦ e₁ ⟧ γ) (⟦ e₂ ⟧ γ) (⟦ e₃ ⟧ γ)

∙-distribʳ-∨ : _DistributesOverʳ_ (_≈_ {n}) _∙_ _∨_
∙-distribʳ-∨ e₁ e₂ e₃ γ = ∙-distribʳ-∪ (⟦ e₁ ⟧ γ) (⟦ e₂ ⟧ γ) (⟦ e₃ ⟧ γ)

∙-distrib-∨ : _DistributesOver_ (_≈_ {n}) _∙_ _∨_
∙-distrib-∨ = ∙-distribˡ-∨ , ∙-distribʳ-∨

∨-idem : Idempotent (_≈_ {n}) _∨_
∨-idem e γ = ∪-idem (⟦ e ⟧ γ)

-- Structures

∨-isMagma : IsMagma (_≈_ {n}) _∨_
∨-isMagma {n} = record
  { isEquivalence = ≈-isEquivalence
  ; ∙-cong        = λ {e₁} {e₁′} {e₂} {e₂′} → ∨-cong {n} {e₁} {e₁′} {e₂} {e₂′}
  }

∨-isCommutativeMagma : IsCommutativeMagma (_≈_ {n}) _∨_
∨-isCommutativeMagma = record
  { isMagma = ∨-isMagma
  ; comm    = ∨-comm
  }

∨-isSemigroup : IsSemigroup (_≈_ {n}) _∨_
∨-isSemigroup = record
  { isMagma = ∨-isMagma
  ; assoc   = ∨-assoc
  }

∨-isBand : IsBand (_≈_ {n}) _∨_
∨-isBand = record
  { isSemigroup = ∨-isSemigroup
  ; idem        = ∨-idem
  }

∨-isCommutativeSemigroup : IsCommutativeSemigroup (_≈_ {n}) _∨_
∨-isCommutativeSemigroup = record
  { isSemigroup = ∨-isSemigroup
  ; comm        = ∨-comm
  }

∨-isSemilattice : IsSemilattice (_≈_ {n}) _∨_
∨-isSemilattice = record
  { isBand = ∨-isBand
  ; comm   = ∨-comm
  }

∨-isMonoid : IsMonoid (_≈_ {n}) _∨_ ⊥
∨-isMonoid = record
  { isSemigroup = ∨-isSemigroup
  ; identity    = ∨-identity
  }

∨-isCommutativeMonoid : IsCommutativeMonoid (_≈_ {n}) _∨_ ⊥
∨-isCommutativeMonoid = record
  { isMonoid = ∨-isMonoid
  ; comm     = ∨-comm
  }

∨-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid (_≈_ {n}) _∨_ ⊥
∨-isIdempotentCommutativeMonoid = record
  { isCommutativeMonoid = ∨-isCommutativeMonoid
  ; idem                = ∨-idem
  }

∨-∙-isNearSemiring : IsNearSemiring (_≈_ {n}) _∨_ _∙_ ⊥
∨-∙-isNearSemiring {a} = record
  { +-isMonoid    = ∨-isMonoid
  ; *-isSemigroup = ∙-isSemigroup {a}
  ; distribʳ      = ∙-distribʳ-∨
  ; zeroˡ         = ∙-zeroˡ
  }

∨-∙-isSemiringWithoutOne : IsSemiringWithoutOne (_≈_ {n}) _∨_ _∙_ ⊥
∨-∙-isSemiringWithoutOne {a} = record
  { +-isCommutativeMonoid = ∨-isCommutativeMonoid
  ; *-isSemigroup         = ∙-isSemigroup {a}
  ; distrib               = ∙-distrib-∨
  ; zero                  = ∙-zero
  }

∨-∙-isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero (_≈_ {n}) _∨_ _∙_ ⊥ ε
∨-∙-isSemiringWithoutAnnihilatingZero {a} = record
  { +-isCommutativeMonoid = ∨-isCommutativeMonoid
  ; *-isMonoid            = ∙-isMonoid {a}
  ; distrib               = ∙-distrib-∨
  }

∨-∙-isSemiring : IsSemiring (_≈_ {n}) _∨_ _∙_ ⊥ ε
∨-∙-isSemiring {a} = record
  { isSemiringWithoutAnnihilatingZero = ∨-∙-isSemiringWithoutAnnihilatingZero {a}
  ; zero                              = ∙-zero
  }

-- Bundles

∨-magma : ∀ {n : ℕ} → Magma _ _
∨-magma {n} = record { isMagma = ∨-isMagma {n} }

∨-commutativeMagma : ∀ {n : ℕ} → CommutativeMagma _ _
∨-commutativeMagma {n} = record { isCommutativeMagma = ∨-isCommutativeMagma {n} }

∨-semigroup : ∀ {n : ℕ} → Semigroup _ _
∨-semigroup {n} = record { isSemigroup = ∨-isSemigroup {n} }

∨-band : ∀ {n : ℕ} → Band _ _
∨-band {n} = record { isBand = ∨-isBand {n} }

∨-commutativeSemigroup : ∀ {n : ℕ} → CommutativeSemigroup _ _
∨-commutativeSemigroup {n} = record { isCommutativeSemigroup = ∨-isCommutativeSemigroup {n} }

∨-semilattice : ∀ {n : ℕ} → Semilattice _ _
∨-semilattice {n} = record { isSemilattice = ∨-isSemilattice {n} }

∨-monoid : ∀ {n : ℕ} → Monoid _ _
∨-monoid {n} = record { isMonoid = ∨-isMonoid {n} }

∨-commutativeMonoid : ∀ {n : ℕ} → CommutativeMonoid _ _
∨-commutativeMonoid {n} = record { isCommutativeMonoid = ∨-isCommutativeMonoid {n} }

∨-idempotentCommutativeMonoid : ∀ {n : ℕ} → IdempotentCommutativeMonoid _ _
∨-idempotentCommutativeMonoid {n} = record
  { isIdempotentCommutativeMonoid = ∨-isIdempotentCommutativeMonoid {n} }

∨-∙-nearSemiring : ∀ {n : ℕ} → NearSemiring _ _
∨-∙-nearSemiring {n} = record { isNearSemiring = ∨-∙-isNearSemiring {n} }

∨-∙-semiringWithoutOne : ∀ {n : ℕ} → SemiringWithoutOne _ _
∨-∙-semiringWithoutOne {n} = record { isSemiringWithoutOne = ∨-∙-isSemiringWithoutOne {n} }

∨-∙-semiringWithoutAnnihilatingZero : ∀ {n : ℕ} → SemiringWithoutAnnihilatingZero _ _
∨-∙-semiringWithoutAnnihilatingZero {n} = record { isSemiringWithoutAnnihilatingZero = ∨-∙-isSemiringWithoutAnnihilatingZero {n} }

∨-∙-semiring : ∀ {n : ℕ} → Semiring _ _
∨-∙-semiring {n} = record { isSemiring = ∨-∙-isSemiring {n} }

------------------------------------------------------------------------
-- Properties of ⋃_
------------------------------------------------------------------------
-- Functional properties

μ-cong : μ_ Preserves _≈_ ⟶ (_≈_ {n})
μ-cong {x = e} {e′} e≈e′ γ = ⋃-cong λ {A} {B} A≈B → begin-equality
  ⟦ e ⟧ (A ∷ γ) ≈⟨ ⟦⟧-cong-env e (A≈B ∷ Pw.refl ≈ˡ-refl) ⟩
  ⟦ e ⟧ (B ∷ γ) ≈⟨ e≈e′ (B ∷ γ) ⟩
  ⟦ e′ ⟧ (B ∷ γ) ∎
  where open ⊆-Reasoning

------------------------------------------------------------------------
-- Properties of wkn
------------------------------------------------------------------------
-- Algebraic properties

⟦⟧-wkn : ∀ (e : Expression n) i γ A → ⟦ wkn e i ⟧ (insert γ i A) ≈ˡ ⟦ e ⟧ γ
⟦⟧-wkn ⊥         i γ A = ≈ˡ-refl
⟦⟧-wkn ε         i γ A = ≈ˡ-refl
⟦⟧-wkn (Char _)  i γ A = ≈ˡ-refl
⟦⟧-wkn (e₁ ∨ e₂) i γ A = ∪-cong (⟦⟧-wkn e₁ i γ A) (⟦⟧-wkn e₂ i γ A)
⟦⟧-wkn (e₁ ∙ e₂) i γ A = ∙ˡ-cong (⟦⟧-wkn e₁ i γ A) (⟦⟧-wkn e₂ i γ A)
⟦⟧-wkn (Var j)   i γ A = ≈ˡ-reflexive (insert-punchIn γ i A j)
⟦⟧-wkn (μ e)     i γ A = ⋃-cong λ {B} {C} B≈C → begin-equality
  ⟦ wkn e (suc i) ⟧ (B ∷ insert γ i A) ≈⟨ ⟦⟧-cong-env (wkn e (suc i)) (B≈C ∷ Pw.refl ≈ˡ-refl) ⟩
  ⟦ wkn e (suc i) ⟧ (C ∷ insert γ i A) ≈⟨ ⟦⟧-wkn e (suc i) (C ∷ γ) A ⟩
  ⟦ e ⟧ (C ∷ γ)                        ∎
  where open ⊆-Reasoning

wkn-mono :
  ∀ (e₁ e₂ : Expression n) i → (∀ γ → ⟦ e₁ ⟧ γ ⊆ ⟦ e₂ ⟧ γ) → ∀ γ → ⟦ wkn e₁ i ⟧ γ ⊆ ⟦ wkn e₂ i ⟧ γ
wkn-mono e₁ e₂ i mono γ = begin
  ⟦ wkn e₁ i ⟧ γ                                    ≡˘⟨ cong ⟦ wkn e₁ i ⟧ (insert-remove γ i) ⟩
  ⟦ wkn e₁ i ⟧ (insert (remove γ i) i (lookup γ i)) ≈⟨  ⟦⟧-wkn e₁ i (remove γ i) (lookup γ i) ⟩
  ⟦ e₁ ⟧ (remove γ i)                               ⊆⟨  mono (remove γ i) ⟩
  ⟦ e₂ ⟧ (remove γ i)                               ≈˘⟨ ⟦⟧-wkn e₂ i (remove γ i) (lookup γ i) ⟩
  ⟦ wkn e₂ i ⟧ (insert (remove γ i) i (lookup γ i)) ≡⟨  cong ⟦ wkn e₂ i ⟧ (insert-remove γ i) ⟩
  ⟦ wkn e₂ i ⟧ γ                                    ∎
  where open ⊆-Reasoning

-- Syntactic properties

rank-wkn : ∀ (e : Expression n) i → rank (wkn e i) ≡ rank e
rank-wkn ⊥         i = refl
rank-wkn ε         i = refl
rank-wkn (Char _)  i = refl
rank-wkn (e₁ ∨ e₂) i = cong₂ (λ x y → suc (x + y)) (rank-wkn e₁ i) (rank-wkn e₂ i)
rank-wkn (e₁ ∙ _) i  = cong suc (rank-wkn e₁ i)
rank-wkn (Var _)   i = refl
rank-wkn (μ e)     i = cong suc (rank-wkn e (suc i))

------------------------------------------------------------------------
-- Other properties of wkn

μ-wkn : ∀ (e : Expression n) → μ (wkn e zero) ≈ e
μ-wkn e γ = ≈ˡ-trans
  (∀[Fⁿ≈Gⁿ]⇒⋃F≈⋃G λ
    { 0       → ≈ˡ-refl
    ; (suc n) → ⟦⟧-wkn e zero γ (Iter (λ X → ⟦ wkn e zero ⟧ (X ∷ γ)) ∅ n)
    })
  (⋃-inverseʳ (⟦ e ⟧ γ))

------------------------------------------------------------------------
-- Properties of subst
------------------------------------------------------------------------
-- Algebraic properties

subst-monoʳ :
  ∀ (e : Expression (suc n)) i {e₁ e₂} → (∀ γ → ⟦ e₁ ⟧ γ ⊆ ⟦ e₂ ⟧ γ) →
  ∀ γ → ⟦ e [ e₁ / i ] ⟧ γ ⊆ ⟦ e [ e₂ / i ] ⟧ γ
subst-monoʳ ⊥         i           mono γ = ⊆-refl
subst-monoʳ ε         i           mono γ = ⊆-refl
subst-monoʳ (Char c)  i           mono γ = ⊆-refl
subst-monoʳ (e₁ ∨ e₂) i           mono γ = ∪-mono (subst-monoʳ e₁ i mono γ) (subst-monoʳ e₂ i mono γ)
subst-monoʳ (e₁ ∙ e₂) i           mono γ = ∙-mono (subst-monoʳ e₁ i mono γ) (subst-monoʳ e₂ i mono γ)
subst-monoʳ (Var j)   i           mono γ with i ≟ j
...                                           | yes refl = mono γ
...                                           | no _     = ⊆-refl
subst-monoʳ (μ e)     i {e₁} {e₂} mono γ = ⋃-mono (λ {A} {B} A⊆B → begin
  ⟦ e [ wkn e₁ zero / suc i ] ⟧ (A ∷ γ) ⊆⟨ ⟦⟧-mono-env (e [ wkn e₁ zero / suc i ]) (A⊆B ∷ Pw.refl ⊆-refl) ⟩
  ⟦ e [ wkn e₁ zero / suc i ] ⟧ (B ∷ γ) ⊆⟨ subst-monoʳ e (suc i) (wkn-mono e₁ e₂ zero mono) (B ∷ γ) ⟩
  ⟦ e [ wkn e₂ zero / suc i ] ⟧ (B ∷ γ) ∎)
  where open ⊆-Reasoning

subst-congⁱ : ∀ (e : Expression (suc n)) e′ {i j} → i ≡ j → e [ e′ / i ] ≈ e [ e′ / j ]
subst-congⁱ e e′ {i} refl = ≈-refl {x = e [ e′ / i ]}

⟦⟧-subst : ∀ (e : Expression (suc n)) e′ i γ → ⟦ e [ e′ / i ] ⟧ γ ≈ˡ ⟦ e ⟧ (insert γ i (⟦ e′ ⟧ γ))
⟦⟧-subst ⊥         e′ i γ = ≈ˡ-refl
⟦⟧-subst ε         e′ i γ = ≈ˡ-refl
⟦⟧-subst (Char c)  e′ i γ = ≈ˡ-refl
⟦⟧-subst (e₁ ∨ e₂) e′ i γ = ∪-cong (⟦⟧-subst e₁ e′ i γ) (⟦⟧-subst e₂ e′ i γ)
⟦⟧-subst (e₁ ∙ e₂) e′ i γ = ∙ˡ-cong (⟦⟧-subst e₁ e′ i γ) (⟦⟧-subst e₂ e′ i γ)
⟦⟧-subst (Var j)   e′ i γ with i ≟ j
...                            | yes refl = ≈ˡ-reflexive (sym (insert-lookup γ i (⟦ e′ ⟧ γ)))
...                            | no i≢j   = begin-equality
  lookup γ po             ≡˘⟨ cong (λ x → lookup x po) (remove-insert γ i (⟦ e′ ⟧ γ)) ⟩
  lookup (remove γ′ i) po ≡⟨ remove-punchOut γ′ i≢j ⟩
  lookup γ′ j             ∎
  where
  open ⊆-Reasoning
  po = punchOut i≢j
  γ′ = insert γ i (⟦ e′ ⟧ γ)
⟦⟧-subst (μ e)     e′ i γ = ⋃-cong λ {A} {B} A≈B → begin-equality
  ⟦ e [ e′′ / suc i ] ⟧ (A ∷ γ)            ≈⟨ ⟦⟧-cong-env (e [ e′′ / suc i ]) (A≈B ∷ Pw.refl ≈ˡ-refl) ⟩
  ⟦ e [ e′′ / suc i ] ⟧ (B ∷ γ)            ≈⟨ ⟦⟧-subst e e′′ (suc i) (B ∷ γ) ⟩
  ⟦ e ⟧ (B ∷ insert γ i (⟦ e′′ ⟧ (B ∷ γ))) ≈⟨ ⟦⟧-cong-env e (insert′ (⟦⟧-wkn e′ zero γ B) (B ∷ γ) (suc i)) ⟩
  ⟦ e ⟧ (B ∷ insert γ i (⟦ e′ ⟧ γ))        ∎
  where
  open ⊆-Reasoning
  e′′ = wkn e′ zero

  insert′ :
    ∀ {n} {x y : Language (c ⊔ ℓ)} (x≈y : x ≈ˡ y) xs i →
    Pointwise _≈ˡ_ {n = suc n} (insert xs i x) (insert xs i y)
  insert′ x≈y xs        zero   = x≈y ∷ Pw.refl ≈ˡ-refl
  insert′ x≈y (x ∷ xs) (suc i) = ≈ˡ-refl ∷ insert′ x≈y xs i

------------------------------------------------------------------------
-- Other properties

μ-roll : ∀ (e : Expression (suc n)) → e [ μ e / zero ] ≈ μ e
μ-roll e γ =
  ⊆-antisym
    (begin
      ⟦ e [ μ e / zero ] ⟧ γ ≈⟨ ⟦⟧-subst e (μ e) zero γ ⟩
      ⟦ e ⟧ (⟦ μ e ⟧ γ ∷ γ)  ⊆⟨ big-bit ⟩
      ⟦ μ e ⟧ γ              ∎)
    (begin
      ⟦ μ e ⟧ γ              ⊆⟨  ⋃-unroll (⟦⟧-mono-env e ∘ (_∷ Pw.refl ⊆-refl)) ⟩
      ⟦ e ⟧ (⟦ μ e ⟧ γ ∷ γ)  ≈˘⟨ ⟦⟧-subst e (μ e) zero γ ⟩
      ⟦ e [ μ e / zero ] ⟧ γ ∎)
  where
  open ⊆-Reasoning

  get-tag :
    ∀ {m} e A (K : ℕ → Language _) →
    (∀ {w} → w ∈ A → ∃[ n ] w ∈ K n) → (∀ {m n} → m ≤ n → K m ⊆ K n) →
    ∀ i γ {w} → w ∈ ⟦ e ⟧ (insert {n = m} γ i A) → ∃[ n ] w ∈ ⟦ e ⟧ (insert γ i (K n))
  get-tag ε         A K tag mono i γ w∈⟦e⟧ = 0 , w∈⟦e⟧
  get-tag (Char c)  A K tag mono i γ w∈⟦e⟧ = 0 , w∈⟦e⟧
  get-tag (e₁ ∨ e₂) A K tag mono i γ w∈⟦e⟧ =
    [ map₂ inj₁ ∘ get-tag e₁ A K tag mono i γ
    , map₂ inj₂ ∘ get-tag e₂ A K tag mono i γ
    ]′ w∈⟦e⟧
  get-tag (e₁ ∙ e₂) A K tag mono i γ (w₁ , w₂ , w₁∈⟦e₁⟧ , w₂∈⟦e₂⟧ , eq) =
    ( n₁ + n₂
    , w₁
    , w₂
    , ∈-resp-⊆
      (⟦⟧-mono-env
        e₁
        (Pointwise-insert i i {fromWitness refl} (mono (m≤m+n n₁ n₂)) (Pw.refl ⊆-refl)))
      w₁∈⟦e₁⟧′
    , ∈-resp-⊆
      (⟦⟧-mono-env
        e₂
        (Pointwise-insert i i {fromWitness refl} (mono (m≤n+m n₂ n₁)) (Pw.refl ⊆-refl)))
      w₂∈⟦e₂⟧′
    , eq
    )
    where
    n₁,w₁∈⟦e₁⟧′ = get-tag e₁ A K tag mono i γ w₁∈⟦e₁⟧
    n₂,w₂∈⟦e₂⟧′ = get-tag e₂ A K tag mono i γ w₂∈⟦e₂⟧

    n₁       = proj₁ n₁,w₁∈⟦e₁⟧′
    n₂       = proj₁ n₂,w₂∈⟦e₂⟧′
    w₁∈⟦e₁⟧′ = proj₂ n₁,w₁∈⟦e₁⟧′
    w₂∈⟦e₂⟧′ = proj₂ n₂,w₂∈⟦e₂⟧′
  get-tag (Var j)   A K tag mono i γ {w} w∈⟦e⟧ with i ≟ j
  ... | yes refl =
    map₂
      (λ {n} → K n |> insert-lookup γ j |> ≈ˡ-reflexive |> ≈ˡ-sym |> ∈-resp-≈)
      (tag (∈-resp-≈ (≈ˡ-reflexive (insert-lookup γ j A)) w∈⟦e⟧))
  ... | no i≢j   =
    0 ,
      ∈-resp-≈
        (begin-equality
          lookup (insert γ i A) j                              ≡˘⟨ cong (lookup (insert γ i A)) (punchIn-punchOut i≢j) ⟩
          lookup (insert γ i A) (punchIn i (punchOut i≢j))     ≡⟨  insert-punchIn γ i A (punchOut i≢j) ⟩
          lookup γ (punchOut i≢j)                              ≡˘⟨ insert-punchIn γ i (K 0) (punchOut i≢j) ⟩
          lookup (insert γ i (K 0)) (punchIn i (punchOut i≢j)) ≡⟨  cong (lookup (insert γ i (K 0))) (punchIn-punchOut i≢j) ⟩
          lookup (insert γ i (K 0)) j                          ∎)
        w∈⟦e⟧
  get-tag (μ e)     A K tag mono i γ {w} (n , w∈⟦e⟧) = map₂ (n ,_) (⟦e⟧′-tag n w∈⟦e⟧)
    where
    ⟦e⟧′ : ℕ → Language _ → Language _
    ⟦e⟧′ n A = Iter (λ X → ⟦ e ⟧ (X ∷ insert γ i A)) ∅ n

    ⟦e⟧′-monoʳ : ∀ n {X Y} → X ⊆ Y → ⟦e⟧′ n X ⊆ ⟦e⟧′ n Y
    ⟦e⟧′-monoʳ n X⊆Y =
      Iter-monoˡ
        (⟦⟧-mono-env e ∘ (_∷ (Pointwise-insert i i {fromWitness refl} X⊆Y (Pw.refl ⊆-refl))))
        n
        ⊆-refl

    ⟦e⟧′-tag : ∀ m {w} → w ∈ ⟦e⟧′ m A → ∃[ n ] w ∈ ⟦e⟧′ m (K n)
    ⟦e⟧′-tag (suc m) {w} w∈⟦e⟧′ =
      n₁ + n₂ ,
      ∈-resp-⊆
        (⟦⟧-mono-env
          e
          ( ⟦e⟧′-monoʳ m (mono (m≤m+n n₁ n₂))
          ∷ Pointwise-insert i i {fromWitness refl} (mono (m≤n+m n₂ n₁)) (Pw.refl ⊆-refl))
          )
        w∈⟦e⟧′₂
      where
      n₁,w∈⟦e⟧′₁ : ∃[ z ] w ∈ ⟦ e ⟧ (⟦e⟧′ m (K z) ∷ insert γ i A)
      n₁,w∈⟦e⟧′₁ = get-tag e (⟦e⟧′ m A) (⟦e⟧′ m ∘ K) (⟦e⟧′-tag m) (⟦e⟧′-monoʳ m ∘ mono) zero (insert γ i A) w∈⟦e⟧′

      n₁      = proj₁ n₁,w∈⟦e⟧′₁
      w∈⟦e⟧′₁ = proj₂ n₁,w∈⟦e⟧′₁

      n₂,w∈⟦e⟧′₂ : ∃[ z ] w ∈ ⟦ e ⟧ (⟦e⟧′ m (K n₁) ∷ insert γ i (K z))
      n₂,w∈⟦e⟧′₂ = get-tag e A K tag mono (suc i) (⟦e⟧′ m (K n₁) ∷ γ) w∈⟦e⟧′₁

      n₂     = proj₁ n₂,w∈⟦e⟧′₂
      w∈⟦e⟧′₂ = proj₂ n₂,w∈⟦e⟧′₂

  big-bit : ⟦ e ⟧ (⟦ μ e ⟧ γ ∷ γ) ⊆ ⟦ μ e ⟧ γ
  big-bit = sub (λ w∈⟦e⟧ →
    map suc id
      (get-tag
        e
        (⟦ μ e ⟧ γ)
        (Iter (⟦ e ⟧ ∘ (_∷ γ)) ∅)
        id
        (Iter-monoʳ (⟦⟧-mono-env e ∘ (_∷ Pw.refl ⊆-refl)) (⊆-min (⟦ e ⟧ (∅ ∷ γ))))
        zero
        γ
        w∈⟦e⟧))
