{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Expression.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (_≈_ to _∼_)

open import Algebra
open import Cfe.Expression.Base over
open import Cfe.Function.Power
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
open import Data.Empty using (⊥-elim)
open import Data.Fin hiding (_+_)
open import Data.Nat hiding (_≟_; _⊔_; _^_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product using (_,_)
open import Data.Vec
open import Data.Vec.Properties
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
  hiding (refl; sym; setoid; lookup)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality hiding (setoid)
open import Relation.Nullary using (yes; no)

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
⟦⟧-mono-env (Var j)   mono = PW.lookup mono j
⟦⟧-mono-env (μ e)     mono = ⋃-mono λ A⊆B → ⟦⟧-mono-env e (A⊆B ∷ mono)

⟦⟧-cong-env : ∀ (e : Expression n) {γ γ′} → Pointwise _≈ˡ_ γ γ′ → ⟦ e ⟧ γ ≈ˡ ⟦ e ⟧ γ′
⟦⟧-cong-env ⊥         cong = ≈ˡ-refl
⟦⟧-cong-env ε         cong = ≈ˡ-refl
⟦⟧-cong-env (Char _)  cong = ≈ˡ-refl
⟦⟧-cong-env (e₁ ∨ e₂) cong = ∪-cong (⟦⟧-cong-env e₁ cong) (⟦⟧-cong-env e₂ cong)
⟦⟧-cong-env (e₁ ∙ e₂) cong = ∙ˡ-cong (⟦⟧-cong-env e₁ cong) (⟦⟧-cong-env e₂ cong)
⟦⟧-cong-env (Var j)   cong = PW.lookup cong j
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

-- Bundles

partialSetoid : ∀ {n} → PartialSetoid _ _
partialSetoid {n} = record { isPartialEquivalence = ≈-isPartialEquivalence {n} }

setoid : ∀ {n} → Setoid _ _
setoid {n} = record { isEquivalence = ≈-isEquivalence {n} }

------------------------------------------------------------------------
-- Properties of _<ᵣₐₙₖ_
------------------------------------------------------------------------
-- Relational properties

<ᵣₐₙₖ-trans : Trans (_<ᵣₐₙₖ_ {k}) (_<ᵣₐₙₖ_ {m} {n}) _<ᵣₐₙₖ_
<ᵣₐₙₖ-trans = <-trans

<ᵣₐₙₖ-asym : Asymmetric (_<ᵣₐₙₖ_ {n})
<ᵣₐₙₖ-asym = <-asym

------------------------------------------------------------------------
-- Other properties

rank-∨ˡ : ∀ (e₁ e₂ : Expression n) → e₁ <ᵣₐₙₖ e₁ ∨ e₂
rank-∨ˡ e₁ e₂ = begin-strict
  rank e₁           ≤⟨ m≤m+n (rank e₁) (rank e₂) ⟩
  rank e₁ + rank e₂ <⟨ n<1+n (rank e₁ + rank e₂) ⟩
  rank (e₁ ∨ e₂)    ∎
  where
  open ≤-Reasoning

rank-∨ʳ : ∀ (e₁ e₂ : Expression n) → e₂ <ᵣₐₙₖ e₁ ∨ e₂
rank-∨ʳ e₁ e₂ = begin-strict
  rank e₂           ≤⟨ m≤n+m (rank e₂) (rank e₁) ⟩
  rank e₁ + rank e₂ <⟨ n<1+n (rank e₁ + rank e₂) ⟩
  rank (e₁ ∨ e₂)    ∎
  where
  open ≤-Reasoning

rank-∙ˡ : ∀ (e₁ e₂ : Expression n) → e₁ <ᵣₐₙₖ e₁ ∙ e₂
rank-∙ˡ e₁ _ = n<1+n (rank e₁)

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
  open import Relation.Binary.Reasoning.Setoid setoidˡ
  ｛ε｝≈∅ = begin
    ｛ε｝ {ℓ}              ≈⟨ j≈k (｛ε｝ ∷ replicate ∅) ⟩
    lookup (replicate ∅) k ≡⟨ lookup-replicate k ∅ ⟩
    ∅                      ∎
Var-inj {.(suc _)} {suc j} {zero}  j≈k = ⊥-elim (ε∉∅ (Null-resp-≈ ｛ε｝≈∅ ε∈｛ε｝))
  where
  open import Relation.Binary.Reasoning.Setoid setoidˡ
  ｛ε｝≈∅ = begin
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
μ-cong {x = e} {e′} e≈e′ γ = ⋃-cong λ {A} {B} A≈B → begin
  ⟦ e ⟧ (A ∷ γ) ≈⟨ ⟦⟧-cong-env e (A≈B ∷ PW.refl ≈ˡ-refl) ⟩
  ⟦ e ⟧ (B ∷ γ) ≈⟨ e≈e′ (B ∷ γ) ⟩
  ⟦ e′ ⟧ (B ∷ γ) ∎
  where
  open import Relation.Binary.Reasoning.Setoid setoidˡ

------------------------------------------------------------------------
-- Properties of wkn
------------------------------------------------------------------------
-- Algebraic properties

wkn-cong : ∀ (e : Expression n) i γ A → ⟦ wkn e i ⟧ (insert γ i A) ≈ˡ ⟦ e ⟧ γ
wkn-cong ⊥         i γ A = ≈ˡ-refl
wkn-cong ε         i γ A = ≈ˡ-refl
wkn-cong (Char _)  i γ A = ≈ˡ-refl
wkn-cong (e₁ ∨ e₂) i γ A = ∪-cong (wkn-cong e₁ i γ A) (wkn-cong e₂ i γ A)
wkn-cong (e₁ ∙ e₂) i γ A = ∙ˡ-cong (wkn-cong e₁ i γ A) (wkn-cong e₂ i γ A)
wkn-cong (Var j)   i γ A = ≈ˡ-reflexive (insert-punchIn γ i A j)
wkn-cong (μ e)     i γ A = ⋃-cong λ {B} {C} B≈C → begin
  ⟦ wkn e (suc i) ⟧ (B ∷ insert γ i A) ≈⟨ ⟦⟧-cong-env (wkn e (suc i)) (B≈C ∷ PW.refl ≈ˡ-refl) ⟩
  ⟦ wkn e (suc i) ⟧ (C ∷ insert γ i A) ≈⟨ wkn-cong e (suc i) (C ∷ γ) A ⟩
  ⟦ e ⟧ (C ∷ γ)                        ∎
  where
  open import Relation.Binary.Reasoning.Setoid setoidˡ

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
    ; (suc n) → wkn-cong e zero γ (((λ X → ⟦ wkn e zero ⟧ (X ∷ γ)) ^ n) ∅)
    })
  (⋃-inverseʳ (⟦ e ⟧ γ))

------------------------------------------------------------------------
-- Properties of subst
------------------------------------------------------------------------
-- Algebraic properties

subst-cong : ∀ (e : Expression (suc n)) e′ i γ → ⟦ e [ e′ / i ] ⟧ γ ≈ˡ ⟦ e ⟧ (insert γ i (⟦ e′ ⟧ γ))
subst-cong ⊥         e′ i γ = ≈ˡ-refl
subst-cong ε         e′ i γ = ≈ˡ-refl
subst-cong (Char c)  e′ i γ = ≈ˡ-refl
subst-cong (e₁ ∨ e₂) e′ i γ = ∪-cong (subst-cong e₁ e′ i γ) (subst-cong e₂ e′ i γ)
subst-cong (e₁ ∙ e₂) e′ i γ = ∙ˡ-cong (subst-cong e₁ e′ i γ) (subst-cong e₂ e′ i γ)
subst-cong (Var j)   e′ i γ with i ≟ j
...                            | yes refl = ≈ˡ-reflexive (sym (insert-lookup γ i (⟦ e′ ⟧ γ)))
...                            | no i≢j   = ≈ˡ-reflexive (begin
  lookup γ po             ≡˘⟨ cong (λ x → lookup x po) (remove-insert γ i (⟦ e′ ⟧ γ)) ⟩
  lookup (remove γ′ i) po ≡⟨ remove-punchOut γ′ i≢j ⟩
  lookup γ′ j             ∎)
  where
  open ≡-Reasoning
  po = punchOut i≢j
  γ′ = insert γ i (⟦ e′ ⟧ γ)
subst-cong (μ e)     e′ i γ = ⋃-cong λ {A} {B} A≈B → begin
  ⟦ e [ e′′ / suc i ] ⟧ (A ∷ γ)            ≈⟨ ⟦⟧-cong-env (e [ e′′ / suc i ]) (A≈B ∷ PW.refl ≈ˡ-refl) ⟩
  ⟦ e [ e′′ / suc i ] ⟧ (B ∷ γ)            ≈⟨ subst-cong e e′′ (suc i) (B ∷ γ) ⟩
  ⟦ e ⟧ (B ∷ insert γ i (⟦ e′′ ⟧ (B ∷ γ))) ≈⟨ ⟦⟧-cong-env e (insert′ (wkn-cong e′ zero γ B) (B ∷ γ) (suc i)) ⟩
  ⟦ e ⟧ (B ∷ insert γ i (⟦ e′ ⟧ γ))        ∎
  where
  open import Relation.Binary.Reasoning.Setoid setoidˡ
  e′′ = wkn e′ zero

  insert′ :
    ∀ {n} {x y : Language (c ⊔ ℓ)} (x≈y : x ≈ˡ y) xs i →
    Pointwise _≈ˡ_ {n = suc n} (insert xs i x) (insert xs i y)
  insert′ x≈y xs        zero   = x≈y ∷ PW.refl ≈ˡ-refl
  insert′ x≈y (x ∷ xs) (suc i) = ≈ˡ-refl ∷ insert′ x≈y xs i
