{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Type.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using ()
  renaming
  ( Carrier to C
  ; _≈_ to _∼_
  ; refl to ∼-refl
  ; sym to ∼-sym
  ; trans to ∼-trans
  )

open import Algebra
open import Cfe.Function.Power
open import Cfe.Language over
  hiding
  ( _≉_; ≈-refl; ≈-trans; ≈-isPartialEquivalence; ≈-isEquivalence; partialSetoid; setoid
  ; ∙-mono ; ∙-cong ; ∙-identityʳ ; ∙-assoc; ∙-isMagma ; ∙-isSemigroup ; ∙-magma ; ∙-semigroup )
  renaming
  ( _≈_ to _≈ˡ_
  ; ≈-sym to ≈ˡ-sym
  ; _∙_ to _∙ˡ_
  )
open import Cfe.List.Compare over
open import Cfe.Type.Base over
  renaming (_⇒_ to _⇒ᵗ_)
open import Data.Bool renaming (_≤_ to _≤ᵇ_; _∨_ to _∨ᵇ_)
open import Data.Bool.Properties
  hiding
    ( ≤-isPreorder; ≤-isPartialOrder ; ≤-preorder ; ≤-poset
    ; ∨-identity
    ; ∨-isMagma ; ∨-isSemigroup ; ∨-isBand ; ∨-isSemilattice ; ∨-isMonoid ; ∨-isCommutativeMonoid
    ; ∨-isIdempotentCommutativeMonoid
    ; ∨-magma ; ∨-semigroup ; ∨-band ; ∨-semilattice ; ∨-commutativeMonoid
    ; ∨-idempotentCommutativeMonoid
    )
  renaming
    ( ≤-refl to ≤ᵇ-refl
    ; ≤-reflexive to ≤ᵇ-reflexive
    ; ≤-trans to ≤ᵇ-trans
    ; ≤-antisym to ≤ᵇ-antisym
    ; ≤-maximum to ≤ᵇ-maximum
    ; ≤-minimum to ≤ᵇ-minimum
    ; ∨-assoc to ∨ᵇ-assoc
    ; ∨-comm to ∨ᵇ-comm
    ; ∨-identityˡ to ∨ᵇ-identityˡ
    ; ∨-identityʳ to ∨ᵇ-identityʳ
    ; ∨-idem to ∨ᵇ-idem
    )
open import Data.Empty using (⊥-elim)
open import Data.Empty.Polymorphic using (⊥)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Binary.Pointwise as Pw hiding (refl; setoid; map)
open import Data.Nat using (suc; zero; _+_; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Nat.Properties using (m≤m+n; m≤n+m)
open import Data.Product renaming (map to mapᵖ)
open import Data.Product.Algebra using (×-distribˡ-⊎)
open import Data.Sum hiding (map₁; map₂; swap)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (Equivalence)
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary

private
  variable
    a b fℓ lℓ fℓ₁ lℓ₁ fℓ₂ lℓ₂ fℓ₃ lℓ₃ fℓ₄ lℓ₄ : Level
    A : Language a
    B : Language b
    τ : Type fℓ lℓ
    τ₁ : Type fℓ₁ lℓ₁
    τ₂ : Type fℓ₂ lℓ₂
    τ₃ : Type fℓ₃ lℓ₃
    τ₄ : Type fℓ₄ lℓ₄

------------------------------------------------------------------------
-- Miscellaneous properties
------------------------------------------------------------------------
-- T

T-resp-≤ : T Respects _≤ᵇ_
T-resp-≤ b≤b = id

------------------------------------------------------------------------
-- ∧

∧-mono : Congruent₂ _≤ᵇ_ _∧_
∧-mono {false} {v = false} f≤t u≤v = b≤b
∧-mono {false} {v = false} b≤b u≤v = b≤b
∧-mono {false} {v = true}  f≤t u≤v = f≤t
∧-mono {false} {v = true}  b≤b u≤v = b≤b
∧-mono {true}              b≤b u≤v = u≤v

------------------------------------------------------------------------
-- ∨ᵇ

∨ᵇ-mono : Congruent₂ _≤ᵇ_ _∨ᵇ_
∨ᵇ-mono {true}              b≤b u≤v = b≤b
∨ᵇ-mono {false}             b≤b u≤v = u≤v
∨ᵇ-mono {false} {u = false} f≤t u≤v = f≤t
∨ᵇ-mono {false} {u = true}  f≤t u≤v = b≤b

------------------------------------------------------------------------
-- _⇒ᵗ_

⇒ᵗ-mono :
  ∀ {b₁ b₂} {A : C → Set a} {B : C → Set b} →
  b₁ ≤ᵇ b₂ → (∀ {c} → A c → B c) → ∀ {c} → (b₁ ⇒ᵗ A) c → (b₂ ⇒ᵗ B) c
⇒ᵗ-mono {b₁ = true} b≤b A⊆B c∈A = A⊆B c∈A

⇒ᵗ-monoˡ :
  ∀ {b₁ b₂} (A : C → Set a) →
  b₁ ≤ᵇ b₂ → ∀ {c} → (b₁ ⇒ᵗ A) c → (b₂ ⇒ᵗ A) c
⇒ᵗ-monoˡ A b₁≤b₂ = ⇒ᵗ-mono b₁≤b₂ id

⇒ᵗ-monoʳ :
  ∀ {A : C → Set a} {B : C → Set b} b → (∀ {c} → A c → B c) → ∀ {c} → (b ⇒ᵗ A) c → (b ⇒ᵗ B) c
⇒ᵗ-monoʳ b A⊆B = ⇒ᵗ-mono (≤ᵇ-refl {b}) A⊆B

⇒ᵗ-construct : ∀ {b} {A : C → Set a} {c} → T b → A c → (b ⇒ᵗ A) c
⇒ᵗ-construct {b = true} _ c∈A = c∈A

⇒ᵗ-zeroʳ : ∀ {A : C → Set a} b → (∀ {c} → ¬ A c) → ∀ {c} → ¬ (b ⇒ᵗ A) c
⇒ᵗ-zeroʳ true ∄[A] c∈A = ∄[A] c∈A

⇒ᵗ-idemˡ : ∀ b (A : C → Set a) {c} → (b ⇒ᵗ (b ⇒ᵗ A)) c → (b ⇒ᵗ A) c
⇒ᵗ-idemˡ true _ c∈A = c∈A

⇒ᵗA⊆A : ∀ b (A : C → Set a) {c} → (b ⇒ᵗ A) c → A c
⇒ᵗA⊆A true _ c∈A = c∈A

⇒ᵗ-⊎ : ∀ x (A : C → Set a) (B : C → Set b) {c} → (x ⇒ᵗ λ c → A c ⊎ B c) c → (x ⇒ᵗ A) c ⊎ (x ⇒ᵗ B) c
⇒ᵗ-⊎ true _ _ c∈A⊎B = c∈A⊎B

⇒ᵗ-∧ : ∀ b₁ b₂ (A : C → Set a) {c} → (b₁ ∧ b₂ ⇒ᵗ A) c → (b₁ ⇒ᵗ (b₂ ⇒ᵗ A)) c
⇒ᵗ-∧ true true _ c∈A = c∈A

⇒ᵗ-∧′ : ∀ b₁ b₂ (A : C → Set a) {c} → (b₁ ⇒ᵗ (b₂ ⇒ᵗ A)) c → (b₁ ∧ b₂ ⇒ᵗ A) c
⇒ᵗ-∧′ true true _ c∈A = c∈A

⇒ᵗ-∨ᵇ : ∀ b₁ b₂ (A : C → Set a) {c} → (b₁ ∨ᵇ b₂ ⇒ᵗ A) c → (b₁ ⇒ᵗ A) c ⊎ (b₂ ⇒ᵗ A) c
⇒ᵗ-∨ᵇ true  _    _ c∈A = inj₁ c∈A
⇒ᵗ-∨ᵇ false true _ c∈A = inj₂ c∈A

⇒ᵗ-∨ᵇ′ˡ : ∀ b₁ b₂ (A : C → Set a) {c} → (b₁ ⇒ᵗ A) c → (b₁ ∨ᵇ b₂ ⇒ᵗ A) c
⇒ᵗ-∨ᵇ′ˡ true _ _ c∈A = c∈A

⇒ᵗ-∨ᵇ′ʳ : ∀ b₁ b₂ (A : C → Set a) {c} → (b₂ ⇒ᵗ A) c → (b₁ ∨ᵇ b₂ ⇒ᵗ A) c
⇒ᵗ-∨ᵇ′ʳ false true _ c∈A = c∈A
⇒ᵗ-∨ᵇ′ʳ true  true _ c∈A = c∈A

⇒ᵗ-contra : ∀ b (A : C → Set a) {c} → (b ⇒ᵗ A) c → T b
⇒ᵗ-contra true _ _ = _

------------------------------------------------------------------------
-- Properties of _≈_
------------------------------------------------------------------------
-- Definitions

infix 4 _≉_

_≉_ : REL (Type fℓ₁ lℓ₁) (Type fℓ₂ lℓ₂) _
τ₁ ≉ τ₂ = ¬ τ₁ ≈ τ₂

-- Relational Properties

≈-refl : Reflexive (_≈_ {fℓ} {lℓ})
≈-refl = record
  { n≡n   = refl
  ; f₁⊆f₂ = id
  ; f₁⊇f₂ = id
  ; l₁⊆l₂ = id
  ; l₁⊇l₂ = id
  }

≈-sym : Sym (_≈_ {fℓ₁} {lℓ₁} {fℓ₂} {lℓ₂}) _≈_
≈-sym τ₁≈τ₂ = record
  { n≡n   = sym n≡n
  ; f₁⊆f₂ = f₁⊇f₂
  ; f₁⊇f₂ = f₁⊆f₂
  ; l₁⊆l₂ = l₁⊇l₂
  ; l₁⊇l₂ = l₁⊆l₂
  }
  where
  open _≈_ τ₁≈τ₂

≈-trans : Trans (_≈_ {fℓ₁} {lℓ₁}) (_≈_ {fℓ₂} {lℓ₂} {fℓ₃} {lℓ₃}) _≈_
≈-trans τ₁≈τ₂ τ₂≈τ₃ = record
  { n≡n   = trans τ₁≈τ₂.n≡n τ₂≈τ₃.n≡n
  ; f₁⊆f₂ = τ₂≈τ₃.f₁⊆f₂ ∘ τ₁≈τ₂.f₁⊆f₂
  ; f₁⊇f₂ = τ₁≈τ₂.f₁⊇f₂ ∘ τ₂≈τ₃.f₁⊇f₂
  ; l₁⊆l₂ = τ₂≈τ₃.l₁⊆l₂ ∘ τ₁≈τ₂.l₁⊆l₂
  ; l₁⊇l₂ = τ₁≈τ₂.l₁⊇l₂ ∘ τ₂≈τ₃.l₁⊇l₂
  }
  where
  module τ₁≈τ₂ = _≈_ τ₁≈τ₂
  module τ₂≈τ₃ = _≈_ τ₂≈τ₃

------------------------------------------------------------------------
-- Structures

≈-isPartialEquivalence : IsPartialEquivalence (_≈_ {fℓ} {lℓ})
≈-isPartialEquivalence = record
  { sym   = ≈-sym
  ; trans = ≈-trans
  }

≈-isEquivalence : IsEquivalence (_≈_ {fℓ} {lℓ})
≈-isEquivalence = record
  { refl  = ≈-refl
  ; sym   = ≈-sym
  ; trans = ≈-trans
  }

------------------------------------------------------------------------
-- Bundles

partialSetoid : ∀ {fℓ} {lℓ} → PartialSetoid _ _
partialSetoid {fℓ} {lℓ} = record { isPartialEquivalence = ≈-isPartialEquivalence {fℓ} {lℓ} }

setoid : ∀ {fℓ} {lℓ} → Setoid _ _
setoid {fℓ} {lℓ} = record { isEquivalence = ≈-isEquivalence {fℓ} {lℓ} }

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------
-- Relational Properties

≤-refl : Reflexive (_≤_ {fℓ} {lℓ})
≤-refl = record
  { n≤n = ≤ᵇ-refl
  ; f⊆f = id
  ; l⊆l = id
  }

≤-reflexive : _≈_ {fℓ₁} {lℓ₁} {fℓ₂} {lℓ₂} ⇒ _≤_
≤-reflexive τ₁≈τ₂ = record
  { n≤n = ≤ᵇ-reflexive n≡n
  ; f⊆f = f₁⊆f₂
  ; l⊆l = l₁⊆l₂
  }
  where
  open _≈_ τ₁≈τ₂

≥-reflexive : _≈_ {fℓ₁} {lℓ₁} {fℓ₂} {lℓ₂} ⇒ _≥_
≥-reflexive τ₁≈τ₂ = record
  { n≤n = ≤ᵇ-reflexive (sym n≡n)
  ; f⊆f = f₁⊇f₂
  ; l⊆l = l₁⊇l₂
  }
  where
  open _≈_ τ₁≈τ₂

≤-trans : Trans (_≤_ {fℓ₁} {lℓ₁}) (_≤_ {fℓ₂} {lℓ₂} {fℓ₃} {lℓ₃}) _≤_
≤-trans τ₁≤τ₂ τ₂≤τ₃ = record
  { n≤n = ≤ᵇ-trans τ₁≤τ₂.n≤n τ₂≤τ₃.n≤n
  ; f⊆f = τ₂≤τ₃.f⊆f ∘ τ₁≤τ₂.f⊆f
  ; l⊆l = τ₂≤τ₃.l⊆l ∘ τ₁≤τ₂.l⊆l
  }
  where
  module τ₁≤τ₂ = _≤_ τ₁≤τ₂
  module τ₂≤τ₃ = _≤_ τ₂≤τ₃

≤-antisym : Antisym (_≤_ {fℓ₁} {lℓ₁} {fℓ₂} {lℓ₂}) _≤_ _≈_
≤-antisym τ₁≤τ₂ τ₁≥τ₂ = record
  { n≡n   = ≤ᵇ-antisym τ₁≤τ₂.n≤n τ₁≥τ₂.n≤n
  ; f₁⊆f₂ = τ₁≤τ₂.f⊆f
  ; f₁⊇f₂ = τ₁≥τ₂.f⊆f
  ; l₁⊆l₂ = τ₁≤τ₂.l⊆l
  ; l₁⊇l₂ = τ₁≥τ₂.l⊆l
  }
  where
  module τ₁≤τ₂ = _≤_ τ₁≤τ₂
  module τ₁≥τ₂ = _≤_ τ₁≥τ₂

≤-min : Min (_≤_ {fℓ₁} {lℓ₁} {fℓ₂} {lℓ₂}) τ⊥
≤-min τ = record
  { n≤n = ≤ᵇ-minimum null
  ; f⊆f = λ ()
  ; l⊆l = λ ()
  }
  where open Type τ

------------------------------------------------------------------------
-- Structures

≤-isPreorder : IsPreorder (_≈_ {fℓ} {lℓ}) _≤_
≤-isPreorder = record
  { isEquivalence = ≈-isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder (_≈_ {fℓ} {lℓ}) _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

------------------------------------------------------------------------
-- Bundles

≤-preorder : ∀ {fℓ} {lℓ} → Preorder _ _ _
≤-preorder {fℓ} {lℓ} = record { isPreorder = ≤-isPreorder {fℓ} {lℓ} }

≤-poset : ∀ {fℓ} {lℓ} → Poset _ _ _
≤-poset {fℓ} {lℓ} = record { isPartialOrder = ≤-isPartialOrder {fℓ} {lℓ} }

------------------------------------------------------------------------
-- Properties of _⊨_
------------------------------------------------------------------------
-- Relational Properties

⊨-min : Min (_⊨_ {a} {fℓ} {lℓ}) ∅
⊨-min τ = record
  { n⇒n = λ ()
  ; f⇒f = λ ()
  ; l⇒l = λ ()
  }

⊨-resp-⊇ : A ⊇ B → A ⊨ τ → B ⊨ τ
⊨-resp-⊇ A⊇B A⊨τ = record
  { n⇒n = n⇒n ∘ Null-resp-⊆ A⊇B
  ; f⇒f = f⇒f ∘ First-resp-⊆ A⊇B
  ; l⇒l = l⇒l ∘ Flast-resp-⊆ A⊇B
  }
  where open _⊨_ A⊨τ

⊨-resp-≈ˡ : A ≈ˡ B → A ⊨ τ → B ⊨ τ
⊨-resp-≈ˡ = ⊨-resp-⊇ ∘ ⊇-reflexive

⊨-resp-≤ : τ₁ ≤ τ₂ → A ⊨ τ₁ → A ⊨ τ₂
⊨-resp-≤ τ₁≤τ₂ A⊨τ₁ = record
  { n⇒n = T-resp-≤ n≤n ∘ n⇒n
  ; f⇒f = f⊆f ∘ f⇒f
  ; l⇒l = l⊆l ∘ l⇒l
  }
  where
  open _≤_ τ₁≤τ₂
  open _⊨_ A⊨τ₁

⊨-resp-≈ʳ : τ₁ ≈ τ₂ → A ⊨ τ₁ → A ⊨ τ₂
⊨-resp-≈ʳ = ⊨-resp-≤ ∘ ≤-reflexive

⊨-fix : ∀ {F : Op₁ (Language a)} → Congruent₁ _⊆_ F → (∀ {A} → A ⊨ τ → F A ⊨ τ) → ⋃ F ⊨ τ
⊨-fix {τ = τ} {F = F} mono ⊨-step = record
  { n⇒n = uncurry Fⁿ⊨τ.n⇒n
  ; f⇒f = λ (w , n , cw∈Fⁿ) → Fⁿ⊨τ.f⇒f n (-, cw∈Fⁿ)
  ; l⇒l = λ (x , w , (m , xw∈Fᵐ) , w′ , n , xwcw′∈Fⁿ) →
    Fⁿ⊨τ.l⇒l
      (m + n)
      (-, -, ∈-resp-⊆ (step (m≤m+n m n)) xw∈Fᵐ , -, ∈-resp-⊆ (step (m≤n+m n m)) xwcw′∈Fⁿ)
  }
  where
  Fⁿ⊨τ : ∀ n → (F ^ n) ∅ ⊨ τ
  Fⁿ⊨τ zero    = ⊨-min τ
  Fⁿ⊨τ (suc n) = ⊨-step (Fⁿ⊨τ n)

  module Fⁿ⊨τ n = _⊨_ (Fⁿ⊨τ n)

  step : ∀ {m n} → m ≤ⁿ n → (F ^ m) ∅ ⊆ (F ^ n) ∅
  step {n = n} z≤n       = ⊆-min ((F  ^ n) ∅)
  step         (s≤s m≤n) = mono (step m≤n)

------------------------------------------------------------------------
-- ⋃-⊨ : ∀ {a fℓ lℓ} {F : Op₁ (Language a)} {τ : Type fℓ lℓ} →
--       (Congruent₁ _≤ˡ_ F) →
--       (∀ {L} → L ⊨ τ → F L ⊨ τ) → ⋃ F ⊨ τ
-- ⋃-⊨ {a} {F = F} {τ} ≤-mono ⊨-mono = record
--   ; l⇒l = λ
--     { (_ , l≢ε , (m , l∈Fᵐ) , _ , (n , l++x∷l′∈Fⁿ)) →
--          _⊨_.l⇒l (Fⁿ⊨τ (m + n))
--            (-, l≢ε , _≤ˡ_.f (^-mono (≤-stepsʳ {m} n ≤ⁿ-refl)) l∈Fᵐ ,
--             -, _≤ˡ_.f (^-mono (≤-stepsˡ m ≤ⁿ-refl)) l++x∷l′∈Fⁿ)
--     }
--   }

------------------------------------------------------------------------
-- Properties of _⊛_
------------------------------------------------------------------------

⊛-resp-≥ˡ : τ₁ ≥ τ₂ → τ ⊛ τ₁ → τ ⊛ τ₂
⊛-resp-≥ˡ τ₁≥τ₂ τ⊛τ₁ = record
  { ∄[l₁∩f₂] = ∄[l₁∩f₂] ∘ map₂ f⊆f
  ; ¬n₁      = ¬n₁
  }
  where
  open _≤_ τ₁≥τ₂
  open _⊛_ τ⊛τ₁

⊛-resp-≥ʳ : τ₁ ≥ τ₂ → τ₁ ⊛ τ → τ₂ ⊛ τ
⊛-resp-≥ʳ τ₁≥τ₂ τ₁⊛τ = record
  { ∄[l₁∩f₂] = ∄[l₁∩f₂] ∘ map₁ l⊆l
  ; ¬n₁      = ¬n₁ ∘ T-resp-≤ n≤n
  }
  where
  open _≤_ τ₁≥τ₂
  open _⊛_ τ₁⊛τ

⊛-resp-≈ˡ : τ₁ ≈ τ₂ → τ ⊛ τ₁ → τ ⊛ τ₂
⊛-resp-≈ˡ = ⊛-resp-≥ˡ ∘ ≥-reflexive

⊛-resp-≈ʳ : τ₁ ≈ τ₂ → τ₁ ⊛ τ → τ₂ ⊛ τ
⊛-resp-≈ʳ = ⊛-resp-≥ʳ ∘ ≥-reflexive

------------------------------------------------------------------------
-- Properties of _#_
------------------------------------------------------------------------

#-sym : Sym (_#_ {fℓ₁} {lℓ₁} {fℓ₂} {lℓ₂}) _#_
#-sym τ₁#τ₂ = record
  { ∄[f₁∩f₂] = ∄[f₁∩f₂] ∘ swap
  ; ¬n₁∨¬n₂  = ¬n₁∨¬n₂ ∘ swap
  }
  where open _#_ τ₁#τ₂

#-max : Max (_#_ {fℓ₁} {lℓ₁} {fℓ₂} {lℓ₂}) τ⊥
#-max τ = record
  { ∄[f₁∩f₂] = λ ()
  ; ¬n₁∨¬n₂  = λ ()
  }

#-min : Min (_#_ {fℓ₁} {lℓ₁} {fℓ₂} {lℓ₂}) τ⊥
#-min = #-sym ∘ #-max

#-resp-≥ˡ : τ₁ ≥ τ₂ → τ # τ₁ → τ # τ₂
#-resp-≥ˡ τ₁≥τ₂ τ#τ₁ = record
  { ∄[f₁∩f₂] = ∄[f₁∩f₂] ∘ map₂ f⊆f
  ; ¬n₁∨¬n₂  = ¬n₁∨¬n₂ ∘ map₂ (T-resp-≤ n≤n)
  }
  where
  open _≤_ τ₁≥τ₂
  open _#_ τ#τ₁

#-resp-≥ʳ : τ₁ ≥ τ₂ → τ₁ # τ → τ₂ # τ
#-resp-≥ʳ τ₁≥τ₂ τ₁#τ = record
  { ∄[f₁∩f₂] = ∄[f₁∩f₂] ∘ map₁ f⊆f
  ; ¬n₁∨¬n₂  = ¬n₁∨¬n₂ ∘ map₁ (T-resp-≤ n≤n)
  }
  where
  open _≤_ τ₁≥τ₂
  open _#_ τ₁#τ

#-resp-≈ˡ : τ₁ ≈ τ₂ → τ # τ₁ → τ # τ₂
#-resp-≈ˡ = #-resp-≥ˡ ∘ ≥-reflexive

#-resp-≈ʳ : τ₁ ≈ τ₂ → τ₁ # τ → τ₂ # τ
#-resp-≈ʳ = #-resp-≥ʳ ∘ ≥-reflexive

------------------------------------------------------------------------
-- Properties of τ⊥
------------------------------------------------------------------------

L⊨τ⊥⇒L≈∅ : A ⊨ τ⊥ {fℓ} {lℓ} → A ≈ˡ ∅ {b}
L⊨τ⊥⇒L≈∅ {A = A} A⊨τ⊥ = ε∉A+∄[First[A]]⇒A≈∅ n⇒n (λ _ xw∈A → case f⇒f xw∈A of λ ())
  where open _⊨_ A⊨τ⊥

------------------------------------------------------------------------
-- Properties of τε
------------------------------------------------------------------------

L⊨τε⇒L≤｛ε｝ : A ⊨ τε {fℓ} {lℓ} → A ⊆ ｛ε｝ {b}
L⊨τε⇒L≤｛ε｝ {A = A} A⊨τε = ∄[First[A]]⇒A⊆｛ε｝ λ _ xw∈A → case f⇒f xw∈A of λ ()
  where open _⊨_ A⊨τε

｛ε｝⊨τε : ｛ε｝{a} ⊨ τε {fℓ} {lℓ}
｛ε｝⊨τε = record
  { n⇒n = const _
  ; f⇒f = λ ()
  ; l⇒l = λ ()
  }

------------------------------------------------------------------------
-- Properties of τ[_]
------------------------------------------------------------------------

｛c｝⊨τ[c] : ∀ c → ｛ c ｝ ⊨ τ[ c ]
｛c｝⊨τ[c] c = record
  { n⇒n = λ ()
  ; f⇒f = λ {(_ , c∼c′ ∷ []) → c∼c′}
  ; l⇒l = λ {(_ , [] , _ , [] , _ ∷ ())}
  }

------------------------------------------------------------------------
-- Properties of _∙_
------------------------------------------------------------------------
-- Algebraic Properties

∙-mono : τ₁ ≤ τ₂ → τ₃ ≤ τ₄ → τ₁ ∙ τ₃ ≤ τ₂ ∙ τ₄
∙-mono τ₁≤τ₂ τ₃≤τ₄ = record
  { n≤n = ∧-mono τ₁≤τ₂.n≤n τ₃≤τ₄.n≤n
  ; f⊆f = map τ₁≤τ₂.f⊆f (⇒ᵗ-mono τ₁≤τ₂.n≤n τ₃≤τ₄.f⊆f)
  ; l⊆l = map τ₃≤τ₄.l⊆l (⇒ᵗ-mono τ₃≤τ₄.n≤n (map τ₃≤τ₄.f⊆f τ₁≤τ₂.l⊆l))
  }
  where
  module τ₁≤τ₂ = _≤_ τ₁≤τ₂
  module τ₃≤τ₄ = _≤_ τ₃≤τ₄

∙-cong : τ₁ ≈ τ₂ → τ₃ ≈ τ₄ → τ₁ ∙ τ₃ ≈ τ₂ ∙ τ₄
∙-cong τ₁≈τ₂ τ₃≈τ₄ =
  ≤-antisym
    (∙-mono (≤-reflexive τ₁≈τ₂) (≤-reflexive τ₃≈τ₄))
    (∙-mono (≤-reflexive (≈-sym τ₁≈τ₂)) (≤-reflexive (≈-sym τ₃≈τ₄)))

∙-assoc :
  ∀ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) (τ₃ : Type fℓ₃ lℓ₃) → (τ₁ ∙ τ₂) ∙ τ₃ ≈ τ₁ ∙ (τ₂ ∙ τ₃)
∙-assoc τ₁ τ₂ τ₃ = record
  { n≡n   = ∧-assoc τ₁.null τ₂.null τ₃.null
  ; f₁⊆f₂ =
    [ [ inj₁ , (inj₂ ∘ ⇒ᵗ-monoʳ τ₁.null inj₁) ]′
    , inj₂ ∘ ⇒ᵗ-monoʳ τ₁.null inj₂ ∘ ⇒ᵗ-∧ τ₁.null τ₂.null τ₃.first
    ]′
  ; f₁⊇f₂ =
    [ inj₁ ∘ inj₁
    , [ inj₁ ∘ inj₂ , inj₂ ∘ ⇒ᵗ-∧′ τ₁.null τ₂.null τ₃.first ]′ ∘
      ⇒ᵗ-⊎ τ₁.null τ₂.first (τ₂.null ⇒ᵗ τ₃.first)
    ]′
  ; l₁⊆l₂ =
    [ inj₁ ∘ inj₁
    , [ inj₁ ∘ inj₂ ∘ ⇒ᵗ-monoʳ τ₃.null inj₁
      , [ inj₁ ∘ inj₂ ∘ ⇒ᵗ-monoʳ τ₃.null inj₂
        , inj₂ ∘
          ⇒ᵗ-mono (≤ᵇ-reflexive (∧-comm τ₃.null τ₂.null)) (map inj₁ id) ∘
          ⇒ᵗ-∧′ τ₃.null τ₂.null (λ c → τ₂.first c ⊎ τ₁.flast c)
        ]′ ∘
        ⇒ᵗ-⊎ τ₃.null τ₂.flast (τ₂.null ⇒ᵗ λ c → τ₂.first c ⊎ τ₁.flast c)
      ]′ ∘
      ⇒ᵗ-⊎ τ₃.null τ₃.first (λ c → τ₂.flast c ⊎ (τ₂.null ⇒ᵗ λ c → τ₂.first c ⊎ τ₁.flast c) c)
    ]′
  ; l₁⊇l₂ =
    [ [ inj₁
      , inj₂ ∘
        [ ⇒ᵗ-monoʳ τ₃.null inj₁
        , ⇒ᵗ-monoʳ τ₃.null (inj₂ ∘ inj₁)
        ]′ ∘
        ⇒ᵗ-⊎ τ₃.null τ₃.first τ₂.flast
      ]′
    , inj₂ ∘
      [ [ ⇒ᵗ-monoʳ τ₃.null (inj₂ ∘ inj₂) ∘
          ⇒ᵗ-∧ τ₃.null τ₂.null (λ c → τ₂.first c ⊎ τ₁.flast c) ∘
          ⇒ᵗ-mono (≤ᵇ-reflexive (∧-comm τ₂.null τ₃.null)) inj₁
        , ⇒ᵗ-monoʳ τ₃.null (inj₁ ∘ ⇒ᵗA⊆A τ₂.null τ₃.first ∘ ⇒ᵗ-idemˡ τ₂.null τ₃.first) ∘
          ⇒ᵗ-∧ τ₃.null τ₂.null (τ₂.null ⇒ᵗ τ₃.first) ∘
          ⇒ᵗ-monoˡ (τ₂.null ⇒ᵗ τ₃.first) (≤ᵇ-reflexive (∧-comm τ₂.null τ₃.null))
        ]′ ∘
        ⇒ᵗ-⊎ (τ₂.null ∧ τ₃.null) τ₂.first (τ₂.null ⇒ᵗ τ₃.first)
      , ⇒ᵗ-monoʳ τ₃.null (inj₂ ∘ inj₂) ∘
        ⇒ᵗ-∧ τ₃.null τ₂.null (λ c → τ₂.first c ⊎ τ₁.flast c) ∘
        ⇒ᵗ-mono (≤ᵇ-reflexive (∧-comm τ₂.null τ₃.null)) inj₂
      ]′ ∘
      ⇒ᵗ-⊎ (τ₂.null ∧ τ₃.null) (λ c → τ₂.first c ⊎ (τ₂.null ⇒ᵗ τ₃.first) c) τ₁.flast
    ]′
  }
  where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂
  module τ₃ = Type τ₃

¬∙-identityˡ : C → Σ (Type ℓ lℓ₁) λ τ′ → (∀ (τ : Type fℓ₂ lℓ₂) → τ ∙ τ′ ≉ τ′)
¬∙-identityˡ {fℓ₂ = fℓ₂} {lℓ₂} c = τ′ , go
  where
    τ′ = record
      { null       = true
      ; first      = c ∼_
      ; flast      = const ⊥
      ; first-cong = flip ∼-trans
      ; flast-cong = λ _ ()
      }

    go : ∀ (τ : Type fℓ₂ lℓ₂) → τ ∙ τ′ ≉ τ′
    go record { null = true } τ∙τ′≈τ′ = lower (l₁⊆l₂ (inj₂ (inj₁ ∼-refl)))
      where open _≈_ τ∙τ′≈τ′

∙-identityʳ : ∀ (τ : Type fℓ₁ lℓ₁) → τ ∙ τε {fℓ₂} {lℓ₂} ≈ τ
∙-identityʳ τ = record
  { n≡n   = ∧-identityʳ null
  ; f₁⊆f₂ = [ id , ⊥-elim ∘ ⇒ᵗ-zeroʳ null (λ ()) ]′
  ; f₁⊇f₂ = inj₁
  ; l₁⊆l₂ = [ (λ ()) , [ (λ ()) , id ]′ ]′
  ; l₁⊇l₂ = inj₂ ∘ inj₂
  }
  where open Type τ

¬∙-zeroˡ :
  ∀ {c : C} (τ : Type fℓ₁ lℓ₁) → Dec (Type.flast τ c) → Σ (Type fℓ₂ (ℓ ⊔ lℓ₁)) λ τ′ → τ ∙ τ′ ≉ τ
¬∙-zeroˡ {c = c} τ c∈?l = τ′ , go
  where
    open Type τ
    τ′ = record
      { null       = false
      ; first      = const ⊥
      ; flast      = λ c′ → ¬ c ∼ c′ × flast c′ ⊎ c ∼ c′ × ¬ flast c′
      ; first-cong = λ _ ()
      ; flast-cong = λ
        { x∼y (inj₁ (c≁x , x∈l)) → inj₁ (c≁x ∘ flip ∼-trans (∼-sym x∼y) , flast-cong x∼y x∈l)
        ; x∼y (inj₂ (c∼x , x∉l)) → inj₂ (∼-trans c∼x x∼y , x∉l ∘ flast-cong (∼-sym x∼y))
        }
      }
    go : τ ∙ τ′ ≉ τ
    go τ∙τ′≈τ = case c∈?l of λ
      { (yes c∈l) → [ [ (∼-refl |>_) ∘ proj₁ , (c∈l |>_) ∘ proj₂ ]′ , lower ]′ (l₁⊇l₂ c∈l)
      ; (no c∉l)  → c∉l (l₁⊆l₂ (inj₁ (inj₂ (∼-refl , c∉l))))
      }
      where open _≈_ τ∙τ′≈τ

¬∙-zeroʳ :
  ∀ {c : C} (τ : Type fℓ₁ lℓ₁) → Dec (Type.first τ c) → Σ (Type (ℓ ⊔ fℓ₁) lℓ₂) λ τ′ → τ′ ∙ τ ≉ τ
¬∙-zeroʳ {c = c} τ c∈?f = τ′ , go
  where
    open Type τ
    τ′ = record
      { null       = false
      ; first      = λ c′ → ¬ c ∼ c′ × first c′ ⊎ c ∼ c′ × ¬ first c′
      ; flast      = const ⊥
      ; first-cong = λ
        { x∼y (inj₁ (c≁x , x∈l)) → inj₁ (c≁x ∘ flip ∼-trans (∼-sym x∼y) , first-cong x∼y x∈l)
        ; x∼y (inj₂ (c∼x , x∉l)) → inj₂ (∼-trans c∼x x∼y , x∉l ∘ first-cong (∼-sym x∼y))
        }
      ; flast-cong = λ _ ()
      }
    go : τ′ ∙ τ ≉ τ
    go τ′∙τ≈τ = case c∈?f of λ
      { (yes c∈f) → [ [ (∼-refl |>_) ∘ proj₁ , (c∈f |>_) ∘ proj₂ ]′ , lower ]′ (f₁⊇f₂ c∈f)
      ; (no c∉f)  → c∉f (f₁⊆f₂ (inj₁ (inj₂ (∼-refl , c∉f))))
      }
      where open _≈_ τ′∙τ≈τ

∙-addˡ-⊛ˡ :
  ∀ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) (τ₃ : Type fℓ₃ lℓ₃) → τ₂ ⊛ τ₃ → τ₁ ∙ τ₂ ⊛ τ₃
∙-addˡ-⊛ˡ τ₁ τ₂ τ₃ τ₂⊛τ₃ = record
  { ∄[l₁∩f₂] = λ
    { (inj₁ c∈l₂   , c∈f₃) → ∄[l₂∩f₃] (c∈l₂ , c∈f₃)
    ; (inj₂ c∈n₂⇒A , c∈f₃) → ¬n₂ (⇒ᵗ-contra τ₂.null (λ c → τ₂.first c ⊎ τ₁.flast c) c∈n₂⇒A)
    }
  ; ¬n₁      = ¬n₂ ∘ proj₂ ∘ (Equivalence.to T-∧ ⟨$⟩_)
  }
  where
  open _⊛_ τ₂⊛τ₃ using () renaming (∄[l₁∩f₂] to ∄[l₂∩f₃]; ¬n₁ to ¬n₂)
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂

∙-cancelʳ-⊛ʳ :
  ∀ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) (τ₃ : Type fℓ₃ lℓ₃) → τ₁ ⊛ τ₂ ∙ τ₃ → τ₁ ⊛ τ₂
∙-cancelʳ-⊛ʳ _ _ _ τ₁⊛τ₂∙τ₃ = record
  { ∄[l₁∩f₂] = λ (c∈l₁ , c∈f₂) → ∄[l₁∩f₂] (c∈l₁ , inj₁ c∈f₂)
  ; ¬n₁      = ¬n₁
  }
  where open _⊛_ τ₁⊛τ₂∙τ₃

------------------------------------------------------------------------
-- Structures

∙-isMagma : ∀ {fℓ} {lℓ} → IsMagma _≈_ (_∙_ {fℓ} {fℓ ⊔ lℓ})
∙-isMagma = record
  { isEquivalence = ≈-isEquivalence
  ; ∙-cong        = ∙-cong
  }

∙-isSemigroup : ∀ {fℓ} {lℓ} → IsSemigroup _≈_ (_∙_ {fℓ} {fℓ ⊔ lℓ})
∙-isSemigroup {fℓ} {lℓ} = record
  { isMagma = ∙-isMagma {fℓ} {lℓ}
  ; assoc   = ∙-assoc
  }

------------------------------------------------------------------------
-- Bundles

∙-magma : ∀ {fℓ} {lℓ} → Magma _ _
∙-magma {fℓ} {lℓ} = record { isMagma = ∙-isMagma {fℓ} {lℓ} }

∙-semigroup : ∀ {fℓ} {lℓ} → Semigroup _ _
∙-semigroup {fℓ} {lℓ} = record { isSemigroup = ∙-isSemigroup {fℓ} {lℓ} }

------------------------------------------------------------------------
-- Other properties

⊛⇒∙-pres-⊨ : τ₁ ⊛ τ₂ → A ⊨ τ₁ → B ⊨ τ₂ → A ∙ˡ B ⊨ τ₁ ∙ τ₂
⊛⇒∙-pres-⊨ {τ₁ = τ₁} {τ₂ = τ₂} {A = A} {B = B} τ₁⊛τ₂ A⊨τ₁ B⊨τ₂ = record
  { n⇒n =  (Equivalence.from T-∧ ⟨$⟩_) ∘ < A⊨τ₁.n⇒n ∘ ε∈A∙B⇒ε∈A A B , B⊨τ₂.n⇒n ∘ ε∈A∙B⇒ε∈B A B >
  ; f⇒f = λ c∈First[A∙B] →
    map
      A⊨τ₁.f⇒f
      (uncurry ⇒ᵗ-construct ∘ mapᵖ A⊨τ₁.n⇒n B⊨τ₂.f⇒f)
      (c∈First[A∙B]⇒c∈First[A]⊎ε∈A+c∈First[B] A B c∈First[A∙B])
  ; l⇒l = l⇒l
  }
  where
  module ≋-setoid = Setoid (Pw.setoid over)
  open import Relation.Binary.Reasoning.Setoid (Pw.setoid over)
  open _⊛_ τ₁⊛τ₂
  module A = Language A
  module B = Language B
  module A⊨τ₁ = _⊨_ A⊨τ₁
  module B⊨τ₂ = _⊨_ B⊨τ₂

  l⇒l : ∀ {c} → Flast (A ∙ˡ B) c → Type.flast (τ₁ ∙ τ₂) c
  l⇒l (_ , _ , _ , _ , [] , _ , ε∈A , _) = ⊥-elim (¬n₁ (A⊨τ₁.n⇒n ε∈A))
  l⇒l (_ , _ , ([] , _ , ε∈A , _) , _ , _ ∷ _ , _)   = ⊥-elim (¬n₁ (A⊨τ₁.n⇒n ε∈A))
  l⇒l {c} (x , w , (y ∷ w₁ , w₂ , yw₁∈A , w₂∈B , eq₁) , w′ , z ∷ w₁′ , w₂′ , zw₁′∈A , w₂′∈B , eq₂) with
    compare (y ∷ w₁) (w₂ ++ c ∷ w′) (z ∷ w₁′) w₂′ (begin
        y ∷ w₁ ++ w₂ ++ c ∷ w′   ≡˘⟨ ++-assoc (y ∷ w₁) w₂ (c ∷ w′) ⟩
        (y ∷ w₁ ++ w₂) ++ c ∷ w′ ≈⟨ ++⁺ eq₁ (Pw.refl ∼-refl) ⟩
        x ∷ w ++ c ∷ w′          ≈˘⟨ eq₂ ⟩
        (z ∷ w₁′) ++ w₂′         ∎)
  ... | cmp with <?> cmp
  ... | tri< l _ _ =
    ⊥-elim (∄[l₁∩f₂]
      ( A⊨τ₁.l⇒l (-, -, zw₁′∈A , -, A.∈-resp-≋ w₁≋zw₁′cw′′ yw₁∈A)
      , B⊨τ₂.f⇒f (-, B.∈-resp-≋ w₂′≋yw′′′ w₂′∈B)
      ))
    where
    lsplit      = left-split cmp l
    w₁≋zw₁′cw′′ = proj₁ (proj₂ (proj₂ lsplit))
    w₂′≋yw′′′   = ≋-setoid.sym (proj₂ (proj₂ (proj₂ lsplit)))
  l⇒l {c} (_ , _ , (_ ∷ _ , [] , w₁∈A , ε∈B , _) , w′ , z ∷ w₁′ , [] , zw₁′∈A , _) | cmp | tri≈ _ e _ =
    inj₂ (⇒ᵗ-construct
      (B⊨τ₂.n⇒n ε∈B)
      (inj₂ (A⊨τ₁.l⇒l (-, -, A.∈-resp-≋ w₁≋zw₁′ w₁∈A , -, A.∈-resp-≋ zw₁′≋zw₁′cw′ zw₁′∈A))))
    where
    esplit = eq-split cmp e
    w₁≋zw₁′ = proj₁ esplit
    zw₁′≋zw₁′cw′ = begin
      z ∷ w₁′           ≡˘⟨ ++-identityʳ (z ∷ w₁′) ⟩
      z ∷ w₁′ ++ []     ≈˘⟨ ++⁺ (Pw.refl ∼-refl) (proj₂ esplit) ⟩
      z ∷ w₁′ ++ c ∷ w′ ∎
  l⇒l (_ , _ , (_ ∷ _ , [] , _ , ε∈B , _) , _ , _ ∷ _ , y ∷ w₂′ , _ , yw₂′∈B , _) | cmp | tri≈ _ e _ =
    inj₂ (⇒ᵗ-construct (B⊨τ₂.n⇒n ε∈B) (inj₁ (B⊨τ₂.f⇒f (-, B.∈-resp-≋ yw₂′≋cw′ yw₂′∈B))))
    where
    esplit = eq-split cmp e
    yw₂′≋cw′ = ≋-setoid.sym (proj₂ esplit)
  l⇒l {c} (_ , _ , (_ ∷ _ , _ ∷ _ , _ , yw₂∈B , _) , _ , _ ∷ _ , _ , _ , w₂′∈B , _) | cmp | tri≈ _ e _ =
    inj₁ (B⊨τ₂.l⇒l (-, -, yw₂∈B , -, B.∈-resp-≋ w₂′≋yw₂cw′ w₂′∈B))
    where
    esplit = eq-split cmp e
    w₂′≋yw₂cw′ = ≋-setoid.sym (proj₂ esplit)
  l⇒l {c} (x , w , (y ∷ w₁ , [] , yw₁∈A , ε∈B , eq₁) , w′ , z ∷ w₁′ , w₂′ , zw₁′∈A , w₂′∈B , eq₂) | cmp | tri> _ _ r =
    inj₂ (⇒ᵗ-construct
      (B⊨τ₂.n⇒n ε∈B)
      (inj₂ (A⊨τ₁.l⇒l (-, -, A.∈-resp-≋ yw₁≋xw yw₁∈A , -, A.∈-resp-≋ zw₁′≋xwcw′′ zw₁′∈A))))
    where
    rsplit = right-split cmp r
    c′ = proj₁ rsplit
    w′′ = proj₁ (proj₂ rsplit)
    c∼c′ = case proj₂ (proj₂ (proj₂ rsplit)) of λ {(c∼c′ ∷ _) → c∼c′}
    yw₁≋xw = begin
      y ∷ w₁       ≡˘⟨ ++-identityʳ (y ∷ w₁) ⟩
      y ∷ w₁ ++ [] ≈⟨ eq₁ ⟩
      x ∷ w        ∎
    zw₁′≋xwcw′′ = begin
      z ∷ w₁′            ≈˘⟨ proj₁ (proj₂ (proj₂ rsplit)) ⟩
      y ∷ w₁ ++ c′ ∷ w′′ ≈⟨ ++⁺ yw₁≋xw (∼-sym c∼c′ ∷ Pw.refl ∼-refl) ⟩
      x ∷ w ++ c ∷ w′′ ∎
  l⇒l {c} (x , w , (y ∷ w₁ , y′ ∷ w₂ , yw₁∈A , y′w₂∈B , eq₁) , w′ , z ∷ w₁′ , w₂′ , zw₁′∈A , w₂′∈B , eq₂) | cmp | tri> _ _ r =
    ⊥-elim (∄[l₁∩f₂]
      ( A⊨τ₁.l⇒l (-, -, yw₁∈A , -, A.∈-resp-≋ zw₁′≋yw₁y′w′′ zw₁′∈A)
      , B⊨τ₂.f⇒f (-, y′w₂∈B)
      ))
    where
    rsplit = right-split cmp r
    u = proj₁ rsplit
    w′′ = proj₁ (proj₂ rsplit)
    y′∼u = case (proj₂ (proj₂ (proj₂ rsplit))) of λ {(y′∼u ∷ _) → y′∼u}
    zw₁′≋yw₁y′w′′ = begin
      z ∷ w₁′            ≈˘⟨ proj₁ (proj₂ (proj₂ rsplit)) ⟩
      y ∷ w₁ ++ u ∷ w′′  ≈˘⟨ ++⁺ (∼-refl ∷ Pw.refl ∼-refl) (y′∼u ∷ Pw.refl ∼-refl) ⟩
      y ∷ w₁ ++ y′ ∷ w′′ ∎

------------------------------------------------------------------------
-- Properties of _∨_
------------------------------------------------------------------------
-- Algebraic Properties

∨-mono : τ₁ ≤ τ₂ → τ₃ ≤ τ₄ → τ₁ ∨ τ₃ ≤ τ₂ ∨ τ₄
∨-mono τ₁≤τ₂ τ₃≤τ₄ = record
  { n≤n = ∨ᵇ-mono τ₁≤τ₂.n≤n τ₃≤τ₄.n≤n
  ; f⊆f = map τ₁≤τ₂.f⊆f τ₃≤τ₄.f⊆f
  ; l⊆l = map τ₁≤τ₂.l⊆l τ₃≤τ₄.l⊆l
  }
  where
  module τ₁≤τ₂ = _≤_ τ₁≤τ₂
  module τ₃≤τ₄ = _≤_ τ₃≤τ₄

∨-cong : τ₁ ≈ τ₂ → τ₃ ≈ τ₄ → τ₁ ∨ τ₃ ≈ τ₂ ∨ τ₄
∨-cong τ₁≈τ₂ τ₃≈τ₄ =
  ≤-antisym
    (∨-mono (≤-reflexive τ₁≈τ₂) (≤-reflexive τ₃≈τ₄))
    (∨-mono (≤-reflexive (≈-sym τ₁≈τ₂)) (≤-reflexive (≈-sym τ₃≈τ₄)))

∨-assoc :
  ∀ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) (τ₃ : Type fℓ₃ lℓ₃) → (τ₁ ∨ τ₂) ∨ τ₃ ≈ τ₁ ∨ (τ₂ ∨ τ₃)
∨-assoc τ₁ τ₂ τ₃ = record
  { n≡n   = ∨ᵇ-assoc τ₁.null τ₂.null τ₃.null
  ; f₁⊆f₂ = [ [ inj₁ , inj₂ ∘ inj₁ ]′ , inj₂ ∘ inj₂ ]′
  ; f₁⊇f₂ = [ inj₁ ∘ inj₁ , [ inj₁ ∘ inj₂ , inj₂ ]′ ]′
  ; l₁⊆l₂ = [ [ inj₁ , inj₂ ∘ inj₁ ]′ , inj₂ ∘ inj₂ ]′
  ; l₁⊇l₂ = [ inj₁ ∘ inj₁ , [ inj₁ ∘ inj₂ , inj₂ ]′ ]′
  }
  where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂
  module τ₃ = Type τ₃

∨-comm : ∀ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) → τ₁ ∨ τ₂ ≈ τ₂ ∨ τ₁
∨-comm τ₁ τ₂ = record
  { n≡n   = ∨ᵇ-comm τ₁.null τ₂.null
  ; f₁⊆f₂ = [ inj₂ , inj₁ ]′
  ; f₁⊇f₂ = [ inj₂ , inj₁ ]′
  ; l₁⊆l₂ = [ inj₂ , inj₁ ]′
  ; l₁⊇l₂ = [ inj₂ , inj₁ ]′
  }
  where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂

∨-identityˡ : ∀ (τ : Type fℓ₁ lℓ₁) → τ⊥ {fℓ₂} {lℓ₂} ∨ τ ≈ τ
∨-identityˡ τ = record
  { n≡n   = ∨ᵇ-identityˡ null
  ; f₁⊆f₂ = [ (λ ()) , id ]′
  ; f₁⊇f₂ = inj₂
  ; l₁⊆l₂ = [ (λ ()) , id ]′
  ; l₁⊇l₂ = inj₂
  }
  where open Type τ

∨-identityʳ : ∀ (τ : Type fℓ₁ lℓ₁) → τ ∨ τ⊥ {fℓ₂} {lℓ₂} ≈ τ
∨-identityʳ τ = record
  { n≡n   = ∨ᵇ-identityʳ null
  ; f₁⊆f₂ = [ id , (λ ()) ]′
  ; f₁⊇f₂ = inj₁
  ; l₁⊆l₂ = [ id , (λ ()) ]′
  ; l₁⊇l₂ = inj₁
  }
  where open Type τ

∨-identity :
  (∀ (τ : Type fℓ₁ lℓ₁) → τ⊥ {fℓ₂} {lℓ₂} ∨ τ ≈ τ) × (∀ (τ : Type fℓ₁ lℓ₁) → τ ∨ τ⊥ {fℓ₂} {lℓ₂} ≈ τ)
∨-identity = ∨-identityˡ , ∨-identityʳ

∙-distribʳ-∨ :
  ∀ (τ₁ : Type fℓ₁ lℓ₁) (τ₂ : Type fℓ₂ lℓ₂) (τ₃ : Type fℓ₃ lℓ₃) →
  (τ₂ ∨ τ₃) ∙ τ₁ ≈ τ₂ ∙ τ₁ ∨ τ₃ ∙ τ₁
∙-distribʳ-∨ τ₁ τ₂ τ₃ = record
  { n≡n   = ∧-distribʳ-∨ τ₁.null τ₂.null τ₃.null
  ; f₁⊆f₂ = [ map inj₁ inj₁ , map inj₂ inj₂ ∘ ⇒ᵗ-∨ᵇ τ₂.null τ₃.null τ₁.first ]′
  ; f₁⊇f₂ =
    [ [ inj₁ ∘ inj₁ , inj₂ ∘ ⇒ᵗ-∨ᵇ′ˡ τ₂.null τ₃.null τ₁.first ]′
    , [ inj₁ ∘ inj₂ , inj₂ ∘ ⇒ᵗ-∨ᵇ′ʳ τ₂.null τ₃.null τ₁.first ]′
    ]′
  ; l₁⊆l₂ =
    [ inj₁ ∘ inj₁
    , [ inj₁ ∘ inj₂ ∘ ⇒ᵗ-monoʳ τ₁.null inj₁
      , map (inj₂ ∘ ⇒ᵗ-monoʳ τ₁.null inj₂) (inj₂ ∘ ⇒ᵗ-monoʳ τ₁.null inj₂) ∘
        ⇒ᵗ-⊎ τ₁.null τ₂.flast τ₃.flast
      ]′ ∘
      ⇒ᵗ-⊎ τ₁.null τ₁.first (λ c → τ₂.flast c ⊎ τ₃.flast c)
    ]′
  ; l₁⊇l₂ =
    [ map id
          ( [ ⇒ᵗ-monoʳ τ₁.null inj₁ , ⇒ᵗ-monoʳ τ₁.null (inj₂ ∘ inj₁) ]′ ∘
            ⇒ᵗ-⊎ τ₁.null τ₁.first τ₂.flast
          )
    , map id
          ( [ ⇒ᵗ-monoʳ τ₁.null inj₁ , ⇒ᵗ-monoʳ τ₁.null (inj₂ ∘ inj₂) ]′ ∘
            ⇒ᵗ-⊎ τ₁.null τ₁.first τ₃.flast
          )
    ]′
  }
  where
  module τ₁ = Type τ₁
  module τ₂ = Type τ₂
  module τ₃ = Type τ₃

∨-idem : ∀ (τ : Type fℓ lℓ) → τ ∨ τ ≈ τ
∨-idem τ = record
  { n≡n   = ∨ᵇ-idem null
  ; f₁⊆f₂ = reduce
  ; f₁⊇f₂ = inj₁
  ; l₁⊆l₂ = reduce
  ; l₁⊇l₂ = inj₁
  }
  where open Type τ

------------------------------------------------------------------------
-- Structures

∨-isMagma : IsMagma _≈_ (_∨_ {fℓ} {lℓ})
∨-isMagma = record
  { isEquivalence = ≈-isEquivalence
  ; ∙-cong        = ∨-cong
  }

∨-isCommutativeMagma : IsCommutativeMagma _≈_ (_∨_ {fℓ} {lℓ})
∨-isCommutativeMagma = record
  { isMagma = ∨-isMagma
  ; comm    = ∨-comm
  }

∨-isSemigroup : IsSemigroup _≈_ (_∨_ {fℓ} {lℓ})
∨-isSemigroup = record
  { isMagma = ∨-isMagma
  ; assoc   = ∨-assoc
  }

∨-isBand : IsBand _≈_ (_∨_ {fℓ} {lℓ})
∨-isBand = record
  { isSemigroup = ∨-isSemigroup
  ; idem        = ∨-idem
  }

∨-isCommutativeSemigroup : IsCommutativeSemigroup _≈_ (_∨_ {fℓ} {lℓ})
∨-isCommutativeSemigroup = record
  { isSemigroup = ∨-isSemigroup
  ; comm        = ∨-comm
  }

∨-isSemilattice : IsSemilattice _≈_ (_∨_ {fℓ} {lℓ})
∨-isSemilattice = record
  { isBand = ∨-isBand
  ; comm   = ∨-comm
  }

∨-isMonoid : IsMonoid _≈_ (_∨_ {fℓ} {lℓ}) τ⊥
∨-isMonoid = record
  { isSemigroup = ∨-isSemigroup
  ; identity    = ∨-identity
  }

∨-isCommutativeMonoid : IsCommutativeMonoid _≈_ (_∨_ {fℓ} {lℓ}) τ⊥
∨-isCommutativeMonoid = record
  { isMonoid = ∨-isMonoid
  ; comm     = ∨-comm
  }

∨-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _≈_ (_∨_ {fℓ} {lℓ}) τ⊥
∨-isIdempotentCommutativeMonoid = record
  { isCommutativeMonoid = ∨-isCommutativeMonoid
  ; idem                = ∨-idem
  }

------------------------------------------------------------------------
-- Bundles

∨-magma : ∀ {fℓ} {lℓ} → Magma _ _
∨-magma {fℓ} {lℓ} = record { isMagma = ∨-isMagma {fℓ} {lℓ} }

∨-commutativeMagma : ∀ {fℓ} {lℓ} → CommutativeMagma _ _
∨-commutativeMagma {fℓ} {lℓ} = record { isCommutativeMagma = ∨-isCommutativeMagma {fℓ} {lℓ} }

∨-semigroup : ∀ {fℓ} {lℓ} → Semigroup _ _
∨-semigroup {fℓ} {lℓ} = record { isSemigroup = ∨-isSemigroup {fℓ} {lℓ} }

∨-band : ∀ {fℓ} {lℓ} → Band _ _
∨-band {fℓ} {lℓ} = record { isBand = ∨-isBand {fℓ} {lℓ} }

∨-commutativeSemigroup : ∀ {fℓ} {lℓ} → CommutativeSemigroup _ _
∨-commutativeSemigroup {fℓ} {lℓ} = record { isCommutativeSemigroup = ∨-isCommutativeSemigroup {fℓ} {lℓ} }

∨-semilattice : ∀ {fℓ} {lℓ} → Semilattice _ _
∨-semilattice {fℓ} {lℓ} = record { isSemilattice = ∨-isSemilattice {fℓ} {lℓ} }

∨-monoid : ∀ {fℓ} {lℓ} → Monoid _ _
∨-monoid {fℓ} {lℓ} = record { isMonoid = ∨-isMonoid {fℓ} {lℓ} }

∨-commutativeMonoid : ∀ {fℓ} {lℓ} → CommutativeMonoid _ _
∨-commutativeMonoid {fℓ} {lℓ} = record { isCommutativeMonoid = ∨-isCommutativeMonoid {fℓ} {lℓ} }

∨-idempotentCommutativeMonoid : ∀ {fℓ} {lℓ} → IdempotentCommutativeMonoid _ _
∨-idempotentCommutativeMonoid {fℓ} {lℓ} = record
  { isIdempotentCommutativeMonoid = ∨-isIdempotentCommutativeMonoid {fℓ} {lℓ} }

------------------------------------------------------------------------
-- Other properties

#⇒∨-pres-⊨ : τ₁ # τ₂ → A ⊨ τ₁ → B ⊨ τ₂ → A ∪ B ⊨ τ₁ ∨ τ₂
#⇒∨-pres-⊨ τ₁#τ₂ A⊨τ₁ B⊨τ₂ = record
  { n⇒n = (Equivalence.from T-∨ ⟨$⟩_) ∘ map A⊨τ₁.n⇒n B⊨τ₂.n⇒n
  ; f⇒f = map A⊨τ₁.f⇒f B⊨τ₂.f⇒f ∘ uncurry λ w → [ inj₁ ∘ (w ,_) , inj₂ ∘ (w ,_) ]′
  ; l⇒l =
    map A⊨τ₁.l⇒l B⊨τ₂.l⇒l ∘
    uncurry λ _ → uncurry λ _ → uncurry
      [ inj₁ ∘₂ (λ xw∈A → uncurry λ _ →
        [ -,_ ∘ -,_ ∘ (xw∈A ,_) ∘ -,_
        , ⊥-elim ∘ ∄[f₁∩f₂] ∘ (A⊨τ₁.f⇒f (-, xw∈A) ,_) ∘ B⊨τ₂.f⇒f ∘ -,_
        ]′)
      , inj₂ ∘₂ (λ xw∈B → uncurry λ _ →
        [ (⊥-elim ∘ ∄[f₁∩f₂] ∘ (_, B⊨τ₂.f⇒f (-, xw∈B)) ∘ A⊨τ₁.f⇒f ∘ -,_)
        , -,_ ∘ -,_ ∘ (xw∈B ,_) ∘ -,_
        ]′)
      ]′
  }
  where
  open _#_ τ₁#τ₂
  module A⊨τ₁ = _⊨_ A⊨τ₁
  module B⊨τ₂ = _⊨_ B⊨τ₂
