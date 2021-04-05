{-# OPTIONS --without-K --safe #-}

open import Relation.Binary hiding (Decidable; Irrelevant; Recomputable)

module Cfe.Language.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C; _≈_ to _∼_; refl to ∼-refl)

open import Algebra
open import Cfe.Function.Power
open import Cfe.Language.Base over
open import Cfe.List.Compare over
open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
open import Data.List as L
open import Data.List.Properties
open import Data.List.Relation.Binary.Equality.Setoid over
import Data.List.Relation.Unary.Any as Any
import Data.Nat as ℕ
open import Data.Product as P
open import Data.Sum as S
open import Function hiding (_⟶_)
open import Level renaming (suc to lsuc)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality hiding (setoid; [_])
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Decidable
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)

private
  variable
    a b d ℓ₁ ℓ₂ : Level
    A X : Language b
    B Y : Language d
    U Z : Language ℓ₁
    V : Language ℓ₂
    F : Language a → Language a
    G : Language b → Language b

  w++[]≋w : ∀ w → w ++ [] ≋ w
  w++[]≋w [] = []
  w++[]≋w (x ∷ w) = ∼-refl ∷ w++[]≋w w

------------------------------------------------------------------------
-- Properties of _⊆_
------------------------------------------------------------------------
-- Relational properties of _⊆_

⊆-refl : Reflexive (_⊆_ {a})
⊆-refl = sub id

⊆-reflexive : (_≈_ {a} {b}) ⇒ _⊆_
⊆-reflexive = proj₁

⊇-reflexive : (_≈_ {a} {b}) ⇒ flip _⊆_
⊇-reflexive = proj₂

⊆-trans : Trans (_⊆_ {a}) (_⊆_ {b} {d}) _⊆_
⊆-trans (sub A⊆B) (sub B⊆C) = sub (B⊆C ∘ A⊆B)

⊆-antisym : Antisym (_⊆_ {a} {b}) _⊆_ _≈_
⊆-antisym = _,_

------------------------------------------------------------------------
-- Membership properties of _⊆_

∈-resp-⊆ : ∀ {w} → (w ∈_) ⟶ (w ∈_) Respects (_⊆_ {a} {b})
∈-resp-⊆ (sub A⊆B) = A⊆B

∉-resp-⊇ : ∀ {w} → (w ∉_) ⟶ (w ∉_) Respects flip (_⊆_ {b} {a})
∉-resp-⊇ (sub A⊇B) w∉A = w∉A ∘ A⊇B

Null-resp-⊆ : Null {a} ⟶ Null {b} Respects _⊆_
Null-resp-⊆ = ∈-resp-⊆

First-resp-⊆ : ∀ {c} → flip (First {a}) c ⟶ flip (First {a}) c Respects _⊆_
First-resp-⊆ (sub A⊆B) = P.map₂ A⊆B

Flast-resp-⊆ : ∀ {c} → flip (Flast {a}) c ⟶ flip (Flast {a}) c Respects _⊆_
Flast-resp-⊆ (sub A⊆B) = P.map₂ (P.map₂ (P.map A⊆B (P.map₂ A⊆B)))

------------------------------------------------------------------------
-- Properties of _≈_
------------------------------------------------------------------------
-- Relational properties of _≈_

≈-refl : Reflexive (_≈_ {a})
≈-refl = ⊆-refl , ⊆-refl

≈-sym : Sym (_≈_ {a} {b}) _≈_
≈-sym = P.swap

≈-trans : Trans (_≈_ {a}) (_≈_ {b} {d}) _≈_
≈-trans = P.zip ⊆-trans (flip ⊆-trans)

------------------------------------------------------------------------
-- Structures

≈-isPartialEquivalence : IsPartialEquivalence (_≈_ {a})
≈-isPartialEquivalence = record
  { sym = ≈-sym
  ; trans = ≈-trans
  }

≈-isEquivalence : IsEquivalence (_≈_ {a})
≈-isEquivalence = record
  { refl = ≈-refl
  ; sym = ≈-sym
  ; trans = ≈-trans
  }

⊆-isPreorder : IsPreorder (_≈_ {a}) _⊆_
⊆-isPreorder = record
  { isEquivalence = ≈-isEquivalence
  ; reflexive = ⊆-reflexive
  ; trans = ⊆-trans
  }

⊆-isPartialOrder : IsPartialOrder (_≈_ {a}) _⊆_
⊆-isPartialOrder = record
  { isPreorder = ⊆-isPreorder
  ; antisym = ⊆-antisym
  }

------------------------------------------------------------------------
-- Bundles

partialSetoid : PartialSetoid (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a)
partialSetoid {a} = record { isPartialEquivalence = ≈-isPartialEquivalence {a} }

setoid : Setoid (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a)
setoid {a} = record { isEquivalence = ≈-isEquivalence {a} }

⊆-preorder : Preorder (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a)
⊆-preorder {a} = record { isPreorder = ⊆-isPreorder {a} }

⊆-poset : Poset (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a)
⊆-poset {a} = record { isPartialOrder = ⊆-isPartialOrder {a} }

------------------------------------------------------------------------
-- Membership properties of _≈_

∈-resp-≈ : ∀ {w} → (w ∈_) ⟶ (w ∈_) Respects (_≈_ {a} {b})
∈-resp-≈ = ∈-resp-⊆ ∘ ⊆-reflexive

∉-resp-≈ : ∀ {w} → (w ∉_) ⟶ (w ∉_) Respects flip (_≈_ {b} {a})
∉-resp-≈ = ∉-resp-⊇ ∘ ⊆-reflexive

Null-resp-≈ : Null {a} ⟶ Null {b} Respects _≈_
Null-resp-≈ = Null-resp-⊆ ∘ ⊆-reflexive

First-resp-≈ : ∀ {c} → flip (First {a}) c ⟶ flip (First {a}) c Respects _≈_
First-resp-≈ = First-resp-⊆ ∘ ⊆-reflexive

Flast-resp-≈ : ∀ {c} → flip (Flast {a}) c ⟶ flip (Flast {a}) c Respects _≈_
Flast-resp-≈ = Flast-resp-⊆ ∘ ⊆-reflexive

------------------------------------------------------------------------
-- Proof properties of _≈_

Decidable-resp-≈ : Decidable {a} ⟶ Decidable {b} Respects _≈_
Decidable-resp-≈ (sub A⊆B , sub A⊇B) A? l = map′ A⊆B A⊇B (A? l)

Recomputable-resp-≈ : Recomputable {a} ⟶ Recomputable {b} Respects _≈_
Recomputable-resp-≈ (sub A⊆B , sub A⊇B) recomp l∈B = A⊆B (recomp (A⊇B l∈B))

------------------------------------------------------------------------
-- Properties of ∅
------------------------------------------------------------------------
-- Algebraic properties of ∅

⊆-min : Min (_⊆_ {a} {b}) ∅
⊆-min _ = sub λ ()

------------------------------------------------------------------------
-- Membership properties of ∅

w∉∅ : ∀ w → w ∉ ∅ {a}
w∉∅ _ ()

ε∉∅ : ¬ Null {a} ∅
ε∉∅ ()

∄[First[∅]] : ∀ c → ¬ First {a} ∅ c
∄[First[∅]] _ ()

∄[Flast[∅]] : ∀ c → ¬ Flast {a} ∅ c
∄[Flast[∅]] _ ()

ε∉A+∄[First[A]]⇒A≈∅ : ¬ Null A → (∀ c → ¬ First A c) → A ≈ ∅ {a}
ε∉A+∄[First[A]]⇒A≈∅ {A = A} ε∉A cw∉A =
  ⊆-antisym
    (sub λ {w} w∈A → case ∃[ w ] w ∈ A ∋ w , w∈A of λ
      { ([]    ,  ε∈A) → lift (ε∉A ε∈A)
      ; (c ∷ w , cw∈A) → lift (cw∉A c (w , cw∈A))
      })
    (⊆-min A)

------------------------------------------------------------------------
-- Proof properties of ∅

∅? : Decidable (∅ {a})
∅? w = no λ ()

∅-irrelevant : Irrelevant (∅ {a})
∅-irrelevant ()

∅-recomputable : Recomputable (∅ {a})
∅-recomputable ()

------------------------------------------------------------------------
-- Properties of ｛ε｝
------------------------------------------------------------------------
-- Membership properties of ∅

ε∈｛ε｝ : Null (｛ε｝{a})
ε∈｛ε｝ = lift refl

∄[First[｛ε｝]] : ∀ c → ¬ First (｛ε｝ {a}) c
∄[First[｛ε｝]] _ ()

∄[Flast[｛ε｝]] : ∀ c → ¬ Flast (｛ε｝ {a}) c
∄[Flast[｛ε｝]] _ ()

∄[First[A]]⇒A⊆｛ε｝ : (∀ c → ¬ First A c) → A ⊆ ｛ε｝ {a}
∄[First[A]]⇒A⊆｛ε｝ {A = A} cw∉A =
  sub λ {w} w∈A → case ∃[ w ] w ∈ A ∋ w , w∈A return (λ (w , _) → w ∈ ｛ε｝) of λ
    { ([]    ,  w∈A) → lift refl
    ; (c ∷ w , cw∈A) → ⊥-elim (cw∉A c (w , cw∈A))
    }

------------------------------------------------------------------------
-- Proof properties of ｛ε｝

｛ε｝? : Decidable (｛ε｝ {a})
｛ε｝? []      = yes (lift refl)
｛ε｝? (_ ∷ _) = no λ ()

｛ε｝-irrelevant : Irrelevant (｛ε｝ {a})
｛ε｝-irrelevant (lift refl) (lift refl) = refl

｛ε｝-recomputable : Recomputable (｛ε｝ {a})
｛ε｝-recomputable {w = []} _ = lift refl

------------------------------------------------------------------------
-- Properties of ｛_｝
------------------------------------------------------------------------
-- Membership properties of ｛_｝

ε∉｛c｝ : ∀ c → ¬ Null ｛ c ｝
ε∉｛c｝ _ ()

c′∈First[｛c｝]⇒c∼c′ : ∀ {c c′} → First ｛ c ｝ c′ → c ∼ c′
c′∈First[｛c｝]⇒c∼c′ (_ , c∼c′ ∷ []) = c∼c′

c∼c′⇒c′∈｛c｝ : ∀ {c c′} → c ∼ c′ → [ c′ ] ∈ ｛ c ｝
c∼c′⇒c′∈｛c｝ c∼c′ = c∼c′ ∷ []

∄[Flast[｛c｝]] : ∀ {c} c′ → ¬ Flast ｛ c ｝ c′
∄[Flast[｛c｝]] _ (_ , _ , _ ∷ [] , _ , _ ∷ ())

xyw∉｛c｝ : ∀ c x y w → x ∷ y ∷ w ∉ ｛ c ｝
xyw∉｛c｝ c x y w (_ ∷ ())

------------------------------------------------------------------------
-- Properties of _∙_
------------------------------------------------------------------------
-- Membership properties of _∙_

-- Null

ε∈A⇒B⊆A∙B : ∀ (A : Language b) (B : Language d) → Null A → B ⊆ A ∙ B
ε∈A⇒B⊆A∙B _ _ ε∈A = sub λ w∈B → -, -, ε∈A , w∈B , ≋-refl

ε∈B⇒A⊆A∙B : ∀ (A : Language b) (B : Language d) → Null B → A ⊆ A ∙ B
ε∈B⇒A⊆A∙B _ _ ε∈B = sub λ {w} w∈A → -, -, w∈A , ε∈B , w++[]≋w w

ε∈A+ε∈B⇒ε∈A∙B : Null A → Null B → Null (A ∙ B)
ε∈A+ε∈B⇒ε∈A∙B ε∈A ε∈B = -, -, ε∈A , ε∈B , ≋-refl

ε∈A∙B⇒ε∈A : ∀ (A : Language b) (B : Language d) → Null (A ∙ B) → Null A
ε∈A∙B⇒ε∈A _ _ ([] , [] , ε∈A , ε∈B , []) = ε∈A

ε∈A∙B⇒ε∈B : ∀ (A : Language b) (B : Language d) → Null (A ∙ B) → Null B
ε∈A∙B⇒ε∈B _ _ ([] , [] , ε∈A , ε∈B , []) = ε∈B

-- First

c∈First[A]+w′∈B⇒c∈First[A∙B] : ∀ {c} → First A c → ∃[ w ] w ∈ B → First (A ∙ B) c
c∈First[A]+w′∈B⇒c∈First[A∙B] (_ , cw∈A) (_ , w′∈B) = -, -, -, cw∈A , w′∈B , ≋-refl

ε∈A+c∈First[B]⇒c∈First[A∙B] : ∀ {c} → Null A → First B c → First (A ∙ B) c
ε∈A+c∈First[B]⇒c∈First[A∙B] ε∈A (_ , cw∈B) = -, -, -, ε∈A , cw∈B , ≋-refl

-- Flast

c∈Flast[B]+w∈A⇒c∈Flast[A∙B] : ∀ {c} → Flast B c → ∃[ w ] w ∈ A → Flast (A ∙ B) c
c∈Flast[B]+w∈A⇒c∈Flast[A∙B]         (_ , _ ,  w∈B , _ ,  wcw′∈B) (       [] ,     ε∈A) =
  -, -, (-, -, ε∈A , w∈B , ≋-refl) , -, -, -, ε∈A , wcw′∈B , ≋-refl
c∈Flast[B]+w∈A⇒c∈Flast[A∙B] {c = c} (x , w , xw∈B , w′ , xwcw′∈B) (c′ ∷ w′′ , c′w′′∈A) =
  -, -, c′w′′xw∈A∙B , -, c′w′′xwcw′∈A∙B
  where
  c′w′′xw∈A∙B    = -, -, c′w′′∈A , xw∈B , ≋-refl
  c′w′′xwcw′∈A∙B = -, -, c′w′′∈A , xwcw′∈B , ∼-refl ∷ ≋-reflexive (sym (++-assoc w′′ (x ∷ w) (c ∷ w′)))

ε∈B+x∈First[A]+c∈First[B]⇒c∈Flast[A∙B] :
  ∀ {c} → Null B → ∃[ x ] First A x → First B c → Flast (A ∙ B) c
ε∈B+x∈First[A]+c∈First[B]⇒c∈Flast[A∙B] ε∈B (x , w , xw∈A) (_ , cw′∈B) = -, -, xw∈A∙B , -, xwcw′∈A∙B
  where
  xw∈A∙B    = -, -, xw∈A , ε∈B , w++[]≋w (x ∷ w)
  xwcw′∈A∙B = -, -, xw∈A , cw′∈B , ≋-refl

ε∈B+c∈Flast[A]⇒c∈Flast[A∙B] : ∀ {c} → Null B → Flast A c → Flast (A ∙ B) c
ε∈B+c∈Flast[A]⇒c∈Flast[A∙B] {c = c} ε∈B (x , w , xw∈A , w′ , xwcw′∈A) = -, -, xw∈A∙B , -, xwcw′∈A∙B
  where
  xw∈A∙B    = -, -, xw∈A , ε∈B , w++[]≋w (x ∷ w)
  xwcw′∈A∙B = -, -, xwcw′∈A , ε∈B , w++[]≋w (x ∷ w ++ c ∷ w′)

------------------------------------------------------------------------
-- Algebraic properties of _∙_

∙-mono : X ⊆ Y → U ⊆ V → X ∙ U ⊆ Y ∙ V
∙-mono (sub X⊆Y) (sub U⊆V) = sub λ (_ , _ , w₁∈X , w₂∈U , eq) → -, -, X⊆Y w₁∈X , U⊆V w₂∈U , eq

∙-cong : X ≈ Y → U ≈ V → X ∙ U ≈ Y ∙ V
∙-cong X≈Y U≈V = ⊆-antisym
  (∙-mono (⊆-reflexive X≈Y) (⊆-reflexive U≈V))
  (∙-mono (⊇-reflexive X≈Y) (⊇-reflexive U≈V))

∙-assoc : ∀ (A : Language a) (B : Language b) (C : Language d) → (A ∙ B) ∙ C ≈ A ∙ (B ∙ C)
∙-assoc A B C =
  (sub λ {w} (w₁w₂ , w₃ , (w₁ , w₂ , w₁∈A , w₂∈B , eq₁) , w₃∈C , eq₂) →
    -, -, w₁∈A , (-, -, w₂∈B , w₃∈C , ≋-refl) ,
      (begin
        w₁ ++ w₂ ++ w₃   ≡˘⟨ ++-assoc w₁ w₂ w₃ ⟩
        (w₁ ++ w₂) ++ w₃ ≈⟨ ++⁺ eq₁ ≋-refl ⟩
        w₁w₂ ++ w₃       ≈⟨ eq₂ ⟩
        w ∎)) ,
  (sub λ {w} (w₁ , w₂w₃ , w₁∈A , (w₂ , w₃ , w₂∈B , w₃∈C , eq₁) , eq₂) →
    -, -, (-, -, w₁∈A , w₂∈B , ≋-refl) , w₃∈C ,
      (begin
        (w₁ ++ w₂) ++ w₃ ≡⟨ ++-assoc w₁ w₂ w₃ ⟩
        w₁ ++ w₂ ++ w₃   ≈⟨ ++⁺ ≋-refl eq₁ ⟩
        w₁ ++ w₂w₃       ≈⟨ eq₂ ⟩
        w ∎))
  where
  open import Relation.Binary.Reasoning.Setoid ≋-setoid

∙-identityˡ : ∀ (A : Language a) → ｛ε｝ {b} ∙ A ≈ A
∙-identityˡ A =
  ⊆-antisym
    (sub λ { (_ , _ , lift refl , w′∈A , eq) → A.∈-resp-≋ eq w′∈A })
    (ε∈A⇒B⊆A∙B ｛ε｝ A ε∈｛ε｝)
  where
  module A = Language A

∙-identityʳ : ∀ (A : Language a) → A ∙ ｛ε｝ {b} ≈ A
∙-identityʳ X =
  ⊆-antisym
    (sub λ {w} → λ
      { (w′ , _ , w′∈X , lift refl , eq) →
        X.∈-resp-≋
          (begin
            w′       ≈˘⟨ w++[]≋w w′ ⟩
            w′ ++ [] ≈⟨ eq ⟩
            w        ∎)
          w′∈X
      })
    (ε∈B⇒A⊆A∙B X ｛ε｝ ε∈｛ε｝)
  where
  open import Relation.Binary.Reasoning.Setoid ≋-setoid
  module X = Language X

∙-identity : (∀ (A : Language a) → ｛ε｝ {b} ∙ A ≈ A) × (∀ (A : Language a) → A ∙ ｛ε｝ {b} ≈ A)
∙-identity = ∙-identityˡ , ∙-identityʳ

∙-zeroˡ : ∀ (A : Language a) → ∅ {b} ∙ A ≈ ∅ {d}
∙-zeroˡ A = ⊆-antisym (sub λ ()) (⊆-min (∅ ∙ A))

∙-zeroʳ : ∀ (A : Language a) → A ∙ ∅ {b} ≈ ∅ {d}
∙-zeroʳ A = ⊆-antisym (sub λ ()) (⊆-min (A ∙ ∅))

∙-zero : (∀ (A : Language a) → ∅ {b} ∙ A ≈ ∅ {d}) × (∀ (A : Language a) → A ∙ ∅ {b} ≈ ∅ {d})
∙-zero = ∙-zeroˡ , ∙-zeroʳ

-- Structures

∙-isMagma : ∀ {a} → IsMagma _≈_ (_∙_ {c ⊔ ℓ ⊔ a})
∙-isMagma = record
  { isEquivalence = ≈-isEquivalence
  ; ∙-cong        = ∙-cong
  }

∙-isSemigroup : ∀ {a} → IsSemigroup _≈_ (_∙_ {c ⊔ ℓ ⊔ a})
∙-isSemigroup {a} = record
  { isMagma = ∙-isMagma {a}
  ; assoc   = ∙-assoc
  }

∙-isMonoid : ∀ {a} → IsMonoid _≈_ _∙_ (｛ε｝ {ℓ ⊔ a})
∙-isMonoid {a} = record
  { isSemigroup = ∙-isSemigroup {a}
  ; identity    = ∙-identity
  }

-- Bundles

∙-Magma : ∀ {a} → Magma (lsuc (c ⊔ ℓ ⊔ a)) (lsuc (c ⊔ ℓ ⊔ a))
∙-Magma {a} = record { isMagma = ∙-isMagma {a} }

∙-Semigroup : ∀ {a} → Semigroup (lsuc (c ⊔ ℓ ⊔ a)) (lsuc (c ⊔ ℓ ⊔ a))
∙-Semigroup {a} = record { isSemigroup = ∙-isSemigroup {a} }

∙-Monoid : ∀ {a} → Monoid (lsuc (c ⊔ ℓ ⊔ a)) (lsuc (c ⊔ ℓ ⊔ a))
∙-Monoid {a} = record { isMonoid = ∙-isMonoid {a} }

------------------------------------------------------------------------
-- Other properties of _∙_

∙-uniqueₗ :
  ∀ (A : Language a) (B : Language b) →
  (∀ {c} → ¬ (Flast A c × First B c)) →
  ¬ Null A →
  ∀ {w} (p q : w ∈ A ∙ B) → (_≋_ on proj₁) p q
∙-uniqueₗ A B ∄[l₁∩f₂] ε∉A (   [] , _ , ε∈A , _             )                  _                       = ⊥-elim (ε∉A ε∈A)
∙-uniqueₗ A B ∄[l₁∩f₂] ε∉A (_ ∷ _  , _                      ) ([] , _ , ε∈A , _                      ) = ⊥-elim (ε∉A ε∈A)
∙-uniqueₗ A B ∄[l₁∩f₂] ε∉A (x ∷ w₁ , w₂ , xw₁∈A , w₂∈B , eq₁) (x′ ∷ w₁′ , w₂′ , x′w₁′∈A , w₂′∈B , eq₂)
  with compare (x ∷ w₁) w₂ (x′ ∷ w₁′) w₂′ (≋-trans eq₁ (≋-sym eq₂))
... | cmp with <?> cmp
... | tri< l _ _ = ⊥-elim (∄[l₁∩f₂] (c∈Flast[A] , c∈First[B]))
  where
  module A   = Language A
  module B   = Language B
  lsplit     = left-split cmp l
  xw∈A       = x′w₁′∈A
  xwcw′∈A    = A.∈-resp-≋ ((proj₁ ∘ proj₂ ∘ proj₂) lsplit) xw₁∈A
  cw′∈B      = B.∈-resp-≋ (≋-sym ((proj₂ ∘ proj₂ ∘ proj₂) lsplit)) w₂′∈B
  c∈Flast[A] = -, -, xw∈A , -, xwcw′∈A
  c∈First[B] = -, cw′∈B
... | tri≈ _ e _ = proj₁ (eq-split cmp e)
... | tri> _ _ r = ⊥-elim (∄[l₁∩f₂] (c∈Flast[A] , c∈First[B]))
  where
  module A   = Language A
  module B   = Language B
  rsplit     = right-split cmp r
  xw∈A       = xw₁∈A
  xwcw′∈A    = A.∈-resp-≋ (≋-sym ((proj₁ ∘ proj₂ ∘ proj₂) rsplit)) x′w₁′∈A
  cw′∈B      = B.∈-resp-≋ ((proj₂ ∘ proj₂ ∘ proj₂) rsplit) w₂∈B
  c∈Flast[A] = -, -, xw∈A , -, xwcw′∈A
  c∈First[B] = -, cw′∈B

∙-uniqueᵣ :
  ∀ (A : Language a) (B : Language b) →
  (∀ {c} → ¬ (Flast A c × First B c)) →
  ¬ Null A →
  ∀ {w} (p q : w ∈ A ∙ B) → (_≋_ on proj₁ ∘ proj₂) p q
∙-uniqueᵣ A B ∄[l₁∩f₂] ε∉A (   []  ,  _ ,   ε∈A , _         )                                        _ = ⊥-elim (ε∉A ε∈A)
∙-uniqueᵣ A B ∄[l₁∩f₂] ε∉A (_ ∷  _ , _                      ) (      [] ,   _ ,     ε∈A , _          ) = ⊥-elim (ε∉A ε∈A)
∙-uniqueᵣ A B ∄[l₁∩f₂] ε∉A (x ∷ w₁ , w₂ , xw₁∈A , w₂∈B , eq₁) (x′ ∷ w₁′ , w₂′ , x′w₁′∈A , w₂′∈B , eq₂)
  with compare (x ∷ w₁) w₂ (x′ ∷ w₁′) w₂′ (≋-trans eq₁ (≋-sym eq₂))
... | cmp with <?> cmp
... | tri< l _ _ = ⊥-elim (∄[l₁∩f₂] (c∈Flast[A] , c∈First[B]))
  where
  module A   = Language A
  module B   = Language B
  lsplit     = left-split cmp l
  xw∈A       = x′w₁′∈A
  xwcw′∈A    = A.∈-resp-≋ ((proj₁ ∘ proj₂ ∘ proj₂) lsplit) xw₁∈A
  cw′∈B      = B.∈-resp-≋ (≋-sym ((proj₂ ∘ proj₂ ∘ proj₂) lsplit)) w₂′∈B
  c∈Flast[A] = -, -, xw∈A , -, xwcw′∈A
  c∈First[B] = -, cw′∈B
... | tri≈ _ e _ = proj₂ (eq-split cmp e)
... | tri> _ _ r = ⊥-elim (∄[l₁∩f₂] (c∈Flast[A] , c∈First[B]))
  where
  module A   = Language A
  module B   = Language B
  rsplit     = right-split cmp r
  xw∈A       = xw₁∈A
  xwcw′∈A    = A.∈-resp-≋ (≋-sym ((proj₁ ∘ proj₂ ∘ proj₂) rsplit)) x′w₁′∈A
  cw′∈B      = B.∈-resp-≋ ((proj₂ ∘ proj₂ ∘ proj₂) rsplit) w₂∈B
  c∈Flast[A] = -, -, xw∈A , -, xwcw′∈A
  c∈First[B] = -, cw′∈B

------------------------------------------------------------------------
-- Proof properties of _∙_

_∙?_ : Decidable A → Decidable B → Decidable (A ∙ B)
_∙?_ {A = A} {B = B} A? B? [] =
  map′
    (λ (ε∈A , ε∈B) → -, -, ε∈A , ε∈B , [])
    (λ {([] , [] , ε∈A , ε∈B , []) → ε∈A , ε∈B})
    (A? [] ×-dec B? [])
_∙?_ {A = A} {B = B} A? B? (x ∷ w) =
  map′
    (λ
      { (inj₁ (ε∈A , xw∈B))                → -, -, ε∈A , xw∈B , ≋-refl
      ; (inj₂ (_ , _ , xw₁∈A , w₂∈B , eq)) → -, -, xw₁∈A , w₂∈B , ∼-refl ∷ eq
      })
    (λ
      { (    [] , _ ,    ε∈A , w′∈B ,        eq) → inj₁ (ε∈A , B.∈-resp-≋ eq w′∈B)
      ; (x′ ∷ _ , _ , x′w₁∈A , w₂∈B , x′∼x ∷ eq) →
        inj₂ (-, -, A.∈-resp-≋ (x′∼x ∷ ≋-refl) x′w₁∈A , w₂∈B , eq)
      })
    (A? [] ×-dec B? (x ∷ w) ⊎-dec (_∙?_ {A = A′} {B = B} (A? ∘ (x ∷_)) B?) w)
  where
  module A = Language A
  module B = Language B
  A′ : Language _
  A′ = record
    { 𝕃 = λ w → x ∷ w ∈ A
    ; ∈-resp-≋ = λ w≋w′ → A.∈-resp-≋ (∼-refl ∷ w≋w′)
    }

------------------------------------------------------------------------
-- Properties of _∪_
------------------------------------------------------------------------
-- Membership properties of _∪_

-- Null

ε∈A⇒ε∈A∪B : ∀ (A : Language b) (B : Language d) → Null A → Null (A ∪ B)
ε∈A⇒ε∈A∪B _ _ = inj₁

ε∈B⇒ε∈A∪B : ∀ (A : Language b) (B : Language d) → Null B → Null (A ∪ B)
ε∈B⇒ε∈A∪B _ _ = inj₂

ε∈A∪B⇒ε∈A⊎ε∈B : ∀ (A : Language b) (B : Language d) → Null (A ∪ B) → Null A ⊎ Null B
ε∈A∪B⇒ε∈A⊎ε∈B _ _ = id

-- First

c∈First[A]⇒c∈First[A∪B] : ∀ {c} → First A c → First (A ∪ B) c
c∈First[A]⇒c∈First[A∪B] = P.map₂ inj₁

c∈First[B]⇒c∈First[A∪B] : ∀ {c} → First B c → First (A ∪ B) c
c∈First[B]⇒c∈First[A∪B] = P.map₂ inj₂

c∈First[A∪B]⇒c∈First[A]∪c∈First[B] : ∀ {c} → First (A ∪ B) c → First A c ⊎ First B c
c∈First[A∪B]⇒c∈First[A]∪c∈First[B] (_ , cw∈A∪B) = S.map -,_ -,_ cw∈A∪B

-- Flast

c∈Flast[A]⇒c∈Flast[A∪B] : ∀ {c} → Flast A c → Flast (A ∪ B) c
c∈Flast[A]⇒c∈Flast[A∪B] = P.map₂ (P.map₂ (P.map inj₁ (P.map₂ inj₁)))

c∈Flast[B]⇒c∈Flast[A∪B] : ∀ {c} → Flast B c → Flast (A ∪ B) c
c∈Flast[B]⇒c∈Flast[A∪B] = P.map₂ (P.map₂ (P.map inj₂ (P.map₂ inj₂)))

-- TODO: rename this
∄[c∈First[A]∩First[B]]+c∈Flast[A∪B]⇒c∈Flast[A]⊎c∈Flast[B] :
  ∀ {c} → (∀ {x} → ¬ (First A x × First B x)) → Flast (A ∪ B) c → Flast A c ⊎ Flast B c
∄[c∈First[A]∩First[B]]+c∈Flast[A∪B]⇒c∈Flast[A]⊎c∈Flast[B] ∄[f₁∩f₂] (_ , _ , inj₁ xw∈A , _ , inj₁ xwcw′∈A) = inj₁ (-, -, xw∈A , -, xwcw′∈A)
∄[c∈First[A]∩First[B]]+c∈Flast[A∪B]⇒c∈Flast[A]⊎c∈Flast[B] ∄[f₁∩f₂] (_ , _ , inj₁ xw∈A , _ , inj₂ xwcw′∈B) = ⊥-elim (∄[f₁∩f₂] ((-, xw∈A) , (-, xwcw′∈B)))
∄[c∈First[A]∩First[B]]+c∈Flast[A∪B]⇒c∈Flast[A]⊎c∈Flast[B] ∄[f₁∩f₂] (_ , _ , inj₂ xw∈B , _ , inj₁ xwcw′∈A) = ⊥-elim (∄[f₁∩f₂] ((-, xwcw′∈A) , (-, xw∈B)))
∄[c∈First[A]∩First[B]]+c∈Flast[A∪B]⇒c∈Flast[A]⊎c∈Flast[B] ∄[f₁∩f₂] (_ , _ , inj₂ xw∈B , _ , inj₂ xwcw′∈B) = inj₂ (-, -, xw∈B , -, xwcw′∈B)

------------------------------------------------------------------------
-- Algebraic properties of _∪_

∪-mono : X ⊆ Y → U ⊆ V → X ∪ U ⊆ Y ∪ V
∪-mono (sub X⊆Y) (sub U⊆V) = sub (S.map X⊆Y U⊆V)

∪-cong : X ≈ Y → U ≈ V → X ∪ U ≈ Y ∪ V
∪-cong X≈Y U≈V = ⊆-antisym
  (∪-mono (⊆-reflexive X≈Y) (⊆-reflexive U≈V))
  (∪-mono (⊇-reflexive X≈Y) (⊇-reflexive U≈V))

∪-assoc : ∀ (A : Language a) (B : Language b) (C : Language d) → (A ∪ B) ∪ C ≈ A ∪ (B ∪ C)
∪-assoc _ _ _ = ⊆-antisym (sub S.assocʳ) (sub S.assocˡ)

∪-comm : ∀ (A : Language a) (B : Language b) → A ∪ B ≈ B ∪ A
∪-comm _ _ = ⊆-antisym (sub S.swap) (sub S.swap)

∪-identityˡ : ∀ (A : Language a) → ∅ {b} ∪ A ≈ A
∪-identityˡ _ = ⊆-antisym (sub λ { (inj₁ ()) ; (inj₂ w∈A) → w∈A }) (sub inj₂)

∪-identityʳ : ∀ (A : Language a) → A ∪ ∅ {b} ≈ A
∪-identityʳ _ = ⊆-antisym (sub λ { (inj₁ w∈A) → w∈A ; (inj₂ ()) }) (sub inj₁)

∪-identity : (∀ (A : Language a) → ∅ {b} ∪ A ≈ A) × (∀ (A : Language a) → A ∪ ∅ {b} ≈ A)
∪-identity = ∪-identityˡ , ∪-identityʳ

∙-distribˡ-∪ : ∀ (A : Language a) (B : Language b) (C : Language d) → A ∙ (B ∪ C) ≈ A ∙ B ∪ A ∙ C
∙-distribˡ-∪ _ _ _ =
  ⊆-antisym
    (sub λ
      { (_ , _ , w₁∈A , inj₁ w₂∈B , eq) → inj₁ (-, -, w₁∈A , w₂∈B , eq)
      ; (_ , _ , w₁∈A , inj₂ w₂∈C , eq) → inj₂ (-, -, w₁∈A , w₂∈C , eq)
      })
    (sub λ
      { (inj₁ (_ , _ , w₁∈A , w₂∈B , eq)) → -, -, w₁∈A , inj₁ w₂∈B , eq
      ; (inj₂ (_ , _ , w₁∈A , w₂∈C , eq)) → -, -, w₁∈A , inj₂ w₂∈C , eq
      })

∙-distribʳ-∪ : ∀ (A : Language a) (B : Language b) (C : Language d) → (B ∪ C) ∙ A ≈ B ∙ A ∪ C ∙ A
∙-distribʳ-∪ _ _ _ =
  ⊆-antisym
    (sub λ
      { (_ , _ , inj₁ w₁∈B , w₂∈A , eq) → inj₁ (-, -, w₁∈B , w₂∈A , eq)
      ; (_ , _ , inj₂ w₁∈C , w₂∈A , eq) → inj₂ (-, -, w₁∈C , w₂∈A , eq)
      })
    (sub λ
      { (inj₁ (_ , _ , w₁∈B , w₂∈A , eq)) → -, -, inj₁ w₁∈B , w₂∈A , eq
      ; (inj₂ (_ , _ , w₁∈C , w₂∈A , eq)) → -, -, inj₂ w₁∈C , w₂∈A , eq
      })

∙-distrib-∪ :
  (∀ (A : Language a) (B : Language b) (C : Language d) → A ∙ (B ∪ C) ≈ A ∙ B ∪ A ∙ C) ×
  (∀ (A : Language a) (B : Language b) (C : Language d) → (B ∪ C) ∙ A ≈ B ∙ A ∪ C ∙ A)
∙-distrib-∪ = ∙-distribˡ-∪ , ∙-distribʳ-∪

∪-idem : ∀ (A : Language a) → A ∪ A ≈ A
∪-idem A = ⊆-antisym (sub [ id , id ]′) (sub inj₁)

-- Structures

∪-isMagma : IsMagma _≈_ (_∪_ {a})
∪-isMagma = record
  { isEquivalence = ≈-isEquivalence
  ; ∙-cong        = ∪-cong
  }

∪-isCommutativeMagma : IsCommutativeMagma _≈_ (_∪_ {a})
∪-isCommutativeMagma = record
  { isMagma = ∪-isMagma
  ; comm    = ∪-comm
  }

∪-isSemigroup : IsSemigroup _≈_ (_∪_ {a})
∪-isSemigroup = record
  { isMagma = ∪-isMagma
  ; assoc   = ∪-assoc
  }

∪-isBand : IsBand _≈_ (_∪_ {a})
∪-isBand = record
  { isSemigroup = ∪-isSemigroup
  ; idem        = ∪-idem
  }

∪-isCommutativeSemigroup : IsCommutativeSemigroup _≈_ (_∪_ {a})
∪-isCommutativeSemigroup = record
  { isSemigroup = ∪-isSemigroup
  ; comm        = ∪-comm
  }

∪-isSemilattice : IsSemilattice _≈_ (_∪_ {a})
∪-isSemilattice = record
  { isBand = ∪-isBand
  ; comm   = ∪-comm
  }

∪-isMonoid : IsMonoid _≈_ _∪_ (∅ {a})
∪-isMonoid = record
  { isSemigroup = ∪-isSemigroup
  ; identity    = ∪-identity
  }

∪-isCommutativeMonoid : IsCommutativeMonoid _≈_ _∪_ (∅ {a})
∪-isCommutativeMonoid = record
  { isMonoid = ∪-isMonoid
  ; comm     = ∪-comm
  }

∪-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _≈_ _∪_ (∅ {a})
∪-isIdempotentCommutativeMonoid = record
  { isCommutativeMonoid = ∪-isCommutativeMonoid
  ; idem                = ∪-idem
  }

∪-∙-isNearSemiring : IsNearSemiring _≈_ _∪_ _∙_ (∅ {c ⊔ ℓ ⊔ a})
∪-∙-isNearSemiring {a} = record
  { +-isMonoid    = ∪-isMonoid
  ; *-isSemigroup = ∙-isSemigroup {a}
  ; distribʳ      = ∙-distribʳ-∪
  ; zeroˡ         = ∙-zeroˡ
  }

∪-∙-isSemiringWithoutOne : IsSemiringWithoutOne _≈_ _∪_ _∙_ (∅ {c ⊔ ℓ ⊔ a})
∪-∙-isSemiringWithoutOne {a} = record
  { +-isCommutativeMonoid = ∪-isCommutativeMonoid
  ; *-isSemigroup         = ∙-isSemigroup {a}
  ; distrib               = ∙-distrib-∪
  ; zero                  = ∙-zero
  }

∪-∙-isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _≈_ _∪_ _∙_ ∅ (｛ε｝ {ℓ ⊔ a})
∪-∙-isSemiringWithoutAnnihilatingZero {a} = record
  { +-isCommutativeMonoid = ∪-isCommutativeMonoid
  ; *-isMonoid            = ∙-isMonoid {a}
  ; distrib               = ∙-distrib-∪
  }

∪-∙-isSemiring : IsSemiring _≈_ _∪_ _∙_ ∅ (｛ε｝ {ℓ ⊔ a})
∪-∙-isSemiring {a} = record
  { isSemiringWithoutAnnihilatingZero = ∪-∙-isSemiringWithoutAnnihilatingZero {a}
  ; zero                              = ∙-zero
  }

-- Bundles

∪-magma : Magma (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a)
∪-magma {a} = record { isMagma = ∪-isMagma {a} }

∪-commutativeMagma : CommutativeMagma (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a)
∪-commutativeMagma {a} = record { isCommutativeMagma = ∪-isCommutativeMagma {a} }

∪-semigroup : Semigroup (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a)
∪-semigroup {a} = record { isSemigroup = ∪-isSemigroup {a} }

∪-band : Band (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a)
∪-band {a} = record { isBand = ∪-isBand {a} }

∪-commutativeSemigroup : CommutativeSemigroup (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a)
∪-commutativeSemigroup {a} = record { isCommutativeSemigroup = ∪-isCommutativeSemigroup {a} }

∪-semilattice : Semilattice (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a)
∪-semilattice {a} = record { isSemilattice = ∪-isSemilattice {a} }

∪-monoid : Monoid (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a)
∪-monoid {a} = record { isMonoid = ∪-isMonoid {a} }

∪-commutativeMonoid : CommutativeMonoid (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a)
∪-commutativeMonoid {a} = record { isCommutativeMonoid = ∪-isCommutativeMonoid {a} }

∪-idempotentCommutativeMonoid : IdempotentCommutativeMonoid (c ⊔ ℓ ⊔ lsuc a) (c ⊔ ℓ ⊔ lsuc a)
∪-idempotentCommutativeMonoid {a} = record
  { isIdempotentCommutativeMonoid = ∪-isIdempotentCommutativeMonoid {a} }

∪-∙-nearSemiring : NearSemiring (lsuc (c ⊔ ℓ ⊔ a)) (lsuc (c ⊔ ℓ ⊔ a))
∪-∙-nearSemiring {a} = record { isNearSemiring = ∪-∙-isNearSemiring {a} }

∪-∙-semiringWithoutOne : SemiringWithoutOne (lsuc (c ⊔ ℓ ⊔ a)) (lsuc (c ⊔ ℓ ⊔ a))
∪-∙-semiringWithoutOne {a} = record { isSemiringWithoutOne = ∪-∙-isSemiringWithoutOne {a} }

∪-∙-semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero (lsuc (c ⊔ ℓ ⊔ a)) (lsuc (c ⊔ ℓ ⊔ a))
∪-∙-semiringWithoutAnnihilatingZero {a} = record { isSemiringWithoutAnnihilatingZero = ∪-∙-isSemiringWithoutAnnihilatingZero {a} }

∪-∙-semiring : Semiring (lsuc (c ⊔ ℓ ⊔ a)) (lsuc (c ⊔ ℓ ⊔ a))
∪-∙-semiring {a} = record { isSemiring = ∪-∙-isSemiring {a} }

------------------------------------------------------------------------
-- Other properties of _∪_

∪-selective :
  ¬ (Null A × Null B) →
  (∀ {c} → ¬ (First A c × First B c)) →
  ∀ {w} → w ∈ A ∪ B → (w ∈ A × w ∉ B) ⊎ (w ∉ A × w ∈ B)
∪-selective ε∉A∩B ∄[f₁∩f₂] {[]}    (inj₁ ε∈A) = inj₁ (ε∈A , ε∉A∩B ∘ (ε∈A ,_))
∪-selective ε∉A∩B ∄[f₁∩f₂] {c ∷ w} (inj₁ cw∈A) = inj₁ (cw∈A , ∄[f₁∩f₂] ∘ ((w , cw∈A) ,_) ∘ (w ,_))
∪-selective ε∉A∩B ∄[f₁∩f₂] {[]}    (inj₂ ε∈B) = inj₂ (ε∉A∩B ∘ (_, ε∈B) , ε∈B)
∪-selective ε∉A∩B ∄[f₁∩f₂] {c ∷ w} (inj₂ cw∈B) = inj₂ (∄[f₁∩f₂] ∘ (_, (w , cw∈B)) ∘ (w ,_) , cw∈B)

------------------------------------------------------------------------
-- Proof properties of _∪_

_∪?_ : Decidable A → Decidable B → Decidable (A ∪ B)
(A? ∪? B?) w = A? w ⊎-dec B? w

------------------------------------------------------------------------
-- Properties of Sup
------------------------------------------------------------------------
-- Membership properties of Sup

FⁿA⊆SupFA : ∀ n → (F ^ n) A ⊆ Sup F A
FⁿA⊆SupFA n = sub (n ,_)

FⁿFA⊆SupFA : ∀ n → (F ^ n) (F A) ⊆ Sup F A
FⁿFA⊆SupFA {F = F} {A = A} n = ⊆-trans (sub (go n)) (FⁿA⊆SupFA (ℕ.suc n))
  where
  go : ∀ {w} n → w ∈ (F ^ n) (F A) → w ∈ (F ^ (ℕ.suc n)) A
  go {w = w} n w∈Fⁿ̂FA = subst (λ x → w ∈ x A) (fⁿf≡fⁿ⁺¹ F n) w∈Fⁿ̂FA

∀[FⁿA⊆B]⇒SupFA⊆B : (∀ n → (F ^ n) A ⊆ B) → Sup F A ⊆ B
∀[FⁿA⊆B]⇒SupFA⊆B FⁿA⊆B = sub λ (n , w∈FⁿA) → ∈-resp-⊆ (FⁿA⊆B n) w∈FⁿA

∃[B⊆FⁿA]⇒B⊆SupFA : ∀ n → B ⊆ (F ^ n) A → B ⊆ Sup F A
∃[B⊆FⁿA]⇒B⊆SupFA n B⊆FⁿA = sub λ w∈B → n , ∈-resp-⊆ B⊆FⁿA w∈B

∀[FⁿA≈GⁿB]⇒SupFA≈SupGB : (∀ n → (F ^ n) A ≈ (G ^ n) B) → Sup F A ≈ Sup G B
∀[FⁿA≈GⁿB]⇒SupFA≈SupGB FⁿA≈GⁿB =
  ⊆-antisym
    (sub λ (n , w∈FⁿA) → n , ∈-resp-≈ (FⁿA≈GⁿB n) w∈FⁿA)
    (sub λ (n , w∈GⁿB) → n , ∈-resp-≈ (≈-sym (FⁿA≈GⁿB n)) w∈GⁿB)
------------------------------------------------------------------------
-- Properties of ⋃_
------------------------------------------------------------------------
-- Membership properties of ⋃_

Fⁿ⊆⋃F : ∀ n → (F ^ n) ∅ ⊆ ⋃ F
Fⁿ⊆⋃F = FⁿA⊆SupFA

∀[Fⁿ⊆B]⇒⋃F⊆B : (∀ n → (F ^ n) ∅ ⊆ B) → ⋃ F ⊆ B
∀[Fⁿ⊆B]⇒⋃F⊆B = ∀[FⁿA⊆B]⇒SupFA⊆B

∃[B⊆Fⁿ]⇒B⊆⋃F : ∀ n → B ⊆ (F ^ n) ∅ → B ⊆ ⋃ F
∃[B⊆Fⁿ]⇒B⊆⋃F = ∃[B⊆FⁿA]⇒B⊆SupFA

∀[Fⁿ≈Gⁿ]⇒⋃F≈⋃G : (∀ n → (F ^ n) ∅ ≈ (G ^ n) ∅) → ⋃ F ≈ ⋃ G
∀[Fⁿ≈Gⁿ]⇒⋃F≈⋃G = ∀[FⁿA≈GⁿB]⇒SupFA≈SupGB

------------------------------------------------------------------------
-- Functional properties of ⋃_

⋃-mono : (∀ {A B} → A ⊆ B → F A ⊆ G B) → ⋃ F ⊆ ⋃ G
⋃-mono mono-ext = ∀[Fⁿ⊆B]⇒⋃F⊆B λ n → ⊆-trans (f∼g⇒fⁿ∼gⁿ _⊆_ (⊆-min ∅) mono-ext n) (Fⁿ⊆⋃F n)

⋃-cong : (∀ {A B} → A ≈ B → F A ≈ G B) → ⋃ F ≈ ⋃ G
⋃-cong ext = ∀[Fⁿ≈Gⁿ]⇒⋃F≈⋃G (f∼g⇒fⁿ∼gⁿ _≈_ (⊆-antisym (⊆-min ∅) (⊆-min ∅)) ext)

⋃-inverseʳ : ∀ (A : Language a) → ⋃ (const A) ≈ A
⋃-inverseʳ _ = ⊆-antisym (sub λ {(ℕ.suc _ , w∈A) → w∈A}) (Fⁿ⊆⋃F 1)
