{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Context.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Context.Base over
open import Cfe.Fin
open import Cfe.Type over using ()
  renaming
  ( _≈_ to _≈ᵗ_
  ; ≈-refl to ≈ᵗ-refl
  ; ≈-sym to ≈ᵗ-sym
  ; ≈-trans to ≈ᵗ-trans
  ; _≤_ to _≤ᵗ_
  ; ≤-refl to ≤ᵗ-refl
  ; ≤-reflexive to ≤ᵗ-reflexive
  ; ≤-trans to ≤ᵗ-trans
  ; ≤-antisym to ≤ᵗ-antisym
  )
open import Data.Fin hiding (pred; _≟_) renaming (_≤_ to _≤ᶠ_)
open import Data.Fin.Properties using (toℕ<n; toℕ-injective; toℕ-inject₁)
  renaming
  ( ≤-refl to ≤ᶠ-refl
  ; ≤-reflexive to ≤ᶠ-reflexive
  ; ≤-trans to ≤ᶠ-trans
  ; ≤-antisym to ≤ᶠ-antisym
  )
open import Data.Nat renaming (_≤_ to _≤ⁿ_)
open import Data.Nat.Properties using (<⇒≤pred; pred-mono; module ≤-Reasoning)
  renaming
  ( ≤-refl to ≤ⁿ-refl
  ; ≤-reflexive to ≤ⁿ-reflexive
  ; ≤-trans to ≤ⁿ-trans
  )
open import Data.Product
open import Data.Vec using ([]; _∷_; Vec; insert; remove)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as Pw using ([]; _∷_; Pointwise)
open import Function
open import Relation.Binary.PropositionalEquality hiding (setoid)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Properties for Pointwise
------------------------------------------------------------------------

  pw-antisym :
    ∀ {a b ℓ} {A : Set a} {B : Set b} {P : REL A B ℓ} {Q : REL B A ℓ} {R : REL A B ℓ} {m n} →
    Antisym P Q R → Antisym (Pointwise P {m} {n}) (Pointwise Q) (Pointwise R)
  pw-antisym antisym []       []       = []
  pw-antisym antisym (x ∷ xs) (y ∷ ys) = antisym x y ∷ pw-antisym antisym xs ys

  pw-insert :
    ∀ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} {m n} {xs : Vec A m} {ys : Vec B n} →
    ∀ i j {i≡j : True (toℕ i ≟ toℕ j)} {x y} →
    x ∼ y → Pointwise _∼_ xs ys → Pointwise _∼_ (insert xs i x) (insert ys j y)
  pw-insert zero    zero          x xs       = x ∷ xs
  pw-insert (suc i) (suc j) {i≡j} x (y ∷ xs) =
    y ∷ pw-insert i j {i≡j |> toWitness |> cong pred |> fromWitness} x xs

  pw-remove :
    ∀ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} →
    ∀ {m n} {xs : Vec A (suc m)} {ys : Vec B (suc n)} →
    ∀ i j {i≡j : True (toℕ i ≟ toℕ j)} →
    Pointwise _∼_ xs ys → Pointwise _∼_ (remove xs i) (remove ys j)
  pw-remove zero zero (_ ∷ xs) = xs
  pw-remove (suc i) (suc j) {i≡j} (x ∷ y ∷ xs) =
    x ∷ pw-remove i j {i≡j |> toWitness |> cong pred |> fromWitness} (y ∷ xs)

------------------------------------------------------------------------
-- Properties of _≈_
------------------------------------------------------------------------
-- Relational Properties

≈-refl : Reflexive (_≈_ {n})
≈-refl = refl , Pw.refl ≈ᵗ-refl

≈-sym : Symmetric (_≈_ {n})
≈-sym = map sym (Pw.sym ≈ᵗ-sym)

≈-trans : Transitive (_≈_ {n})
≈-trans = zip trans (Pw.trans ≈ᵗ-trans)

------------------------------------------------------------------------
-- Structures

≈-isPartialEquivalence : IsPartialEquivalence (_≈_ {n})
≈-isPartialEquivalence = record
  { sym   = ≈-sym
  ; trans = ≈-trans
  }

≈-isEquivalence : IsEquivalence (_≈_ {n})
≈-isEquivalence = record
  { refl  = ≈-refl
  ; sym   = ≈-sym
  ; trans = ≈-trans
  }

------------------------------------------------------------------------
-- Bundles

partialSetoid : ∀ {n} → PartialSetoid _ _
partialSetoid {n} = record { isPartialEquivalence = ≈-isPartialEquivalence {n} }

setoid : ∀ {n} → Setoid _ _
setoid {n} = record { isEquivalence = ≈-isEquivalence {n} }

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------

≤-refl : Reflexive (_≤_ {n})
≤-refl = ≤ᶠ-refl , Pw.refl ≤ᵗ-refl

≤-reflexive : (_≈_ {n}) ⇒ _≤_
≤-reflexive = map (≤ᶠ-reflexive ∘ sym) (Pw.map ≤ᵗ-reflexive)

≤-trans : Transitive (_≤_ {n})
≤-trans = zip (flip ≤ᶠ-trans) (Pw.trans ≤ᵗ-trans)

≤-antisym : Antisymmetric (_≈_ {n}) _≤_
≤-antisym = zip (sym ∘₂ ≤ᶠ-antisym) (pw-antisym ≤ᵗ-antisym)

------------------------------------------------------------------------
-- Structures

≤-isPreorder : IsPreorder (_≈_ {n}) _≤_
≤-isPreorder = record
  { isEquivalence = ≈-isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder (_≈_ {n}) _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

------------------------------------------------------------------------
-- Bundles

≤-preorder : ∀ {n} → Preorder _ _ _
≤-preorder {n} = record { isPreorder = ≤-isPreorder {n} }

≤-poset : ∀ {n} → Poset _ _ _
≤-poset {n} = record { isPartialOrder = ≤-isPartialOrder {n} }

------------------------------------------------------------------------
-- Properties of wkn₂
------------------------------------------------------------------------

wkn₂-mono :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ< i ≟ toℕ< j)} {τ₁ τ₂} →
  τ₁ ≤ᵗ τ₂ → ctx₁ ≤ ctx₂ → wkn₂ {n} ctx₁ i τ₁ ≤ wkn₂ ctx₂ j τ₂
wkn₂-mono i j {i≡j} τ₁≤τ₂ (g₂≤g₁ , Γ,Δ₁≤Γ,Δ₂) =
  s≤s g₂≤g₁ ,
  pw-insert
    (inject!< i) (inject!< j)
    {i≡j |> toWitness |> inject!<-cong |> fromWitness}
    τ₁≤τ₂
    Γ,Δ₁≤Γ,Δ₂

wkn₂-cong :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ< i ≟ toℕ< j)} {τ₁ τ₂} →
  τ₁ ≈ᵗ τ₂ → ctx₁ ≈ ctx₂ → wkn₂ {n} ctx₁ i τ₁ ≈ wkn₂ ctx₂ j τ₂
wkn₂-cong i j {i≡j} τ₁≈τ₂ ctx₁≈ctx₂ =
  ≤-antisym
    (wkn₂-mono i j {i≡j} (≤ᵗ-reflexive τ₁≈τ₂) (≤-reflexive ctx₁≈ctx₂))
    (wkn₂-mono j i
      {i≡j |> toWitness |> sym |> fromWitness}
      (≤ᵗ-reflexive (≈ᵗ-sym τ₁≈τ₂))
      (≤-reflexive (≈-sym ctx₁≈ctx₂)))

wkn₂-cong-≡ :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ< i ≟ toℕ< j)} {τ₁ τ₂} →
  τ₁ ≡ τ₂ → ctx₁ ≡ ctx₂ → wkn₂ {n} ctx₁ i τ₁ ≡ wkn₂ ctx₂ j τ₂
wkn₂-cong-≡ {ctx₁ = Γ,Δ ⊐ g} i j {i≡j} {τ} refl refl =
  i≡j |> toWitness |> inject!<-cong |> toℕ-injective |> cong (λ x → insert Γ,Δ x τ ⊐ suc g)

wkn₂-comm :
  ∀ ctx i j τ τ′ →
  wkn₂ (wkn₂ {n} ctx (inject!<< {j = suc i} j) τ′) (suc i) τ ≡ wkn₂ (wkn₂ ctx i τ) (inject<< j) τ′
wkn₂-comm (Γ,Δ ⊐ g)         i       zero    τ τ′ = refl
wkn₂-comm (_ ∷ Γ,Δ ⊐ suc g) (suc i) (suc j) τ τ′ =
  wkn₂-cong-≡ zero zero refl (wkn₂-comm (Γ,Δ ⊐ g) i j τ τ′)

------------------------------------------------------------------------
-- Properties of wkn₁
------------------------------------------------------------------------

wkn₁-mono :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ> i ≟ toℕ> j)} →
  ∀ {τ₁ τ₂} → τ₁ ≤ᵗ τ₂ → ctx₁ ≤ ctx₂ → wkn₁ {n} ctx₁ i τ₁ ≤ wkn₁ ctx₂ j τ₂
wkn₁-mono {_} {_ ⊐ g₁} {_ ⊐ g₂} i j {i≡j} τ₁≤τ₂ (g₂≤g₁ , Γ,Δ₁≤Γ,Δ₂) =
  (begin
    toℕ (inject₁ g₂) ≡⟨ toℕ-inject₁ g₂ ⟩
    toℕ g₂           ≤⟨ g₂≤g₁ ⟩
    toℕ g₁           ≡˘⟨ toℕ-inject₁ g₁ ⟩
    toℕ (inject₁ g₁) ∎) ,
  pw-insert
    (raise!> i) (raise!> j)
    {i≡j |> toWitness |> raise!>-cong |> fromWitness}
    τ₁≤τ₂
    Γ,Δ₁≤Γ,Δ₂
  where open ≤-Reasoning

wkn₁-cong :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ> i ≟ toℕ> j)} {τ₁ τ₂} →
  τ₁ ≈ᵗ τ₂ → ctx₁ ≈ ctx₂ → wkn₁ {n} ctx₁ i τ₁ ≈ wkn₁ ctx₂ j τ₂
wkn₁-cong i j {i≡j} τ₁≈τ₂ ctx₁≈ctx₂ =
  ≤-antisym
    (wkn₁-mono i j {i≡j} (≤ᵗ-reflexive τ₁≈τ₂) (≤-reflexive ctx₁≈ctx₂))
    (wkn₁-mono j i
      {i≡j |> toWitness |> sym |> fromWitness}
      (≤ᵗ-reflexive (≈ᵗ-sym τ₁≈τ₂))
      (≤-reflexive (≈-sym ctx₁≈ctx₂)))

wkn₁-cong-≡ :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ> i ≟ toℕ> j)} {τ₁ τ₂} →
  τ₁ ≡ τ₂ → ctx₁ ≡ ctx₂ → wkn₁ {n} ctx₁ i τ₁ ≡ wkn₁ ctx₂ j τ₂
wkn₁-cong-≡ {ctx₁ = Γ,Δ ⊐ g} i j {i≡j} {τ} refl refl =
  i≡j |> toWitness |> raise!>-cong |> toℕ-injective |> cong (λ x → insert Γ,Δ x τ ⊐ inject₁ g)

wkn₁-comm :
  ∀ ctx i j τ τ′ →
  wkn₁ (wkn₁ {n} ctx (inject!>< {j = suc> i} j) τ′) (suc> i) τ ≡ wkn₁ (wkn₁ ctx i τ) (inject>< j) τ′
wkn₁-comm (Γ,Δ ⊐ zero)      zero    zero    τ τ′ = refl
wkn₁-comm (Γ,Δ ⊐ zero)      (suc i) zero    τ τ′ =
  wkn₁-cong-≡ zero zero refl
    (wkn₁-cong-≡ (suc> i) (suc i) {toℕ-suc> i |> fromWitness } refl refl)
wkn₁-comm (_ ∷ Γ,Δ ⊐ zero)  (suc i) (suc j) τ τ′ =
  wkn₁-cong-≡ zero zero refl (wkn₁-comm (Γ,Δ ⊐ zero) i j τ τ′)
wkn₁-comm (_ ∷ Γ,Δ ⊐ suc g) (inj i) (inj j) τ τ′ =
  wkn₂-cong-≡ zero zero refl (wkn₁-comm (Γ,Δ ⊐ g) i j τ τ′)

wkn₁-wkn₂-comm :
  ∀ ctx i j τ τ′ →
  wkn₁ (wkn₂ {n} ctx j τ′) (inj i) τ ≡
  wkn₂ (wkn₁ ctx i τ) (cast< (guard ctx |> toℕ-inject₁ |> cong suc |> sym) j) τ′
wkn₁-wkn₂-comm (Γ,Δ ⊐ g)         i       zero    τ τ′ = refl
wkn₁-wkn₂-comm (_ ∷ Γ,Δ ⊐ suc g) (inj i) (suc j) τ τ′ =
  wkn₂-cong-≡ zero zero refl (wkn₁-wkn₂-comm (Γ,Δ ⊐ g) i j τ τ′)

------------------------------------------------------------------------
-- Properties of shift
------------------------------------------------------------------------

shift-mono : ∀ {ctx₁ ctx₂ i j} → toℕ< j ≤ⁿ toℕ< i → ctx₁ ≤ ctx₂ → shift {n} ctx₁ i ≤ shift ctx₂ j
shift-mono {i = i} {j} j≤i (_ , Γ,Δ₁≤Γ,Δ₂) = inject!<-mono j≤i , Γ,Δ₁≤Γ,Δ₂

shift-cong :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ< i ≟ toℕ< j)} → ctx₁ ≈ ctx₂ → shift {n} ctx₁ i ≈ shift ctx₂ j
shift-cong i j {i≡j} ctx₁≈ctx₂ =
  ≤-antisym
    (shift-mono (i≡j |> toWitness |> sym |> ≤ⁿ-reflexive) (≤-reflexive ctx₁≈ctx₂))
    (shift-mono (i≡j |> toWitness |> ≤ⁿ-reflexive) (≤-reflexive (≈-sym ctx₁≈ctx₂)))

shift-cong-≡ :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ< i ≟ toℕ< j)} → ctx₁ ≡ ctx₂ → shift {n} ctx₁ i ≡ shift ctx₂ j
shift-cong-≡ {ctx₁ = Γ,Δ ⊐ _} i j {i≡j} refl =
  i≡j |> toWitness |> inject!<-cong |> toℕ-injective |> cong (Γ,Δ ⊐_)

shift-identity : ∀ ctx → shift {n} ctx (strengthen< (guard ctx)) ≡ ctx
shift-identity (Γ,Δ ⊐ zero)       = refl
shift-identity (_ ∷ Γ,Δ ⊐ suc g) = wkn₂-cong-≡ zero zero refl (shift-identity (Γ,Δ ⊐ g))

shift-trans :
  ∀ ctx i j →
  shift (shift {n} ctx i) (inject!<< (cast<< (strengthen<-inject!< i |> cong suc |> sym) j)) ≡
  shift ctx (inject!<< j)
shift-trans (Γ,Δ ⊐ _)         _       zero    = refl
shift-trans (_ ∷ Γ,Δ ⊐ suc g) (suc i) (suc j) =
  wkn₂-cong-≡ zero zero refl (shift-trans (Γ,Δ ⊐ g) i j)

shift-wkn₁-comm :
  ∀ ctx i j τ →
  let i≤g = ≤ⁿ-trans (≤ⁿ-reflexive (toℕ-inject!< i)) (pred-mono (toℕ<<i i)) in
  shift (wkn₁ {n} ctx j τ) (cast< (toℕ-inject₁ (guard ctx) |> cong suc |> sym) i) ≡
  wkn₁ (shift ctx i) (cast> (inject₁-mono i≤g) j) τ
shift-wkn₁-comm (Γ,Δ ⊐ zero)      zero    j τ =
 wkn₁-cong-≡ j (cast> ≤ⁿ-refl j) {toℕ-cast> ≤ⁿ-refl j |> sym |> fromWitness} refl refl
shift-wkn₁-comm (_ ∷ Γ,Δ ⊐ suc g) zero    (inj j) τ =
  wkn₁-cong-≡ zero zero refl (shift-wkn₁-comm (Γ,Δ ⊐ g) zero j τ)
shift-wkn₁-comm (_ ∷ Γ,Δ ⊐ suc g) (suc i) (inj j) τ =
  wkn₂-cong-≡ zero zero refl (shift-wkn₁-comm (Γ,Δ ⊐ g) i j τ)

shift-wkn₂-comm :
  ∀ ctx i j τ →
  shift (wkn₂ {n} ctx (inject!<< j) τ) (suc i) ≡
  wkn₂ (shift ctx i) (inject!<< (cast<< (strengthen<-inject!< i |> cong suc |> sym) j)) τ
shift-wkn₂-comm (Γ,Δ ⊐ g)         i       zero    τ = refl
shift-wkn₂-comm (_ ∷ Γ,Δ ⊐ suc g) (suc i) (suc j) τ =
  wkn₂-cong-≡ zero zero refl (shift-wkn₂-comm (Γ,Δ ⊐ g) i j τ)

shift-wkn₁-wkn₂-comm :
  ∀ ctx i j τ →
  shift (wkn₂ {n} ctx i τ) (inject<< j) ≡ wkn₁ (shift ctx (inject!<< j)) (reflect! i j) τ
shift-wkn₁-wkn₂-comm (Γ,Δ ⊐ g)         zero    zero    τ = refl
shift-wkn₁-wkn₂-comm (_ ∷ Γ,Δ ⊐ suc g) (suc i) zero    τ =
  wkn₁-cong-≡ zero zero refl (shift-wkn₁-wkn₂-comm (Γ,Δ ⊐ g) i zero τ)
shift-wkn₁-wkn₂-comm (_ ∷ Γ,Δ ⊐ suc g) (suc i) (suc j) τ =
  wkn₂-cong-≡ zero zero refl (shift-wkn₁-wkn₂-comm (Γ,Δ ⊐ g) i j τ)

------------------------------------------------------------------------
-- Properties of remove₂
------------------------------------------------------------------------

remove₂-mono :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ< i ≟ toℕ< j)} →
  ctx₁ ≤ ctx₂ → remove₂ {n} ctx₁ i ≤ remove₂ ctx₂ j
remove₂-mono i j {i≡j} (g₂≤g₁ , Γ,Δ₁≤Γ,Δ₂) =
  predⁱ<-mono j i g₂≤g₁ ,
  pw-remove (inject!< i) (inject!< j) {i≡j |> toWitness |> inject!<-cong |> fromWitness} Γ,Δ₁≤Γ,Δ₂

remove₂-cong :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ< i ≟ toℕ< j)} →
  ctx₁ ≈ ctx₂ → remove₂ {n} ctx₁ i ≈ remove₂ ctx₂ j
remove₂-cong i j {i≡j} ctx₁≈ctx₂ =
  ≤-antisym
    (remove₂-mono i j {i≡j} (≤-reflexive ctx₁≈ctx₂))
    (remove₂-mono j i {i≡j |> toWitness |> sym |> fromWitness} (≤-reflexive (≈-sym ctx₁≈ctx₂)))

remove₂-cong-≡ :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ< i ≟ toℕ< j)} →
  ctx₁ ≡ ctx₂ → remove₂ {n} ctx₁ i ≡ remove₂ ctx₂ j
remove₂-cong-≡ {ctx₁ = Γ,Δ ⊐ _} i j {i≡j} refl =
  i≡j |> toWitness |> λ i≡j →
    cong₂
      _⊐_
      (i≡j |> inject!<-cong |> toℕ-injective |> cong (remove Γ,Δ))
      (predⁱ<-cong i j refl |> toℕ-injective)

remove₂-wkn₂-comm :
  ∀ ctx i j τ →
  remove₂ (wkn₂ {suc n} ctx (inject<< {j = suc i} j) τ) (suc i) ≡
  wkn₂ (remove₂ ctx i) (cast< (sym (toℕ-predⁱ< i)) (inject!<< j)) τ
remove₂-wkn₂-comm (_ ∷ Γ,Δ ⊐ suc g)            i       zero          τ = refl
remove₂-wkn₂-comm (_ ∷ τ′ ∷ Γ,Δ ⊐ suc (suc g)) (suc i) (suc zero)    τ = refl
remove₂-wkn₂-comm (_ ∷ τ′ ∷ Γ,Δ ⊐ suc (suc g)) (suc i) (suc (suc j)) τ =
  wkn₂-cong-≡ zero zero refl (remove₂-wkn₂-comm (τ′ ∷ Γ,Δ ⊐ suc g) i (suc j) τ)

------------------------------------------------------------------------
-- Properties of remove₁
------------------------------------------------------------------------

remove₁-mono :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ> i ≟ toℕ> j)} →
  ctx₁ ≤ ctx₂ → remove₁ {n} ctx₁ i ≤ remove₁ ctx₂ j
remove₁-mono i j {i≡j} (g₂≤g₁ , Γ,Δ₁≤Γ,Δ₂) =
  inject₁ⁱ>-mono j i g₂≤g₁ ,
  pw-remove (raise!> i) (raise!> j) {i≡j |> toWitness |> raise!>-cong |> fromWitness} Γ,Δ₁≤Γ,Δ₂

remove₁-cong :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ> i ≟ toℕ> j)} →
  ctx₁ ≈ ctx₂ → remove₁ {n} ctx₁ i ≈ remove₁ ctx₂ j
remove₁-cong i j {i≡j} ctx₁≈ctx₂ =
  ≤-antisym
    (remove₁-mono i j {i≡j} (≤-reflexive ctx₁≈ctx₂))
    (remove₁-mono j i {i≡j |> toWitness |> sym |> fromWitness} (≤-reflexive (≈-sym ctx₁≈ctx₂)))

remove₁-cong-≡ :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ> i ≟ toℕ> j)} →
  ctx₁ ≡ ctx₂ → remove₁ {n} ctx₁ i ≡ remove₁ ctx₂ j
remove₁-cong-≡ {ctx₁ = Γ,Δ ⊐ _} i j {i≡j} refl =
  i≡j |> toWitness |> λ i≡j →
    cong₂
      _⊐_
      (i≡j |> raise!>-cong |> toℕ-injective |> cong (remove Γ,Δ))
      (inject₁ⁱ>-cong i j refl |> toℕ-injective)

remove₁-wkn₂-comm :
  ∀ ctx i j τ →
  remove₁ (wkn₂ {suc n} ctx j τ) (inj i) ≡
  wkn₂ (remove₁ ctx i) (cast< (toℕ-inject₁ⁱ> i |> cong suc |> sym) j) τ
remove₁-wkn₂-comm (_ ∷ Γ,Δ ⊐ g)               _       zero           τ = refl
remove₁-wkn₂-comm (_ ∷ _ ∷ Γ,Δ ⊐ suc zero)    (inj i) (suc zero)     τ = refl
remove₁-wkn₂-comm (_ ∷ _ ∷ Γ,Δ ⊐ suc (suc g)) (inj i) (suc zero)     τ = refl
remove₁-wkn₂-comm (_ ∷ τ′ ∷ Γ,Δ ⊐ suc (suc g)) (inj i) (suc (suc j)) τ =
  wkn₂-cong-≡ zero zero refl (remove₁-wkn₂-comm ((τ′ ∷ Γ,Δ) ⊐ suc g) i (suc j) τ)

remove₁-shift-comm :
  ∀ ctx i j →
  remove₁ (shift ctx i) (cast> (≤ⁿ-trans (≤ⁿ-reflexive (toℕ-inject!< i)) (<⇒≤pred (toℕ<<i i))) j) ≡
  shift (remove₁ {n} ctx j) (cast< (toℕ-inject₁ⁱ> j |> cong suc |> sym) i)
remove₁-shift-comm (Γ,Δ ⊐ g)                    zero    zero    = refl
remove₁-shift-comm (Γ,Δ ⊐ g)                    zero    (suc j) =
  toℕ-cast> z≤n j |> raise!>-cong |> toℕ-injective |> cong ((_⊐ zero) ∘ remove Γ,Δ ∘ suc)
remove₁-shift-comm (Γ,Δ ⊐ g)                    zero    (inj j) =
  toℕ-cast> z≤n j |> raise!>-cong |> toℕ-injective |> cong ((_⊐ zero) ∘ remove Γ,Δ ∘ suc)
remove₁-shift-comm (_ ∷ τ′ ∷ Γ,Δ ⊐ suc zero)    (suc i) (inj j) =
  wkn₂-cong-≡ zero zero refl (remove₁-shift-comm (τ′ ∷ Γ,Δ ⊐ zero) i j)
remove₁-shift-comm (_ ∷ τ′ ∷ Γ,Δ ⊐ suc (suc g)) (suc i) (inj j) =
  wkn₂-cong-≡ zero zero refl (remove₁-shift-comm (τ′ ∷ Γ,Δ ⊐ suc g) i j)

-- remove₁ (shift ctx zero) (reflect i zero) ≡ shift (remove ctx i) zero
remove₁-remove₂-shift-comm :
  ∀ ctx i j →
  let eq = inject-square j |> cong toℕ |> sym |> ≤ⁿ-reflexive in
  remove₁ (shift {suc n} ctx (inject<< j)) (cast> eq (reflect i j)) ≡
  shift (remove₂ ctx i) (cast< (sym (toℕ-predⁱ< i)) (inject!<< j))
remove₁-remove₂-shift-comm (Γ,Δ ⊐ suc g)                zero    zero    = refl
remove₁-remove₂-shift-comm (Γ,Δ ⊐ suc (suc g))          (suc i) zero    =
  cong ((_⊐ zero) ∘ remove Γ,Δ ∘ suc) (toℕ-injective (begin
    toℕ (raise!> (cast> _ (reflect i zero))) ≡⟨ toℕ-raise!> (cast> _ (reflect i zero)) ⟩
    toℕ> (cast> _ (reflect i zero))          ≡⟨ toℕ-cast> z≤n (reflect i zero) ⟩
    toℕ> (reflect i zero)                    ≡⟨ toℕ-reflect i zero ⟩
    toℕ< i                                   ≡˘⟨ toℕ-inject!< i ⟩
    toℕ (inject!< i)                         ∎))
  where open ≡-Reasoning
remove₁-remove₂-shift-comm (_ ∷ τ′ ∷ Γ,Δ ⊐ suc (suc g)) (suc i) (suc j) =
  wkn₂-cong-≡ zero zero refl (remove₁-remove₂-shift-comm (τ′ ∷ Γ,Δ ⊐ suc g) i j)
