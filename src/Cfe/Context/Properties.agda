{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Context.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Context.Base over as C
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
open import Data.Fin.Properties using (toℕ-inject₁; toℕ<n)
  renaming
  ( ≤-refl to ≤ᶠ-refl
  ; ≤-reflexive to ≤ᶠ-reflexive
  ; ≤-trans to ≤ᶠ-trans
  ; ≤-antisym to ≤ᶠ-antisym
  )
open import Data.Nat renaming (_≤_ to _≤ⁿ_)
open import Data.Nat.Properties using (module ≤-Reasoning) renaming (≤-reflexive to ≤ⁿ-reflexive)
open import Data.Product
open import Data.Vec using ([]; _∷_; Vec; insert)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as Pw using ([]; _∷_; Pointwise)
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
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
    ∀ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} {n} {xs : Vec A n} {ys : Vec B n} →
    ∀ i j {i≡j : True (toℕ i ≟ toℕ j)} {x y} →
    x ∼ y → Pointwise _∼_ xs ys → Pointwise _∼_ (insert xs i x) (insert ys j y)
  pw-insert zero    zero          x xs       = x ∷ xs
  pw-insert (suc i) (suc j) {i≡j} x (y ∷ xs) =
    y ∷ pw-insert i j {i≡j |> toWitness |> cong pred |> fromWitness} x xs

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
-- Algebraic Properties

wkn₂-mono :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ< i ≟ toℕ< j)} {τ₁ τ₂} →
  τ₁ ≤ᵗ τ₂ → ctx₁ ≤ ctx₂ → wkn₂ {n} ctx₁ i τ₁ ≤ wkn₂ ctx₂ j τ₂
wkn₂-mono i j {i≡j} τ₁≤τ₂ (g₂≤g₁ , Γ,Δ₁≤Γ,Δ₂) =
  s≤s g₂≤g₁ ,
  pw-insert
    (inject<! i) (inject<! j)
    {i≡j |> toWitness |> inject<!-cong |> cong toℕ |> fromWitness}
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

wkn₂-comm :
  ∀ ctx i j τ τ′ →
  wkn₂ (wkn₂ {n} ctx (inject<!′ {j = suc i} j) τ′) (suc i) τ ≈ wkn₂ (wkn₂ ctx i τ) (inject<′ j) τ′
wkn₂-comm (Γ,Δ ⊐ g)          i      zero     τ τ′ = ≈-refl
wkn₂-comm (_ ∷ Γ,Δ ⊐ suc g) (suc i) (suc j) τ τ′ =
  wkn₂-cong zero zero ≈ᵗ-refl (wkn₂-comm (Γ,Δ ⊐ g) i j τ τ′)

------------------------------------------------------------------------
-- Properties of wkn₁
------------------------------------------------------------------------
-- Algebraic Properties

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
    (raise> i) (raise> j)
    {i≡j |> toWitness |> raise>-cong |> cong toℕ |> fromWitness}
    τ₁≤τ₂
    Γ,Δ₁≤Γ,Δ₂
  where open ≤-Reasoning

wkn₁-cong :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ> i ≟ toℕ> j)} →
  ∀ {τ₁ τ₂} → τ₁ ≈ᵗ τ₂ → ctx₁ ≈ ctx₂ → wkn₁ {n} ctx₁ i τ₁ ≈ wkn₁ ctx₂ j τ₂
wkn₁-cong i j {i≡j} τ₁≈τ₂ ctx₁≈ctx₂ =
  ≤-antisym
    (wkn₁-mono i j {i≡j} (≤ᵗ-reflexive τ₁≈τ₂) (≤-reflexive ctx₁≈ctx₂))
    (wkn₁-mono j i
      {i≡j |> toWitness |> sym |> fromWitness}
      (≤ᵗ-reflexive (≈ᵗ-sym τ₁≈τ₂))
      (≤-reflexive (≈-sym ctx₁≈ctx₂)))

wkn₁-comm :
  ∀ ctx i j τ τ′ →
  let g = guard ctx in
  wkn₁ (wkn₁ {n} ctx (inject>!′ {j = suc> i} j) τ′) (suc> i) τ ≈ wkn₁ (wkn₁ ctx i τ) (inject>′ j) τ′
-- wkn₁-comm = {!!}
wkn₁-comm (Γ,Δ ⊐ zero)      zero    zero    τ τ′ = ≈-refl
wkn₁-comm (Γ,Δ ⊐ zero)      (suc i) zero    τ τ′ =
  wkn₁-cong zero zero ≈ᵗ-refl
    (wkn₁-cong (suc> i) (suc i) {toℕ>-suc> i |> fromWitness } ≈ᵗ-refl ≈-refl)
wkn₁-comm (_ ∷ Γ,Δ ⊐ zero)  (suc i) (suc j) τ τ′ =
  wkn₁-cong zero zero ≈ᵗ-refl (wkn₁-comm (Γ,Δ ⊐ zero) i j τ τ′)
wkn₁-comm (_ ∷ Γ,Δ ⊐ suc g) (inj i) (inj j) τ τ′ =
  wkn₂-cong zero zero ≈ᵗ-refl (wkn₁-comm (Γ,Δ ⊐ g) i j τ τ′)

wkn₁-wkn₂-comm :
  ∀ ctx i j τ τ′ →
  wkn₁ (wkn₂ {n} ctx j τ′) (inj i) τ ≈ wkn₂ (wkn₁ ctx i τ) (cast<-inject₁ j) τ′
wkn₁-wkn₂-comm (Γ,Δ ⊐ g)         i       zero    τ τ′ = ≈-refl
wkn₁-wkn₂-comm (_ ∷ Γ,Δ ⊐ suc g) (inj i) (suc j) τ τ′ =
  wkn₂-cong zero zero ≈ᵗ-refl (wkn₁-wkn₂-comm (Γ,Δ ⊐ g) i j τ τ′)

------------------------------------------------------------------------
-- Properties of shift
------------------------------------------------------------------------

shift-mono : ∀ {ctx₁ ctx₂ i j} → toℕ< j ≤ⁿ toℕ< i → ctx₁ ≤ ctx₂ → shift {n} ctx₁ i ≤ shift ctx₂ j
shift-mono {i = i} {j} j≤i (_ , Γ,Δ₁≤Γ,Δ₂) =
  (begin
    toℕ (inject<! j) ≡⟨ toℕ<-inject<! j ⟩
    toℕ< j           ≤⟨ j≤i ⟩
    toℕ< i           ≡˘⟨ toℕ<-inject<! i ⟩
    toℕ (inject<! i) ∎) ,
  Γ,Δ₁≤Γ,Δ₂
  where open ≤-Reasoning

shift-cong :
  ∀ {ctx₁ ctx₂} i j {i≡j : True (toℕ< i ≟ toℕ< j)} → ctx₁ ≈ ctx₂ → shift {n} ctx₁ i ≈ shift ctx₂ j
shift-cong i j {i≡j} ctx₁≈ctx₂ =
  ≤-antisym
    (shift-mono (i≡j |> toWitness |> sym |> ≤ⁿ-reflexive) (≤-reflexive ctx₁≈ctx₂))
    (shift-mono (i≡j |> toWitness |> ≤ⁿ-reflexive) (≤-reflexive (≈-sym ctx₁≈ctx₂)))

shift-identity : ∀ ctx → shift {n} ctx (strengthen< (guard ctx)) ≈ ctx
shift-identity (Γ,Δ ⊐ zero)       = ≈-refl
shift-identity (_ ∷ Γ,Δ ⊐ suc g) = wkn₂-cong zero zero ≈ᵗ-refl (shift-identity (Γ,Δ ⊐ g))

shift-trans : ∀ ctx i j → shift (shift {n} ctx i) (inject<!′-inject! j) ≈ shift {n} ctx (inject<!′ j)
shift-trans (Γ,Δ ⊐ _)         _       zero    = ≈-refl
shift-trans (_ ∷ Γ,Δ ⊐ suc g) (suc i) (suc j) =
  wkn₂-cong zero zero ≈ᵗ-refl (shift-trans (Γ,Δ ⊐ g) i j)

shift-wkn₁-comm :
  ∀ ctx i j τ →
  shift (wkn₁ {n} ctx j τ) (cast<-inject₁ i) ≈ wkn₁ (shift ctx i) (cast>-inject<! i j) τ
shift-wkn₁-comm (Γ,Δ ⊐ zero)      zero    j τ =
  wkn₁-cong j (cast>-inject<! zero j) {toℕ>-cast>-inject<! zero j |> fromWitness} ≈ᵗ-refl ≈-refl
shift-wkn₁-comm (_ ∷ Γ,Δ ⊐ suc g) zero    (inj j) τ =
  wkn₁-cong zero zero ≈ᵗ-refl (shift-wkn₁-comm (Γ,Δ ⊐ g) zero j τ)
shift-wkn₁-comm (_ ∷ Γ,Δ ⊐ suc g) (suc i) (inj j) τ =
  wkn₂-cong zero zero ≈ᵗ-refl (shift-wkn₁-comm (Γ,Δ ⊐ g) i j τ)

shift-wkn₂-comm :
  ∀ ctx i j τ →
  shift (wkn₂ {n} ctx (inject<!′ j) τ) (suc i) ≈ wkn₂ (shift ctx i) (inject<!′-inject! j) τ
shift-wkn₂-comm (Γ,Δ ⊐ g)         i       zero    τ = ≈-refl
shift-wkn₂-comm (_ ∷ Γ,Δ ⊐ suc g) (suc i) (suc j) τ =
  wkn₂-cong zero zero ≈ᵗ-refl (shift-wkn₂-comm (Γ,Δ ⊐ g) i j τ)

shift-wkn₁-wkn₂-comm :
  ∀ ctx i j τ →
  shift (wkn₂ {n} ctx i τ) (inject<′ j) ≈ wkn₁ (shift ctx (inject<!′ j)) (reflect i j) τ
shift-wkn₁-wkn₂-comm (Γ,Δ ⊐ g) zero zero τ = ≈-refl
shift-wkn₁-wkn₂-comm (_ ∷ Γ,Δ ⊐ suc g) (suc i) zero τ = wkn₁-cong zero zero ≈ᵗ-refl (shift-wkn₁-wkn₂-comm (Γ,Δ ⊐ g) i zero τ)
shift-wkn₁-wkn₂-comm (_ ∷ Γ,Δ ⊐ suc g) (suc i) (suc j) τ = wkn₂-cong zero zero ≈ᵗ-refl (shift-wkn₁-wkn₂-comm (Γ,Δ ⊐ g) i j τ)
