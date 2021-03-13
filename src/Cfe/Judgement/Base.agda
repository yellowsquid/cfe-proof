{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Judgement.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Expression over as E
open import Cfe.Type over renaming (_∙_ to _∙ₜ_; _∨_ to _∨ₜ_)
open import Cfe.Type.Construct.Lift over
open import Data.Fin as F
open import Data.Nat as ℕ hiding (_⊔_)
open import Data.Vec hiding (_⊛_)
open import Level hiding (Lift) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality

infix 2 _,_⊢_∶_
infix 4 _≅_

data _,_⊢_∶_ : {m : ℕ} → {n : ℕ} → Vec (Type ℓ ℓ) m → Vec (Type ℓ ℓ) n → Expression (n ℕ.+ m) → Type ℓ ℓ → Set (c ⊔ lsuc ℓ) where
  Eps : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} → Γ , Δ ⊢ ε ∶ Lift ℓ ℓ τε
  Char : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} c → Γ , Δ ⊢ Char c ∶ Lift ℓ ℓ τ[ c ]
  Bot : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} → Γ , Δ ⊢ ⊥ ∶ Lift ℓ ℓ τ⊥
  Var : ∀ {m n : ℕ} {Γ : Vec _ m} {Δ : Vec _ n} {i : Fin (n ℕ.+ m)} (i≥n : toℕ i ≥ n) → Γ , Δ ⊢ Var i ∶ lookup Γ (reduce≥ i i≥n)
  Fix : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} {e τ} → Γ , τ ∷ Δ ⊢ e ∶ τ → Γ , Δ ⊢ μ e ∶ τ
  Cat : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} {e₁ e₂ τ₁ τ₂} → Γ , Δ ⊢ e₁ ∶ τ₁ → Δ ++ Γ , [] ⊢ e₂ ∶ τ₂ → (τ₁⊛τ₂ : τ₁ ⊛ τ₂) → Γ , Δ ⊢ e₁ ∙ e₂ ∶ τ₁ ∙ₜ τ₂
  Vee : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} {e₁ e₂ τ₁ τ₂} → Γ , Δ ⊢ e₁ ∶ τ₁ → Γ , Δ ⊢ e₂ ∶ τ₂ → (τ₁#τ₂ : τ₁ # τ₂) → Γ , Δ ⊢ e₁ ∨ e₂ ∶ τ₁ ∨ₜ τ₂

vcast : ∀ {a A m n} → .(m ≡ n) → Vec {a} A m → Vec A n
vcast {n = suc n} eq (x ∷ xs) = x ∷ vcast (suc-injective eq) xs
  where
  open import Data.Nat.Properties using (suc-injective)
vcast {n = ℕ.zero} eq [] = []

data _≅_ {a A} : {m n : ℕ} → Vec {a} A m → Vec A n → Set a where
  []≅[] : [] ≅ []
  _∷_ : ∀ {m n x y} {xs : Vec _ m} {ys : Vec _ n} → (x≡y : x ≡ y) → xs ≅ ys → x ∷ xs ≅ y ∷ ys

≅-refl : ∀ {a A m} {xs : Vec {a} A m} → xs ≅ xs
≅-refl {xs = []} = []≅[]
≅-refl {xs = x ∷ xs} = refl ∷ ≅-refl

≅-reflexive : ∀ {a A m} {xs : Vec {a} A m} {ys} → xs ≡ ys → xs ≅ ys
≅-reflexive refl = ≅-refl

≅-length : ∀ {a A m n} {xs : Vec {a} A m} {ys : Vec _ n} → xs ≅ ys → m ≡ n
≅-length []≅[] = refl
≅-length (_ ∷ xs≅ys) = cong suc (≅-length xs≅ys)

≅⇒≡ : ∀ {a A m n} {xs : Vec {a} A m} {ys : Vec _ n} → (xs≅ys : xs ≅ ys) → vcast (≅-length xs≅ys) xs ≡ ys
≅⇒≡ []≅[] = refl
≅⇒≡ (x≡y ∷ xs≅ys) = cong₂ _∷_ x≡y (≅⇒≡ xs≅ys)

++ˡ : ∀ {a A m n k} {xs : Vec {a} A m} {ys : Vec _ n} (zs : Vec _ k) → xs ≅ ys → zs ++ xs ≅ zs ++ ys
++ˡ [] xs≅ys = xs≅ys
++ˡ (z ∷ zs) xs≅ys = refl ∷ ++ˡ zs xs≅ys

cast₁ : ∀ {m₁ m₂ n} {Γ₁ : Vec _ m₁} {Γ₂ : Vec _ m₂} {Δ : Vec _ n} {e τ} → (eq : Γ₁ ≅ Γ₂) → Γ₁ , Δ ⊢ e ∶ τ → Γ₂ , Δ ⊢ E.cast (cong (n ℕ.+_) (≅-length eq)) e ∶ τ
cast₁ eq Eps = Eps
cast₁ eq (Char c) = Char c
cast₁ eq Bot = Bot
cast₁ {n = n} {Γ₁} {Δ = Δ} eq (Var {i = i} i≥n) =
  subst₂ (_, Δ ⊢ E.cast (cong (n ℕ.+_) (≅-length eq)) (Var i) ∶_)
         (≅⇒≡ eq)
         (eq′ Γ₁ i≥n (≅-length eq))
         (Var (ge (≅-length eq) i≥n))
  where
  open import Data.Empty using (⊥-elim)
  open import Data.Fin.Properties using (toℕ<n; toℕ-cast; toℕ-injective)
  open import Data.Nat.Properties using (<⇒≱; +-identityʳ; module ≤-Reasoning)

  ge : ∀ {m₁ m₂ n i} → .(eq : m₁ ≡ m₂) → toℕ {n ℕ.+ m₁} i ≥ n → toℕ (F.cast (cong (n ℕ.+_) eq) i) ≥ n
  ge {n = ℕ.zero} {i} _ _ = z≤n
  ge {n = suc n} {suc i} eq (s≤s i≥n) = s≤s (ge eq i≥n)

  eq′ : ∀ {a A m₁ m₂ n i} Γ i≥n → (eq : m₁ ≡ m₂) → lookup {a} {A} {m₂} (vcast eq Γ) (reduce≥ {n} (F.cast (cong (n ℕ.+_) eq) i) (ge eq i≥n)) ≡ lookup Γ (reduce≥ i i≥n)
  eq′ {m₁ = ℕ.zero} {ℕ.zero} {n} {i} Γ i≥n _ = ⊥-elim (<⇒≱ (begin-strict
    toℕ i <⟨ toℕ<n i ⟩
    n ℕ.+ 0 ≡⟨ +-identityʳ n ⟩
    n ∎) i≥n)
    where
    open ≤-Reasoning
  eq′ {m₁ = suc m₁} {suc m₁} {ℕ.zero} {i} Γ i≥n refl = cong₂ lookup {vcast refl Γ} (≅⇒≡ ≅-refl) (toℕ-injective (toℕ-cast refl i))
  eq′ {m₁ = suc m₁} {suc m₂} {suc n} {suc i} Γ (s≤s i≥n) eq = eq′ Γ i≥n eq
cast₁ eq (Fix Γ₁,τ∷Δ⊢e∶τ) = Fix (cast₁ eq Γ₁,τ∷Δ⊢e∶τ)
cast₁ {Δ = Δ} eq (Cat Γ₁,Δ⊢e₁∶τ₁ Δ++Γ₁,∙⊢e₂∶τ₂ τ₁⊛τ₂) = Cat (cast₁ eq Γ₁,Δ⊢e₁∶τ₁) (cast₁ (++ˡ Δ eq) Δ++Γ₁,∙⊢e₂∶τ₂) τ₁⊛τ₂
cast₁ eq (Vee Γ₁,Δ⊢e₁∶τ₁ Γ₁,Δ⊢e₂∶τ₂ τ₁#τ₂) = Vee (cast₁ eq Γ₁,Δ⊢e₁∶τ₁) (cast₁ eq Γ₁,Δ⊢e₂∶τ₂) τ₁#τ₂
