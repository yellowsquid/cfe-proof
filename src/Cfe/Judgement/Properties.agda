{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Cfe.Judgement.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Expression over
open import Cfe.Judgement.Base over
open import Cfe.Type over
open import Data.Empty
open import Data.Fin as F hiding (cast)
open import Data.Fin.Properties
open import Data.Nat as ℕ
open import Data.Nat.Properties as NP
open import Data.Vec
open import Data.Vec.Properties
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

private
  raise-mono : ∀ {m n i j} → i F.≤ j → raise {n} m i F.≤ raise m j
  raise-mono {zero} i≤j = i≤j
  raise-mono {suc m} i≤j = s≤s (raise-mono i≤j)

  raise≤ : ∀ {m} n i → n ℕ.≤ toℕ (raise {m} n i)
  raise≤ zero i = z≤n
  raise≤ (suc n) i = s≤s (raise≤ n i)

  inject+≤raise : ∀ {m n} i j → inject+ {suc n} m i F.≤ F.cast (+-suc n m) (raise {suc m} n j)
  inject+≤raise {m} {n} i j = begin
    toℕ (inject+ m i)          ≡˘⟨ toℕ-inject+ m i ⟩
    toℕ i                      ≤⟨ NP.<⇒≤pred (toℕ<n i) ⟩
    n                          ≤⟨ m≤m+n n (toℕ j) ⟩
    n ℕ.+ toℕ j                ≡˘⟨ toℕ-raise n j ⟩
    toℕ (raise n j)            ≡˘⟨ toℕ-cast (+-suc n m) (raise n j) ⟩
    toℕ (F.cast _ (raise n j)) ∎
    where
    open ≤-Reasoning

  toℕ-punchIn : ∀ {m} i j → toℕ j ℕ.≤ toℕ (punchIn {m} i j)
  toℕ-punchIn zero j = n≤1+n (toℕ j)
  toℕ-punchIn (suc i) zero = z≤n
  toℕ-punchIn (suc i) (suc j) = s≤s (toℕ-punchIn i j)

  toℕ-punchOut : ∀ {m i j} → (i≢j : i ≢ j) → toℕ j ℕ.≤ suc (toℕ (punchOut {m} i≢j))
  toℕ-punchOut {_} {zero} {zero} i≢j = ⊥-elim (i≢j refl)
  toℕ-punchOut {_} {zero} {suc j} i≢j = NP.≤-refl
  toℕ-punchOut {suc m} {suc i} {zero} i≢j = z≤n
  toℕ-punchOut {suc m} {suc i} {suc j} i≢j = s≤s (toℕ-punchOut (i≢j ∘ cong suc))

  toℕ-reduce : ∀ {m n} i i≥m → toℕ (reduce≥ {m} {n} i i≥m) ≡ toℕ i ∸ m
  toℕ-reduce {zero} i i≥m = refl
  toℕ-reduce {suc m} (suc i) (s≤s i≥m) = toℕ-reduce i i≥m

  <⇒punchOut≤ : ∀ {m n i j} → n ℕ.< toℕ j → (i≢j : i ≢ j) → n ℕ.≤ toℕ (punchOut {m} i≢j)
  <⇒punchOut≤ {m} {n} {zero} {suc j} (s≤s n<j) i≢j = n<j
  <⇒punchOut≤ {suc m} {zero} {suc i} {suc j} (s≤s n<j) i≢j = z≤n
  <⇒punchOut≤ {suc m} {suc n} {suc i} {suc j} (s≤s n<j) i≢j = s≤s (<⇒punchOut≤ n<j (i≢j ∘ cong suc))

  punchIn-∸ : ∀ {m n} i {j} j≥n → toℕ (punchIn (F.cast (+-suc n m) (raise n i)) j) ∸ n ≡ toℕ (punchIn i (reduce≥ j j≥n))
  punchIn-∸ {zero} {n} zero {j} j≥n = ⊥-elim (<⇒≱ (begin-strict
    toℕ j ≡˘⟨ toℕ-cast (+-identityʳ n) j ⟩
    toℕ (F.cast _ j) <⟨ toℕ<n (F.cast _ j) ⟩
    n ∎) j≥n)
    where
    open ≤-Reasoning
  punchIn-∸ {suc m} {zero} zero {j} z≤n = refl
  punchIn-∸ {suc m} {suc n} zero {suc j} (s≤s j≥n) = punchIn-∸ zero j≥n
  punchIn-∸ {suc m} {zero} (suc i) {zero} z≤n = refl
  punchIn-∸ {suc m} {zero} (suc i) {suc j} z≤n = cong suc (punchIn-∸ i z≤n)
  punchIn-∸ {suc m} {suc n} (suc i) {suc j} (s≤s j≥n) = punchIn-∸ (suc i) j≥n

≅-refl : ∀ {a A m} {xs : Vec {a} A m} → xs ≅ xs
≅-refl {xs = []} = []≅[]
≅-refl {xs = x ∷ xs} = refl ∷ ≅-refl

≅-reflexive : ∀ {a A m} {xs : Vec {a} A m} {ys} → xs ≡ ys → xs ≅ ys
≅-reflexive refl = ≅-refl

≅-length : ∀ {a A m n} {xs : Vec {a} A m} {ys : Vec _ n} → xs ≅ ys → m ≡ n
≅-length []≅[] = refl
≅-length (_ ∷ xs≅ys) = cong suc (≅-length xs≅ys)

≅-vcast : ∀ {a A m n} {xs : Vec {a} A m} → .(m≡n : m ≡ n) → vcast m≡n xs ≅ xs
≅-vcast {n = zero} {[]} m≡n = []≅[]
≅-vcast {n = suc n} {x ∷ xs} m≡n = refl ∷ ≅-vcast (NP.suc-injective m≡n)

≅⇒≡ : ∀ {a A m n} {xs : Vec {a} A m} {ys : Vec _ n} → (xs≅ys : xs ≅ ys) → vcast (≅-length xs≅ys) xs ≡ ys
≅⇒≡ []≅[] = refl
≅⇒≡ (x≡y ∷ xs≅ys) = cong₂ _∷_ x≡y (≅⇒≡ xs≅ys)

++ˡ : ∀ {a A m n k} {xs : Vec {a} A m} {ys : Vec _ n} (zs : Vec _ k) → xs ≅ ys → zs ++ xs ≅ zs ++ ys
++ˡ [] xs≅ys = xs≅ys
++ˡ (z ∷ zs) xs≅ys = refl ∷ ++ˡ zs xs≅ys

cast₁ : ∀ {m₁ m₂ n} {Γ₁ : Vec _ m₁} {Γ₂ : Vec _ m₂} {Δ : Vec _ n} {e τ} → (eq : Γ₁ ≅ Γ₂) → Γ₁ , Δ ⊢ e ∶ τ → Γ₂ , Δ ⊢ cast (cong (n ℕ.+_) (≅-length eq)) e ∶ τ
cast₁ eq Eps = Eps
cast₁ eq (Char c) = Char c
cast₁ eq Bot = Bot
cast₁ {n = n} {Γ₁} {Δ = Δ} eq (Var {i = i} i≥n) =
  subst₂ (_, Δ ⊢ cast (cong (n ℕ.+_) (≅-length eq)) (Var i) ∶_)
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

wkn₁ : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} {e τ} →
       Γ , Δ ⊢ e ∶ τ →
       ∀ τ′ i →
       insert Γ i τ′ , Δ ⊢ cast (sym (+-suc n m)) (wkn e (F.cast (+-suc n m) (raise n i))) ∶ τ
wkn₁ Eps τ′ i = Eps
wkn₁ (Char c) τ′ i = Char c
wkn₁ Bot τ′ i = Bot
wkn₁ {m} {n} {Γ} {Δ} {e} {τ} (Var {i = j} j≥n) τ′ i =
  subst (insert Γ i τ′ , Δ ⊢ cast (sym (+-suc n m)) (Var (punchIn (F.cast (+-suc n m) (raise n i)) j)) ∶_)
        eq
        (Var le)
  where
  le : toℕ (F.cast _ (punchIn (F.cast _ (raise n i)) j)) ≥ n
  le  = begin
    n ≤⟨ j≥n ⟩
    toℕ j ≤⟨ toℕ-punchIn (F.cast (+-suc n m) (raise n i)) j ⟩
    toℕ (punchIn (F.cast _ (raise n i)) j) ≡˘⟨ toℕ-cast (sym (+-suc n m)) (punchIn (F.cast _ (raise n i)) j) ⟩
    toℕ (F.cast _ (punchIn (F.cast _ (raise n i)) j)) ∎
    where
    open ≤-Reasoning

  lookup-cast : ∀ {a A n} l j → lookup {a} {A} {n} l (F.cast refl j) ≡ lookup l j
  lookup-cast l zero = refl
  lookup-cast (x ∷ l) (suc j) = lookup-cast l j

  missing-link : reduce≥ (F.cast _ (punchIn (F.cast _ (raise n i)) j)) le ≡ punchIn i (reduce≥ j j≥n)
  missing-link = toℕ-injective (begin
    toℕ (reduce≥ (F.cast _ (punchIn (F.cast _ (raise n i)) j)) le) ≡⟨ toℕ-reduce (F.cast _ (punchIn (F.cast _ (raise n i)) j)) le ⟩
    toℕ (F.cast _ (punchIn (F.cast _ (raise n i)) j)) ∸ n ≡⟨ cong (_∸ n) (toℕ-cast _ (punchIn (F.cast _ (raise n i)) j)) ⟩
    toℕ (punchIn (F.cast _ (raise n i)) j) ∸ n ≡⟨ punchIn-∸ i j≥n ⟩
    toℕ (punchIn i (reduce≥ j j≥n)) ∎)
    where
    open ≡-Reasoning

  eq : lookup (insert Γ i τ′) (reduce≥ (F.cast _ (punchIn (F.cast _ (raise n i)) j)) le) ≡ lookup Γ (reduce≥ j j≥n)
  eq = begin
    lookup (insert Γ i τ′) (reduce≥ (F.cast _ (punchIn (F.cast _ (raise n i)) j)) le) ≡⟨ cong (lookup (insert Γ i τ′)) missing-link ⟩
    lookup (insert Γ i τ′) (punchIn i (reduce≥ j j≥n)) ≡⟨ insert-punchIn Γ i τ′ (reduce≥ j j≥n) ⟩
    lookup Γ (reduce≥ j j≥n) ∎
    where
    open ≡-Reasoning

wkn₁ (Fix Γ,τ∷Δ⊢e∶τ) τ′ i = Fix (wkn₁ Γ,τ∷Δ⊢e∶τ τ′ i)
wkn₁{m} {n} {Γ} {Δ} (Cat {e₂ = e₂} {τ₂ = τ₂} Γ,Δ⊢e₁∶τ₁ Δ++Γ,∙⊢e₂∶τ₂ τ₁⊛τ₂) τ′ i =
  Cat (wkn₁ Γ,Δ⊢e₁∶τ₁  τ′ i)
      (subst (λ x → Δ ++ insert Γ i τ′ , [] ⊢ x ∶ τ₂)
             (begin
               cast _ (cast _ (wkn e₂ (F.cast refl (raise zero (F.cast _ (raise n i)))))) ≡⟨⟩
               cast _ (cast _ (wkn e₂ (F.cast refl (F.cast _ (raise n i))))) ≡⟨ cast-involutive (wkn e₂ (F.cast refl (F.cast _ (raise n i)))) refl (sym (+-suc n m)) (sym (+-suc n m)) ⟩
               cast _ (wkn e₂ (F.cast refl (F.cast _ (raise n i)))) ≡⟨ cong (λ x → cast (sym (+-suc n m)) (wkn e₂ x)) (fcast-involutive (raise n i) (+-suc n m) refl (+-suc n m)) ⟩
               cast _ (wkn e₂ (F.cast _ (raise n i))) ∎)
             (cast₁ (eq Γ Δ τ′ i) (wkn₁ Δ++Γ,∙⊢e₂∶τ₂ τ′ (F.cast (+-suc n m) (raise n i)))))
      τ₁⊛τ₂
  where
  open ≡-Reasoning
  eq : ∀ {a A m n} Γ Δ τ′ i → insert (Δ ++ Γ) (F.cast (+-suc n m) (raise n i)) τ′ ≅ Δ ++ insert {a} {A} {m} Γ i τ′
  eq Γ [] τ′ zero = ≅-refl
  eq (x ∷ Γ) [] τ′ (suc i) = refl ∷ eq Γ [] τ′ i
  eq Γ (x ∷ Δ) τ′ i = refl ∷ (eq Γ Δ τ′ i)

  fcast-involutive : ∀ {k m n} i → .(k≡m : k ≡ m) → .(m≡n : m ≡ n) → .(k≡n : k ≡ n) → F.cast m≡n (F.cast k≡m i) ≡ F.cast k≡n i
  fcast-involutive i k≡m m≡n k≡n = toℕ-injective (begin
    toℕ (F.cast m≡n (F.cast k≡m i)) ≡⟨ toℕ-cast m≡n (F.cast k≡m i) ⟩
    toℕ (F.cast k≡m i) ≡⟨ toℕ-cast k≡m i ⟩
    toℕ i ≡˘⟨ toℕ-cast k≡n i ⟩
    toℕ (F.cast k≡n i) ∎)
wkn₁ (Vee Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e₂∶τ₂ τ₁#τ₂) τ′ i = Vee (wkn₁ Γ,Δ⊢e₁∶τ₁ τ′ i) (wkn₁ Γ,Δ⊢e₂∶τ₂ τ′ i) τ₁#τ₂

wkn₂ : ∀ {m n} {Γ : Vec _ m} {Δ : Vec _ n} {e τ} →
       Γ , Δ ⊢ e ∶ τ →
       ∀ τ′ i →
       Γ , insert Δ i τ′ ⊢ wkn e (inject+ m i) ∶ τ
wkn₂ Eps τ′ i = Eps
wkn₂ (Char c) τ′ i = Char c
wkn₂ Bot τ′ i = Bot
wkn₂ {m} {n} {Γ} {Δ} (Var {i = j} j≥n) τ′ i =
  subst (Γ , insert Δ i τ′ ⊢_∶ lookup Γ (reduce≥ j j≥n))
        (cong Var (toℕ-injective (begin-equality
          toℕ (suc j) ≡⟨⟩
          suc (toℕ j) ≡˘⟨ cong toℕ (punchIn-suc i≤j) ⟩
          toℕ (punchIn (inject+ m i) j) ∎)))
        (Var (s≤s j≥n))
  where
  open ≤-Reasoning

  i≤j : toℕ (inject+ m i) ℕ.≤ toℕ j
  i≤j = begin
    toℕ (inject+ m i) ≡˘⟨ toℕ-inject+ m i ⟩
    toℕ i ≤⟨ NP.<⇒≤pred (toℕ<n i) ⟩
    n ≤⟨ j≥n ⟩
    toℕ j ∎

  punchIn-suc : ∀ {m i j} → toℕ i ℕ.≤ toℕ j → punchIn {m} i j ≡ suc j
  punchIn-suc {_} {zero} {j} i≤j = refl
  punchIn-suc {_} {suc i} {suc j} (s≤s i≤j) = cong suc (punchIn-suc i≤j)
wkn₂ (Fix Γ,τ∷Δ⊢e∶τ) τ′ i = Fix (wkn₂ Γ,τ∷Δ⊢e∶τ τ′ (suc i))
wkn₂ {m} {n} {Γ} {Δ} (Cat {e₂ = e₂} {τ₂ = τ₂} Γ,Δ⊢e₁∶τ₁ Δ++Γ,∙⊢e₂∶τ₂ τ₁⊛τ₂) τ′ i =
  Cat (wkn₂ Γ,Δ⊢e₁∶τ₁ τ′ i)
      (subst (insert Δ i τ′ ++ Γ , [] ⊢_∶ τ₂)
             (begin
               cast refl (cast refl (wkn e₂ (F.cast refl (inject+ m i)))) ≡⟨ cast-inverse (wkn e₂ (F.cast refl (inject+ m i))) refl refl ⟩
               wkn e₂ (F.cast refl (inject+ m i)) ≡⟨ cong (wkn e₂) (toℕ-injective (toℕ-cast refl (inject+ m i))) ⟩
               wkn e₂ (inject+ m i) ∎)
             (cast₁ (≅-reflexive (eq Γ Δ τ′ i)) (wkn₁ Δ++Γ,∙⊢e₂∶τ₂ τ′ (inject+ m i))))
      τ₁⊛τ₂
  where
  open ≡-Reasoning

  eq : ∀ {a A m n} Γ Δ τ i → insert (Δ ++ Γ) (inject+ m i) τ ≡ insert {a} {A} {n} Δ i τ ++ Γ
  eq Γ Δ τ zero = refl
  eq Γ (_ ∷ Δ) τ (suc i) = cong₂ _∷_ refl (eq Γ Δ τ i)
wkn₂ (Vee Γ,Δ⊢e₁∶τ₁ Γ,Δ⊢e₂∶τ₂ τ₁#τ₂) τ′ i = Vee (wkn₂ Γ,Δ⊢e₁∶τ₁ τ′ i) (wkn₂ Γ,Δ⊢e₂∶τ₂ τ′ i) τ₁#τ₂
