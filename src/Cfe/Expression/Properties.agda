{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Expression.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C)

open import Algebra
open import Cfe.Expression.Base over as E
open import Cfe.Language over as L
import Cfe.Language.Construct.Concatenate over as ∙
import Cfe.Language.Construct.Union over as ∪
import Cfe.Language.Indexed.Construct.Iterate over as ⋃
open import Data.Fin as F
open import Data.Fin.Properties
open import Data.Nat as ℕ hiding (_⊔_)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Vec
open import Data.Vec.Properties
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
open import Function
open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Nullary

isEquivalence : ∀ n → IsEquivalence (_≋_ {n})
isEquivalence n = record
  { refl = λ γ → ≈-refl
  ; sym = λ x≋y γ → ≈-sym (x≋y γ)
  ; trans = λ x≋y y≋z γ → ≈-trans (x≋y γ) (y≋z γ)
  }

isSemiring : ∀ n → IsSemiring (_≋_ {n}) _∨_ _∙_ ⊥ ε
isSemiring n = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = isEquivalence n
            ; ∙-cong = λ x≋y u≋v γ → ∪-comm.∙-cong (x≋y γ) (u≋v γ)
            }
          ; assoc = λ x y z γ → ∪-comm.assoc (⟦ x ⟧ γ) (⟦ y ⟧ γ) (⟦ z ⟧ γ)
          }
        ; identity = (λ x γ → ∪-comm.identityˡ (⟦ x ⟧ γ)) , (λ x γ → ∪-comm.identityʳ (⟦ x ⟧ γ))
        }
      ; comm = λ x y γ → ∪-comm.comm (⟦ x ⟧ γ) (⟦ y ⟧ γ)
      }
    ; *-isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = isEquivalence n
          ; ∙-cong = λ x≋y u≋v γ → ∙-mon.∙-cong (x≋y γ) (u≋v γ)
          }
        ; assoc = λ x y z γ → ∙-mon.assoc (⟦ x ⟧ γ) (⟦ y ⟧ γ) (⟦ z ⟧ γ)
        }
      ; identity = (λ x γ → ∙-mon.identityˡ (⟦ x ⟧ γ)) , (λ x γ → ∙-mon.identityʳ (⟦ x ⟧ γ))
      }
    ; distrib = (λ x y z γ → record
      { f = λ
        { (l₁ , l₁∈⟦x⟧ , l₂ , inj₁ l₂∈⟦y⟧ , l₁++l₂≡l) → inj₁ (-, l₁∈⟦x⟧ , -, l₂∈⟦y⟧ , l₁++l₂≡l)
        ; (l₁ , l₁∈⟦x⟧ , l₂ , inj₂ l₂∈⟦z⟧ , l₁++l₂≡l) → inj₂ (-, l₁∈⟦x⟧ , -, l₂∈⟦z⟧ , l₁++l₂≡l)
        }
      ; f⁻¹ = λ
        { (inj₁ (l₁ , l₁∈⟦x⟧ , l₂ , l₂∈⟦y⟧ , l₁++l₂≡l)) → -, l₁∈⟦x⟧ , -, inj₁ l₂∈⟦y⟧ , l₁++l₂≡l
        ; (inj₂ (l₁ , l₁∈⟦x⟧ , l₂ , l₂∈⟦z⟧ , l₁++l₂≡l)) → -, l₁∈⟦x⟧ , -, inj₂ l₂∈⟦z⟧ , l₁++l₂≡l
        }
      }) , (λ x y z γ → record
      { f = λ
        { (l₁ , inj₁ l₁∈⟦y⟧ , l₂ , l₂∈⟦x⟧ , l₁++l₂≡l) → inj₁ (-, l₁∈⟦y⟧ , -, l₂∈⟦x⟧ , l₁++l₂≡l)
        ; (l₁ , inj₂ l₁∈⟦z⟧ , l₂ , l₂∈⟦x⟧ , l₁++l₂≡l) → inj₂ (-, l₁∈⟦z⟧ , -, l₂∈⟦x⟧ , l₁++l₂≡l)
        }
      ; f⁻¹ = λ
        { (inj₁ (l₁ , l₁∈⟦y⟧ , l₂ , l₂∈⟦x⟧ , l₁++l₂≡l)) → -, inj₁ l₁∈⟦y⟧ , -, l₂∈⟦x⟧ , l₁++l₂≡l
        ; (inj₂ (l₁ , l₁∈⟦z⟧ , l₂ , l₂∈⟦x⟧ , l₁++l₂≡l)) → -, inj₂ l₁∈⟦z⟧ , -, l₂∈⟦x⟧ , l₁++l₂≡l
        }
      })
    }
  ; zero = (λ x γ → record
    { f = λ ()
    ; f⁻¹ = λ ()
    }) , (λ x γ → record
    { f = λ ()
    ; f⁻¹ = λ ()
    })
  }
  where
  module ∪-comm = IsCommutativeMonoid (∪.isCommutativeMonoid {c ⊔ ℓ})
  module ∙-mon = IsMonoid (∙.isMonoid {ℓ})

module _ where
  open import Data.Vec.Relation.Binary.Equality.Setoid (L.setoid (c ⊔ ℓ)) as VE
  open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW

  cong-env : ∀ {n} → (e : Expression n) → ∀ {γ γ′} → γ VE.≋ γ′ → ⟦ e ⟧ γ ≈ ⟦ e ⟧ γ′
  cong-env ⊥ γ≈γ′ = ≈-refl
  cong-env ε γ≈γ′ = ≈-refl
  cong-env (Char x) γ≈γ′ = ≈-refl
  cong-env (e₁ ∨ e₂) γ≈γ′ = ∪-cong (cong-env e₁ γ≈γ′) (cong-env e₂ γ≈γ′)
    where
    open IsCommutativeMonoid (∪.isCommutativeMonoid {c ⊔ ℓ}) renaming (∙-cong to ∪-cong)
  cong-env (e₁ ∙ e₂) γ≈γ′ = ∙-cong (cong-env e₁ γ≈γ′) (cong-env e₂ γ≈γ′)
    where
    open IsMonoid (∙.isMonoid {c ⊔ ℓ})
  cong-env (Var j) γ≈γ′ = PW.lookup γ≈γ′ j
  cong-env (μ e) γ≈γ′ = ⋃.⋃-cong (λ x → cong-env e (x PW.∷ γ≈γ′))

wkn-no-use : ∀ {n} → (e : Expression n) → ∀ i γ → ⟦ wkn e i ⟧ γ ≈ ⟦ e ⟧ (remove γ i)
wkn-no-use ⊥ i γ = ≈-refl
wkn-no-use ε i γ = ≈-refl
wkn-no-use (Char x) i γ = ≈-refl
wkn-no-use (e₁ ∨ e₂) i γ = ∪-cong (wkn-no-use e₁ i γ) (wkn-no-use e₂ i γ)
  where
  open IsCommutativeMonoid (∪.isCommutativeMonoid {c ⊔ ℓ}) renaming (∙-cong to ∪-cong)
wkn-no-use (e₁ ∙ e₂) i γ = ∙-cong (wkn-no-use e₁ i γ) (wkn-no-use e₂ i γ)
  where
  open IsMonoid (∙.isMonoid {c ⊔ ℓ})
wkn-no-use (Var j) i γ = reflexive (begin
  lookup γ (punchIn i j)                                    ≡˘⟨ ≡.cong (λ x → lookup x (punchIn i j)) (insert-remove γ i) ⟩
  lookup (insert (remove γ i) i (lookup γ i)) (punchIn i j) ≡⟨ insert-punchIn (remove γ i) i (lookup γ i) j ⟩
  lookup (remove γ i) j                                     ∎)
  where
  open IsEquivalence (≈-isEquivalence {c ⊔ ℓ})
  open ≡.≡-Reasoning
wkn-no-use (μ e) i (z ∷ γ) = ⋃.⋃-cong (λ {x} {y} x≈y → begin
  ⟦ wkn e (suc i) ⟧ (x ∷ z ∷ γ)      ≈⟨ cong-env (wkn e (suc i)) (x≈y ∷ ≋-refl) ⟩
  ⟦ wkn e (suc i) ⟧ (y ∷ z ∷ γ)      ≈⟨ wkn-no-use e (suc i) (y ∷ z ∷ γ) ⟩
  ⟦ e ⟧ (remove (y ∷ z ∷ γ) (suc i)) ≡⟨⟩
  ⟦ e ⟧ (y ∷ remove (z ∷ γ) i)       ∎)
  where
  open import Relation.Binary.Reasoning.Setoid (L.setoid (c ⊔ ℓ))
  open import Data.Vec.Relation.Binary.Equality.Setoid (L.setoid (c ⊔ ℓ)) as VE

subst-fun : ∀ {n} → (e : Expression (suc n)) → ∀ e′ i γ → ⟦ e [ e′ / i ] ⟧ γ ≈ ⟦ e ⟧ (insert γ i (⟦ e′ ⟧ γ))
subst-fun ⊥ e′ i γ = ≈-refl
subst-fun ε e′ i γ = ≈-refl
subst-fun (Char x) e′ i γ = ≈-refl
subst-fun {n} (e₁ ∨ e₂) e′ i γ = ∪-cong (subst-fun e₁ e′ i γ) (subst-fun e₂ e′ i γ)
  where
  open IsCommutativeMonoid (∪.isCommutativeMonoid {c ⊔ ℓ}) renaming (∙-cong to ∪-cong)
subst-fun (e₁ ∙ e₂) e′ i γ = ∙-cong (subst-fun e₁ e′ i γ) (subst-fun e₂ e′ i γ)
  where
  open IsMonoid (∙.isMonoid {c ⊔ ℓ})
subst-fun (Var j) e′ i γ with i F.≟ j
... | yes _≡_.refl = sym (reflexive (insert-lookup γ i (⟦ e′ ⟧ γ)))
  where
  open IsEquivalence (≈-isEquivalence {c ⊔ ℓ})
... | no i≢j = reflexive (begin
                 lookup γ (punchOut i≢j) ≡˘⟨ ≡.cong (λ x → lookup x (punchOut i≢j)) (remove-insert γ i (⟦ e′ ⟧ γ)) ⟩
                 lookup (remove (insert γ i (⟦ e′ ⟧ γ)) i) (punchOut i≢j) ≡⟨ remove-punchOut (insert γ i (⟦ e′ ⟧ γ)) i≢j ⟩
                 lookup (insert γ i (⟦ e′ ⟧ γ)) j ∎)
  where
  open ≡.≡-Reasoning
  open IsEquivalence (≈-isEquivalence {c ⊔ ℓ})
subst-fun (μ e) e′ i γ = ⋃.⋃-cong λ {x} {y} x≈y → begin
  ⟦ e [ wkn e′ F.zero / suc i ] ⟧ (x ∷ γ) ≈⟨ cong-env (e [ wkn e′ F.zero / suc i ]) (x≈y ∷ ≋-refl) ⟩
  ⟦ e [ wkn e′ F.zero / suc i ] ⟧ (y ∷ γ) ≈⟨ subst-fun e (wkn e′ F.zero) (suc i) (y ∷ γ) ⟩
  ⟦ e ⟧ (y ∷ insert γ i (⟦ wkn e′ F.zero ⟧ (y ∷ γ))) ≈⟨ cong-env e (≈-refl ∷ insert′ (wkn-no-use e′ F.zero (y ∷ γ)) ≋-refl i) ⟩
  ⟦ e ⟧ (y ∷ insert γ i (⟦ e′ ⟧ γ)) ∎
  where
  open import Relation.Binary.Reasoning.Setoid (L.setoid (c ⊔ ℓ))
  open import Data.Vec.Relation.Binary.Equality.Setoid (L.setoid (c ⊔ ℓ)) as VE

  insert′ : ∀ {n x y} {xs ys : Vec (Language (c ⊔ ℓ)) n} → x ≈ y → xs VE.≋ ys → (i : Fin (suc n)) → insert xs i x VE.≋ insert ys i y
  insert′ x≈y xs≋ys F.zero = x≈y ∷ xs≋ys
  insert′ x≈y (z≈w ∷ xs≋ys) (suc i) = z≈w ∷ insert′ x≈y xs≋ys i

mono : ∀ {n} (e : Expression n) → ⟦ e ⟧ Preserves PW.Pointwise L._≤_ ⟶ L._≤_
mono ⊥ γ≤γ′ = L.≤-refl
mono ε γ≤γ′ = L.≤-refl
mono (Char x) γ≤γ′ = L.≤-refl
mono (e₁ ∨ e₂) γ≤γ′ = ∪.∪-mono (mono e₁ γ≤γ′) (mono e₂ γ≤γ′)
mono (e₁ ∙ e₂) γ≤γ′ = ∙.∙-mono (mono e₁ γ≤γ′) (mono e₂ γ≤γ′)
mono (Var i) γ≤γ′ = PW.lookup γ≤γ′ i
mono (μ e) γ≤γ′ = ⋃.⋃-mono (λ x≤y → mono e (x≤y PW.∷ γ≤γ′))

cast-inverse : ∀ {m n} e → .(m≡n : m ≡ n) → .(n≡m : n ≡ m) → E.cast m≡n (E.cast n≡m e) ≡ e
cast-inverse ⊥ m≡n n≡m = ≡.refl
cast-inverse ε m≡n n≡m = ≡.refl
cast-inverse (Char x) m≡n n≡m = ≡.refl
cast-inverse (e₁ ∨ e₂) m≡n n≡m = ≡.cong₂ _∨_ (cast-inverse e₁ m≡n n≡m) (cast-inverse e₂ m≡n n≡m)
cast-inverse (e₁ ∙ e₂) m≡n n≡m = ≡.cong₂ _∙_ (cast-inverse e₁ m≡n n≡m) (cast-inverse e₂ m≡n n≡m)
cast-inverse (Var x) m≡n n≡m = ≡.cong Var (toℕ-injective (begin
  toℕ (F.cast m≡n (F.cast n≡m x)) ≡⟨ toℕ-cast m≡n (F.cast n≡m x) ⟩
  toℕ (F.cast n≡m x)              ≡⟨ toℕ-cast n≡m x ⟩
  toℕ x                           ∎))
  where
  open ≡.≡-Reasoning
cast-inverse (μ e) m≡n n≡m = ≡.cong μ (cast-inverse e (≡.cong suc m≡n) (≡.cong suc n≡m))

cast-involutive : ∀ {k m n} e → .(k≡m : k ≡ m) → .(m≡n : m ≡ n) → .(k≡n : k ≡ n) → E.cast m≡n (E.cast k≡m e) ≡ E.cast k≡n e
cast-involutive ⊥ k≡m m≡n k≡n = ≡.refl
cast-involutive ε k≡m m≡n k≡n = ≡.refl
cast-involutive (Char x) k≡m m≡n k≡n = ≡.refl
cast-involutive (e₁ ∨ e₂) k≡m m≡n k≡n = ≡.cong₂ _∨_ (cast-involutive e₁ k≡m m≡n k≡n) (cast-involutive e₂ k≡m m≡n k≡n)
cast-involutive (e₁ ∙ e₂) k≡m m≡n k≡n = ≡.cong₂ _∙_ (cast-involutive e₁ k≡m m≡n k≡n) (cast-involutive e₂ k≡m m≡n k≡n)
cast-involutive (Var x) k≡m m≡n k≡n = ≡.cong Var (toℕ-injective (begin
  toℕ (F.cast m≡n (F.cast k≡m x)) ≡⟨ toℕ-cast m≡n (F.cast k≡m x) ⟩
  toℕ (F.cast k≡m x)              ≡⟨ toℕ-cast k≡m x ⟩
  toℕ x                           ≡˘⟨ toℕ-cast k≡n x ⟩
  toℕ (F.cast k≡n x)              ∎))
  where
  open ≡.≡-Reasoning
cast-involutive (μ e) k≡m m≡n k≡n = ≡.cong μ (cast-involutive e (≡.cong suc k≡m) (≡.cong suc m≡n) (≡.cong suc k≡n))
