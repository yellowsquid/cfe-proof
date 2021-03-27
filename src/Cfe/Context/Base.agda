{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; Rel)

module Cfe.Context.Base
  {c ℓ} (over : Setoid c ℓ)
  where

open import Cfe.Type over
open import Data.Empty
open import Data.Fin as F hiding (cast)
open import Data.Fin.Properties hiding (≤-trans)
open import Data.Nat as ℕ hiding (_⊔_)
open import Data.Nat.Properties as NP
open import Data.Product
open import Data.Vec
open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

drop′ : ∀ {a A n m i} → m ℕ.≤ n → i ℕ.≤ m → Vec {a} A (m ℕ.+ (n ∸ m)) → Vec A (n ∸ i)
drop′ z≤n z≤n xs = xs
drop′ (s≤s m≤n) z≤n (x ∷ xs) = x ∷ drop′ m≤n z≤n xs
drop′ (s≤s m≤n) (s≤s i≤m) (x ∷ xs) = drop′ m≤n i≤m xs

take′ : ∀ {a A m i} → i ℕ.≤ m → Vec {a} A m → Vec A i
take′ z≤n xs = []
take′ (s≤s i≤m) (x ∷ xs) = x ∷ (take′ i≤m xs)

reduce≥′ : ∀ {n m i} → m ℕ.≤ n → toℕ {n} i ≥ m → Fin (n ∸ m)
reduce≥′ {i = i} z≤n i≥m = i
reduce≥′ {i = suc i} (s≤s m≤n) (s≤s i≥m) = reduce≥′ m≤n i≥m

reduce≥′-mono : ∀ {n m i j} → (m≤n : m ℕ.≤ n) → (i≥m : toℕ i ≥ m) → (i≤j : i F.≤ j) → reduce≥′ m≤n i≥m F.≤ reduce≥′ m≤n (≤-trans i≥m i≤j)
reduce≥′-mono z≤n i≥m i≤j = i≤j
reduce≥′-mono {i = suc i} {suc j} (s≤s m≤n) (s≤s i≥m) (s≤s i≤j) = reduce≥′-mono m≤n i≥m i≤j

insert′ : ∀ {a A n m} → Vec {a} A (n ∸ suc m) → suc m ℕ.≤ n → Fin (n ∸ m) → A → Vec A (n ∸ m)
insert′ xs (s≤s z≤n) i x = insert xs i x
insert′ xs (s≤s (s≤s m≤n)) i x = insert′ xs (s≤s m≤n) i x

rotate : ∀ {a A n} {i j : Fin n} → Vec {a} A n → i F.≤ j → Vec A n
rotate {i = F.zero} {j} (x ∷ xs) z≤n = insert xs j x
rotate {i = suc i} {suc j} (x ∷ xs) (s≤s i≤j) = x ∷ (rotate xs i≤j)

remove′ : ∀ {a A n} → Vec {a} A n → Fin n → Vec A (ℕ.pred n)
remove′ (x ∷ xs) F.zero = xs
remove′ (x ∷ y ∷ xs) (suc i) = x ∷ remove′ (y ∷ xs) i

record Context n : Set (c ⊔ lsuc ℓ) where
  field
    m : ℕ
    m≤n : m ℕ.≤ n
    Γ : Vec (Type ℓ ℓ) (n ∸ m)
    Δ : Vec (Type ℓ ℓ) m

∙,∙ : Context 0
∙,∙ = record { m≤n = z≤n ; Γ = [] ; Δ = [] }

toVec : ∀ {n} → Context n → Vec (Type ℓ ℓ) n
toVec record { m = .0 ; m≤n = _ ; Γ = Γ ; Δ = [] } = Γ
toVec {suc n} record { m = .(suc _) ; m≤n = (s≤s m≤n) ; Γ = Γ ; Δ = (x ∷ Δ) } = x ∷ toVec (record { m≤n = m≤n ; Γ = Γ ; Δ = Δ })

wkn₁ : ∀ {n i} → (Γ,Δ : Context n) → toℕ {suc n} i ≥ Context.m Γ,Δ → Type ℓ ℓ → Context (suc n)
wkn₁ Γ,Δ i≥m τ = record
  { m≤n = ≤-step m≤n
  ; Γ = insert′ Γ (s≤s m≤n) (reduce≥′ (≤-step m≤n) i≥m) τ
  ; Δ = Δ
  }
  where
  open Context Γ,Δ

wkn₂ : ∀ {n i} → (Γ,Δ : Context n) → toℕ {suc n} i ℕ.≤ Context.m Γ,Δ → Type ℓ ℓ → Context (suc n)
wkn₂ Γ,Δ i≤m τ = record
  { m≤n = s≤s m≤n
  ; Γ = Γ
  ; Δ = insert Δ (fromℕ< (s≤s i≤m)) τ
  }
  where
  open Context Γ,Δ

shift≤ : ∀ {n i} (Γ,Δ : Context n) → i ℕ.≤ Context.m Γ,Δ → Context n
shift≤ {n} {i} record { m = m ; m≤n = m≤n ; Γ = Γ ; Δ = Δ } i≤m = record
  { m≤n = ≤-trans i≤m m≤n
  ; Γ = drop′ m≤n i≤m (Δ ++ Γ)
  ; Δ = take′ i≤m Δ
  }

cons : ∀ {n} → Context n → Type ℓ ℓ → Context (suc n)
cons Γ,Δ τ = wkn₂ Γ,Δ z≤n τ

shift : ∀ {n} → Context n → Context n
shift Γ,Δ = shift≤ Γ,Δ z≤n

_≋_ : ∀ {n} → Rel (Context n) (c ⊔ lsuc ℓ)
Γ,Δ ≋ Γ,Δ′ = Σ (Context.m Γ,Δ ≡ Context.m Γ,Δ′) λ {refl → Context.Γ Γ,Δ ≡ Context.Γ Γ,Δ′ × Context.Δ Γ,Δ ≡ Context.Δ Γ,Δ′}
