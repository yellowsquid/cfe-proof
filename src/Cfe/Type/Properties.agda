{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Cfe.Type.Properties
  {c ℓ} (over : Setoid c ℓ)
  where

open Setoid over using () renaming (Carrier to C; _≈_ to _∼_)

open import Algebra
open import Cfe.Language over renaming (_≤_ to _≤ˡ_; _≈_ to _≈ˡ_; ≤-min to ≤ˡ-min)
open import Cfe.Language.Construct.Concatenate over renaming (_∙_ to _∙ˡ_)
open import Cfe.Language.Construct.Single over
open import Cfe.Language.Construct.Union over
open import Cfe.Language.Indexed.Construct.Iterate over
open import Cfe.Type.Base over
open import Data.Bool renaming (_≤_ to _≤ᵇ_; _∨_ to _∨ᵇ_)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans)
open import Data.Empty
open import Data.List hiding (null)
open import Data.List.Relation.Binary.Equality.Setoid over
open import Data.Nat hiding (_≤ᵇ_; _^_) renaming (_≤_ to _≤ⁿ_)
open import Data.Nat.Properties using (≤-stepsˡ; ≤-stepsʳ) renaming (≤-refl to ≤ⁿ-refl)
open import Data.Product as Product
open import Data.Sum as Sum
open import Function hiding (_⟶_)
open import Relation.Unary.Properties
open import Relation.Binary.PropositionalEquality

≤-min : ∀ {fℓ lℓ} → Min (_≤_ {_} {_} {fℓ} {lℓ}) τ⊥
≤-min τ = record
  { n≤n = ≤-minimum τ.Null
  ; f⊆f = λ ()
  ; l⊆l = λ ()
  }
  where
  module τ = Type τ

L⊨τ+¬N⇒ε∉L : ∀ {a fℓ lℓ} {L : Language a} {τ : Type fℓ lℓ} → L ⊨ τ → T (not (Type.Null τ)) → [] ∉ L
L⊨τ+¬N⇒ε∉L {L = L} {τ} L⊨τ ¬n ε∈L = case ∃[ b ] ((null L → T b) × T (not b)) ∋ Null τ , _⊨_.n⇒n L⊨τ , ¬n of λ
  { (false , n⇒n , _) → n⇒n ε∈L }

⊨-anticongˡ : ∀ {a b fℓ lℓ} {A : Language a} {B : Language b} {τ : Type fℓ lℓ} → B ≤ˡ A → A ⊨ τ → B ⊨ τ
⊨-anticongˡ B≤A A⊨τ = record
  { n⇒n = A⊨τ.n⇒n ∘ B≤A.f
  ; f⇒f = A⊨τ.f⇒f ∘ Product.map₂ B≤A.f
  ; l⇒l = A⊨τ.l⇒l ∘ Product.map₂ (Product.map₂ (Product.map B≤A.f (Product.map₂ B≤A.f)))
  }
  where
  module B≤A = _≤ˡ_ B≤A
  module A⊨τ = _⊨_ A⊨τ

⊨-congʳ : ∀ {a fℓ₁ lℓ₁ fℓ₂ lℓ₂} {A : Language a} → (A ⊨_) ⟶ (A ⊨_) Respects (_≤_ {fℓ₁} {lℓ₁} {fℓ₂} {lℓ₂})
⊨-congʳ {A = A} τ₁≤τ₂ A⊨τ₁ = record
  { n⇒n = λ ε∈A → case ∃[ b ] (null A → T b) × ∃[ b′ ] b ≤ᵇ b′ ∋ τ₁.Null , A⊨τ₁.n⇒n , τ₂.Null , n≤n return (λ (_ , _ , x , _) → T x) of λ
    { (_ , _ , true , _) → _
    ; (false , n⇒n , false , _) → n⇒n ε∈A
    }
  ; f⇒f = f⊆f ∘ A⊨τ₁.f⇒f
  ; l⇒l = l⊆l ∘ A⊨τ₁.l⇒l
  }
  where
  open _≤_ τ₁≤τ₂
  module A⊨τ₁ = _⊨_ A⊨τ₁

L⊨τ⊥⇒L≈∅ : ∀ {a} {L : Language a} → L ⊨ τ⊥ → L ≈ˡ ∅
L⊨τ⊥⇒L≈∅ {L = L} L⊨τ⊥ = record
  { f = λ {l} → elim l
  ; f⁻¹ = λ ()
  }
  where
  module L⊨τ⊥ = _⊨_ L⊨τ⊥

  elim : ∀ l (l∈L : l ∈ L) → l ∈ ∅
  elim [] []∈L = L⊨τ⊥.n⇒n []∈L
  elim (x ∷ l) xl∈L = L⊨τ⊥.f⇒f (-, xl∈L)

∅⊨τ⊥ : ∅ ⊨ τ⊥
∅⊨τ⊥ = record
  { n⇒n = λ ()
  ; f⇒f = λ ()
  ; l⇒l = λ ()
  }

L⊨τε⇒L≤｛ε｝ : ∀ {a} {L : Language a} → L ⊨ τε → L ≤ˡ ｛ε｝
L⊨τε⇒L≤｛ε｝{L = L} L⊨τε = record
  { f = λ {l} → elim l
  }
  where
  module L⊨τε = _⊨_ L⊨τε

  elim : ∀ l → l ∈ L → l ∈ ｛ε｝
  elim [] []∈L = refl
  elim (x ∷ l) xl∈L = ⊥-elim (L⊨τε.f⇒f (-, xl∈L))

｛ε｝⊨τε : ｛ε｝ ⊨ τε
｛ε｝⊨τε = record
  { n⇒n = const tt
  ; f⇒f = λ ()
  ; l⇒l = λ { ([] , ()) ; (_ ∷ _ , ())}
  }
  where
  open import Data.Unit

｛c｝⊨τ[c] : ∀ c → ｛ c ｝ ⊨ τ[ c ]
｛c｝⊨τ[c] c = record
  { n⇒n = λ ()
  ; f⇒f = λ {x} → λ {([] , (c∼x ∷ []≋[])) → c∼x}
  ; l⇒l = λ {x} → λ
    { ([] , []≢[] , _) → ⊥-elim ([]≢[] refl)
    ; (y ∷ [] , _ , _ , l′ , y∷x∷l′∈｛c｝) → ⊥-elim (xy∉｛c｝ c y x l′ y∷x∷l′∈｛c｝)
    ; (y ∷ z ∷ l , _ , _ , l′ , y∷z∷l++x∷l′∈｛c｝) → ⊥-elim (xy∉｛c｝ c y z (l ++ x ∷ l′) y∷z∷l++x∷l′∈｛c｝)
    }
  }
  where

∙-⊨ : ∀ {a b fℓ₁ lℓ₁ fℓ₂ lℓ₂} {A : Language a} {B : Language b} {τ₁ : Type fℓ₁ lℓ₁} {τ₂ : Type fℓ₂ lℓ₂} →
      A ⊨ τ₁ → B ⊨ τ₂ → τ₁ ⊛ τ₂ → A ∙ˡ B ⊨ τ₁ ∙ τ₂
∙-⊨ {A = A} {B} {τ₁} {τ₂} A⊨τ₁ B⊨τ₂ τ₁⊛τ₂ = record
  { n⇒n = λ { ([] , l∈A , _) → ⊥-elim (L⊨τ+¬N⇒ε∉L A⊨τ₁ τ₁⊛τ₂.¬n₁ l∈A) }
  ; f⇒f = λ
    { (_ , [] , l∈A , l′ , l′∈B , _) → ⊥-elim (L⊨τ+¬N⇒ε∉L A⊨τ₁ τ₁⊛τ₂.¬n₁ l∈A)
    ; (_ , x ∷ l , l∈A , l′ , l′∈B , x≈x ∷ _) → inj₁ (A⊨τ₁.f⇒f (l , A.∈-resp-≋ (x≈x ∷ ≋-refl) l∈A))
    }
  ; l⇒l = {!!}
  }
  where
  module A = Language A
  module A⊨τ₁ = _⊨_ A⊨τ₁
  module B⊨τ₂ = _⊨_ B⊨τ₂
  module τ₁⊛τ₂ = _⊛_ τ₁⊛τ₂

∪-⊨ : ∀ {a b fℓ₁ lℓ₁ fℓ₂ lℓ₂} {A : Language a} {B : Language b} {τ₁ : Type fℓ₁ lℓ₁} {τ₂ : Type fℓ₂ lℓ₂} →
      A ⊨ τ₁ → B ⊨ τ₂ → τ₁ # τ₂ → A ∪ B ⊨ τ₁ ∨ τ₂
∪-⊨ {A = A} {B} {τ₁} {τ₂} A⊨τ₁ B⊨τ₂ τ₁#τ₂ = record
  { n⇒n = λ
    { (inj₁ ε∈A) → case ∃[ b ] T b ∋ Null τ₁ , A⊨τ₁.n⇒n ε∈A return (λ {(x , _) → T (x ∨ᵇ Null τ₂)}) of λ
      { (true , _) → _ }
    ; (inj₂ ε∈B) → case ∃[ b ] T b ∋ Null τ₂ , B⊨τ₂.n⇒n ε∈B return (λ {(x , _) → T (Null τ₁ ∨ᵇ x)}) of λ
      { (true , _) → subst T (sym (∨-zeroʳ (Null τ₁))) _ }
    }
  ; f⇒f = λ
    { (l , inj₁ x∷l∈A) → inj₁ (A⊨τ₁.f⇒f (-, x∷l∈A))
    ; (l , inj₂ x∷l∈B) → inj₂ (B⊨τ₂.f⇒f (-, x∷l∈B))
    }
  ; l⇒l = λ
    { ([] , l≢ε , l∈A∪B , l′ , l++x∷l′∈A∪B) → ⊥-elim (l≢ε refl)
    ; (_ ∷ _ , _ , inj₁ l∈A , _ , inj₁ l++x∷l′∈A) → inj₁ (A⊨τ₁.l⇒l (-, (λ ()) , l∈A , -, l++x∷l′∈A))
    ; (c ∷ _ , _ , inj₁ c∷u∈A , l′ , inj₂ c∷v∈B) → ⊥-elim (τ₁#τ₂.∄[f₁∩f₂] c (A⊨τ₁.f⇒f (-, c∷u∈A) , B⊨τ₂.f⇒f (-, c∷v∈B)))
    ; (c ∷ _ , _ , inj₂ c∷u∈B , l′ , inj₁ c∷v∈A) → ⊥-elim (τ₁#τ₂.∄[f₁∩f₂] c (A⊨τ₁.f⇒f (-, c∷v∈A) , B⊨τ₂.f⇒f (-, c∷u∈B)))
    ; (_ ∷ _ , _ , inj₂ l∈B , _ , inj₂ l++x∷l′∈B) → inj₂ (B⊨τ₂.l⇒l (-, (λ ()) , l∈B , -, l++x∷l′∈B))
    }
  }
  where
  module τ₁#τ₂ = _#_ τ₁#τ₂
  module A⊨τ₁ = _⊨_ A⊨τ₁
  module B⊨τ₂ = _⊨_ B⊨τ₂

⋃-⊨ : ∀ {a fℓ lℓ} {F : Op₁ (Language a)} {τ : Type fℓ lℓ} →
      (Congruent₁ _≤ˡ_ F) →
      (∀ {L} → L ⊨ τ → F L ⊨ τ) → ⋃ F ⊨ τ
⋃-⊨ {a} {F = F} {τ} ≤-mono ⊨-mono = record
  { n⇒n = λ { (n , l∈Fⁿ) → _⊨_.n⇒n (Fⁿ⊨τ n) l∈Fⁿ}
  ; f⇒f = λ { (_ , n , x∷l∈Fⁿ) → _⊨_.f⇒f (Fⁿ⊨τ n) (-, x∷l∈Fⁿ) }
  ; l⇒l = λ
    { (_ , l≢ε , (m , l∈Fᵐ) , _ , (n , l++x∷l′∈Fⁿ)) →
         _⊨_.l⇒l (Fⁿ⊨τ (m + n))
           (-, l≢ε , _≤ˡ_.f (^-mono (≤-stepsʳ {m} n ≤ⁿ-refl)) l∈Fᵐ ,
            -, _≤ˡ_.f (^-mono (≤-stepsˡ m ≤ⁿ-refl)) l++x∷l′∈Fⁿ)
    }
  }
  where
  Fⁿ⊨τ : ∀ n → (F ^ n) (Lift a ∅) ⊨ τ
  Fⁿ⊨τ zero = ⊨-anticongˡ (≤-reflexive (lift-cong a ∅)) (⊨-congʳ (≤-min τ) ∅⊨τ⊥)
  Fⁿ⊨τ (suc n) = ⊨-mono (Fⁿ⊨τ n)

  ^-mono : ∀ {m n} → m ≤ⁿ n → (F ^ m) (Lift a ∅) ≤ˡ (F ^ n) (Lift a ∅)
  ^-mono {n = n} z≤n = ≤-trans (≤-reflexive (lift-cong a ∅)) (≤ˡ-min ((F ^ n) (Lift a ∅)))
  ^-mono (s≤s m≤n) = ≤-mono (^-mono m≤n)
