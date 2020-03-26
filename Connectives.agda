module plfa.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.Isomorphism using (_⇔_; _≃_; _≤_; extensionality)
open plfa.Isomorphism.≃-Reasoning


data _×_ (A B : Set) : Set where

    ⟪_,_⟫ :
        A
      → B
        -----
      → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟪ a , b ⟫ = a

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟪ a , b ⟫ = b

η-× : ∀ {A B : Set} → (w : A × B) → ⟪ proj₁ w , proj₂ w ⟫ ≡ w
η-× ⟪ x , y ⟫ = refl

infixr 2 _×_

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    {   to = λ{ ⟪ x , y ⟫ → ⟪ y , x ⟫ }
      ; from = λ{ ⟪ x , y ⟫ → ⟪ y , x ⟫ }
      ; from∘to = λ{ ⟪ x , y ⟫ → refl }
      ; to∘from = λ{ ⟪ x , y ⟫ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    {   to = λ{ ⟪ ⟪ x , y ⟫ , z ⟫ → ⟪ x , ⟪ y , z ⟫ ⟫ }
      ; from = λ{ ⟪ x , ⟪ y , z ⟫ ⟫ → ⟪ ⟪ x , y ⟫ , z ⟫ }
      ; from∘to = λ{ ⟪ ⟪ x , y ⟫ , z ⟫ → refl }
      ; to∘from = λ{ ⟪ x , ⟪ y , z ⟫ ⟫ → refl }
    }

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    {   to = λ x → ⟪ _⇔_.to x , _⇔_.from x ⟫
      ; from = λ x → record
            {   to = proj₁ x
              ; from = proj₂ x
            }
      ; from∘to = λ{ a → refl }
      ; to∘from = λ{ ⟪ x , y ⟫ → refl }
    }

data ⊤ : Set where

  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
    record
      {   to = proj₂
        ; from = λ x → ⟪ tt , x ⟫
        ; from∘to = λ{ ⟪ tt , x ⟫ → refl }
        ; to∘from = λ b → refl
      }

⊤-identityʳ : ∀ {A : Set} → A × ⊤ ≃ A
⊤-identityʳ {A} =
    ≃-begin
      (A × ⊤)
    ≃⟨ ×-comm ⟩
      (⊤ × A)
    ≃⟨ ⊤-identityˡ ⟩
      A
    ≃-∎

data _⊎_ (A B : Set) : Set where

    inj₁ :
        A
        -----
      → A ⊎ B

    inj₂ :
        B
        -----
      → A ⊎ B

case-⊎ : {A B C : Set}
    → (A → C)
    → (B → C)
    → A ⊎ B
      -------
    → C
case-⊎ ac bc (inj₁ a) = ac a
case-⊎ ac bc (inj₂ b) = bc b

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ a) = refl
η-⊎ (inj₂ b) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
    case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ a) = refl
uniq-⊎ h (inj₂ b) = refl

infixr 1 _⊎_

η-swap : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₂ inj₁ (case-⊎ inj₂ inj₁ w) ≡ w
η-swap (inj₁ x) = refl
η-swap (inj₂ x) = refl

comm-⊎ : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
comm-⊎ =
  record
    {   to = λ x → case-⊎ inj₂ inj₁ x
      ; from = λ x → case-⊎ inj₂ inj₁ x
      ; from∘to = η-swap
      ; to∘from = η-swap
    }

assoc-⊎-left : ∀ {A B C : Set} (w : A ⊎ (B ⊎ C)) → (A ⊎ B) ⊎ C
assoc-⊎-left (inj₁ x) = inj₁ (inj₁ x)
assoc-⊎-left (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
assoc-⊎-left (inj₂ (inj₂ x)) = inj₂ x

assoc-⊎-right : ∀ {A B C : Set} (w : (A ⊎ B) ⊎ C) → A ⊎ (B ⊎ C)
assoc-⊎-right (inj₁ (inj₁ x)) = inj₁ x
assoc-⊎-right (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
assoc-⊎-right (inj₂ x) = inj₂ (inj₂ x)

η-assoc-left : ∀ {A B C : Set} (w : (A ⊎ B) ⊎ C) → assoc-⊎-left (assoc-⊎-right w) ≡ w
η-assoc-left (inj₁ (inj₁ x)) = refl
η-assoc-left (inj₁ (inj₂ x)) = refl
η-assoc-left (inj₂ x) = refl

η-assoc-right : ∀ {A B C : Set} (w : A ⊎ (B ⊎ C)) → assoc-⊎-right (assoc-⊎-left w) ≡ w
η-assoc-right (inj₁ x) = refl
η-assoc-right (inj₂ (inj₁ x)) = refl
η-assoc-right (inj₂ (inj₂ x)) = refl

assoc-⊎ : ∀ {A B C : Set} → A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C
assoc-⊎ =
  record
    {   to = assoc-⊎-left
      ; from = assoc-⊎-right
      ; from∘to = η-assoc-right
      ; to∘from = η-assoc-left
    }

data ⊥ : Set where
    -- nothing to see here

⊥-elim : ∀ {A : Set}
    → ⊥
      --
    → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

η-⊥-⊎ : ∀ {A : Set} (a : ⊥ ⊎ A) → inj₂ (case-⊎ ⊥-elim (λ x → x) a) ≡ a
η-⊥-⊎ (inj₂ x) = refl

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    {   to = λ x → case-⊎ ⊥-elim (λ x → x) x
      ; from = inj₂
      ; from∘to = η-⊥-⊎
      ; to∘from = λ b → refl
    }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} =
    ≃-begin
      (A ⊎ ⊥)
    ≃⟨ comm-⊎ ⟩
      (⊥ ⊎ A)
    ≃⟨ ⊥-identityˡ ⟩
      A
    ≃-∎

→-elim : ∀ {A B : Set}
    → (A → B)
    → A
      -------
    → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ x → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    {   to = λ f → λ x → (f (proj₁ x)) (proj₂ x)
      ; from = λ f → λ x → λ y → f ⟪ x , y ⟫
      ; from∘to = λ a → refl
      ; to∘from = λ b → extensionality λ{ ⟪ x , y ⟫ → refl }
    }


→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ (A → C) × (B → C)
→-distrib-⊎ =
  record
    {   to = λ x → ⟪ x ∘ inj₁ , x ∘ inj₂ ⟫
      ; from = λ x x₁ → case-⊎ (proj₁ x) (proj₂ x) x₁
      ; from∘to = λ a → extensionality λ{ (inj₁ x) → refl; (inj₂ x) → refl }
      ; to∘from = λ{ ⟪ b₁ , b₂ ⟫ → refl }
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
    record {
        to = λ x → ⟪ proj₁ ∘ x , proj₂ ∘ x ⟫
      ; from = λ x → λ y → ⟪ (proj₁ x) y , (proj₂ x) y ⟫
      ; from∘to = λ a → extensionality λ{ x → η-× (a x) }
      ; to∘from = λ{ ⟪ a , b ⟫ → refl }
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
    record {
        to = λ{ ⟪ inj₁ a , c ⟫ → inj₁ ⟪ a , c ⟫; ⟪ inj₂ b , c ⟫ → inj₂ ⟪ b , c ⟫ }
      ; from = λ{ (inj₁ ⟪ a , c ⟫) → ⟪ inj₁ a , c ⟫; (inj₂ ⟪ b , c ⟫) → ⟪ inj₂ b , c ⟫ }
      ; from∘to = λ{ ⟪ inj₁ a , c ⟫ → refl; ⟪ inj₂ b , c ⟫ → refl  }
      ; to∘from = λ{ (inj₁ ⟪ a , c ⟫) → refl; (inj₂ ⟪ b , c ⟫) → refl }
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≤ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
    record {
        to = λ{ (inj₁ ⟪ a , b ⟫) → ⟪ inj₁ a , inj₁ b ⟫; (inj₂ c) → ⟪ inj₂ c , inj₂ c ⟫ }
      ; from = λ{ ⟪ inj₁ a , inj₁ b ⟫ → inj₁ ⟪ a , b ⟫
                ; ⟪ _ , inj₂ c ⟫ → inj₂ c
                ; ⟪ inj₂ c , _ ⟫ → inj₂ c }
      ; from∘to = λ{ (inj₁ ⟪ a , b ⟫) → refl
                   ; (inj₂ c) → refl }
    }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟪ inj₁ x , x₁ ⟫ = inj₁ x
⊎-weak-× ⟪ inj₂ x , x₁ ⟫ = inj₂ ⟪ x , x₁ ⟫

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟪ a , b ⟫) = ⟪ inj₁ a , inj₁ b ⟫
⊎×-implies-×⊎ (inj₂ ⟪ c , d ⟫) = ⟪ inj₂ c , inj₂ d ⟫
