module plfa.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using(ℕ; zero; suc; _+_; _*_; _≤_)
open _≤_
open import Data.Nat.Properties using (
    +-assoc; +-comm; +-suc; +-identityʳ; *-distribˡ-+;
    ≤-refl; ≤-trans; ≤-step; +-identityˡ)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; extensionality)

∀-elim : ∀ {A : Set} {B : A → Set}
    → (L : ∀ (x : A) → B x)
    → (M : A)
      ---------------------
    → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× {A} {B} {C} =
  record {
      to = λ x → proj₁ ∘ x , proj₂ ∘ x
    ; from = λ x x₁ → (proj₁ x) x₁ , (proj₂ x) x₁
    ; from∘to = λ a → refl
    ; to∘from = λ b → refl
  }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → (∀ (x : A) → B x ⊎ C x)
⊎∀-implies-∀⊎ {A} {B} {C} (inj₁ x) = inj₁ ∘ x
⊎∀-implies-∀⊎ {A} {B} {C} (inj₂ y) = inj₂ ∘ y

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  π-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → (∀ (a : A) → f a ≡ g a)
      ----------------------
    → f ≡ g

∀-× : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× {B} =
  record {
      to = λ x → (x aa) , (x bb) , (x cc)
    ; from = λ{ x aa → proj₁ x; x bb → (proj₁ ∘ proj₂) x; x cc → (proj₂ ∘ proj₂) x }
    ; from∘to = λ a → π-extensionality λ{ aa → refl; bb → refl; cc → refl}
    ; to∘from = λ{ (b₁ , b₂ , b₃) → refl }
  }

data Σ (A : Set) (B : A → Set) : Set where
    ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-proj₁ : ∀{ A : Set} {B : A → Set} (eab : ∃ {A} B) → A
∃-proj₁ ⟨ a , ba ⟩ = a


∃-syntax = ∃
infix 2 ∃-syntax
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
    → (∀ x → B x → C)
    → ∃[ x ] B x
      ---------------
    → C
∃-elim xbc ⟨ x , x₁ ⟩ = xbc x x₁

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying {A} {B} =
  record {
      to = λ{ x ⟨ a , b ⟩ → x a b }
    ; from = λ x x₁ x₂ → x ⟨ x₁ , x₂ ⟩
    ; from∘to = λ a → refl
    ; to∘from = λ b → π-extensionality λ{ ⟨ x₁ , x₂ ⟩ → refl }
  }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)

∃-distrib-⊎ =
  record {
      to = λ{ ⟨ x , (inj₁ bx) ⟩ → inj₁ ⟨ x , bx ⟩; ⟨ x , (inj₂ cx) ⟩ → inj₂ ⟨ x , cx ⟩ }
    ; from = λ{ (inj₁ ⟨ x , bx ⟩)  → ⟨ x , inj₁ bx ⟩; (inj₂ ⟨ x , cx ⟩) → ⟨ x , inj₂ cx ⟩ }
    ; from∘to = λ{ ⟨ x , (inj₁ bx) ⟩ → refl; ⟨ x , (inj₂ cx) ⟩ → refl }
    ; to∘from = λ{ (inj₁ ⟨ x , bx ⟩) → refl; (inj₂ ⟨ x , cx ⟩) → refl }
  }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , (bx , cx) ⟩ = ⟨ x , bx ⟩ , ⟨ x , cx ⟩

∃-⊎ : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ {B} =
  record {
      to = λ{ ⟨ aa , bx ⟩ → inj₁ bx; ⟨ bb , bx ⟩ → inj₂ (inj₁ bx); ⟨ cc , bx ⟩ → inj₂ (inj₂ bx) }
    ; from = λ{ (inj₁ baa) → ⟨ aa , baa ⟩; (inj₂ (inj₁ bbb)) → ⟨ bb , bbb ⟩; (inj₂ (inj₂ bcc)) → ⟨ cc , bcc ⟩ }
    ; from∘to = λ{ ⟨ aa , bx ⟩ → refl; ⟨ bb , bx ⟩ → refl; ⟨ cc , bc ⟩ → refl }
    ; to∘from = λ{ (inj₁ baa) → refl; (inj₂ (inj₁ bbb)) → refl; (inj₂ (inj₂ bcc)) → refl }
  }

data even : ℕ → Set
data odd : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc : ∀ {n : ℕ}
    → odd n
      -----------
    → even (suc n)

data odd where

  suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] ( m * 2 ≡ n )
odd-∃ : ∀ {n : ℕ} → odd n → ∃[ m ] ( 1 + m * 2 ≡ n )

even-∃ zero = ⟨ zero , refl ⟩
even-∃ (suc x) with odd-∃ x
...                   | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (suc x) with even-∃ x
...                   | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] ( m * 2 ≡ n ) → even n
∃-odd : ∀ {n : ℕ} → ∃[ m ] ( 1 + m * 2 ≡ n ) → odd n

∃-even ⟨ zero , refl ⟩ = zero
∃-even ⟨ suc x , refl ⟩ = suc (∃-odd ⟨ x , refl ⟩)

∃-odd ⟨ m , refl ⟩ = suc (∃-even ⟨ m , refl ⟩ )

∃-even′ : ∀ {n : ℕ} → ∃[ m ] (2 * m ≡ n) → even n
∃-odd′ : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) → odd n

+1≡suc : ∀ {x : ℕ} → x + 1 ≡ suc x
+1≡suc {zero} = refl
+1≡suc {suc x} = cong (suc) (+1≡suc {x})

∃-even′ ⟨ zero , refl ⟩ = zero
∃-even′ ⟨ suc x , refl ⟩ with (∃-odd′ ⟨ x , refl ⟩)
...                   | y rewrite (sym (+1≡suc {x + 0}))
                      | +-assoc x (x + 0) 1 = suc y

∃-odd′ ⟨ m , refl ⟩ rewrite +1≡suc {m + (m + 0)} = suc (∃-even′ ⟨ m , refl ⟩)

∃-+-≤ : ∀ {y z : ℕ} → ∃[ x ] ( y + x ≡ z ) → y ≤ z
∃-+-≤ {y} {.(y + 0)} ⟨ zero , refl ⟩ rewrite +-identityʳ y = ≤-refl
∃-+-≤ {zero} {.(suc x)} ⟨ suc x , refl ⟩ = z≤n
∃-+-≤ {suc y} {.(suc (y + suc x))} ⟨ suc x , refl ⟩ = s≤s (∃-+-≤ {y} {y + suc x} ⟨ suc x , refl ⟩)

≤-+-∃ : ∀ {y z : ℕ} → y ≤ z → ∃[ x ] ( y + x ≡ z )
≤-+-∃ {.0} {z} z≤n = ⟨ z , +-identityˡ z ⟩
≤-+-∃ {.(suc _)} {.(suc _)} (s≤s yz) with ≤-+-∃ yz
...                                   | ⟨ x , refl ⟩ = ⟨ x , refl ⟩

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → ¬ (∃[ x ] ( B x )) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
    record {
        to = λ ¬∃bx x bx → ¬∃bx ⟨ x , bx ⟩
      ; from = λ{ ∀x¬bx ⟨ x , bx ⟩ → (∀x¬bx x) bx }
      ; from∘to = λ{ ¬∃xy → π-extensionality λ{ ⟨ x , bx ⟩ → refl } }
      ; to∘from = λ ∀¬xy → refl
    }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
    → ∃[ x ] ( ¬ B x )
      ----------------
    → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , ¬bx ⟩ xbx = ¬bx (xbx x)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero = ⟨⟩
to (suc b) = inc (to b)

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = 2 * (from b)
from (b I) = 1 + 2 * (from b)

data One : Bin → Set where

  one :
      ----------
      One (⟨⟩ I)

  oneAfter : ∀ {b : Bin}
    → One b
      -------
    → One (b I)

  zeroAfter : ∀ {b : Bin}
    → One b
      -------
    → One (b O)

data Can : Bin → Set where

  zero :
      --------
      Can ⟨⟩

  one : ∀ {b : Bin}
    → One b
      -------
    → Can b

postulate
    from-to-n : ∀ {n : ℕ} → from (to n) ≡ n

postulate
  can-to-from : ∀ {b : Bin}
    → Can b
      ---------
    → to (from b) ≡ b

postulate
  can-inc : ∀ {b : Bin} → Can b → Can (inc b)

≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
≡One {.(⟨⟩ I)} one one = refl
≡One {.(_ I)} (oneAfter o) (oneAfter o′) with ≡One o o′
...                                       | refl = refl
≡One {.(_ O)} (zeroAfter o) (zeroAfter o′) with ≡One o o′
...                                       | refl = refl

≡Can : ∀ {b : Bin} → (cb cb′ : Can b) → cb ≡ cb′
≡Can zero zero = refl
≡Can (one x) (one x₁) with ≡One x x₁
...                     | refl = refl

∃-proj₁≡→Can≡ : {cb cb′ : ∃[ b ](Can b)} → ∃-proj₁ cb ≡ ∃-proj₁ cb′ → cb ≡ cb′
∃-proj₁≡→Can≡ {⟨ b , cb ⟩ } {⟨ b′ , cb′ ⟩} refl with ≡Can cb cb′
...                                               | refl = refl

ℕ→Can : ∀ (n : ℕ) → ∃[ b ]( Can b )
ℕ→Can zero = ⟨ to zero , zero ⟩
ℕ→Can (suc n) with ℕ→Can n
...                 | ⟨ (to n) , cb ⟩ = ⟨ inc b , can-inc cb ⟩

Can→ℕ : ∀ {b : Bin} (cb : Can b) → ℕ
Can→ℕ {b} cb = from b

∃-proj₁∘ℕ→Can≡to : ∀{n : ℕ} → (∃-proj₁ ∘ ℕ→Can) n ≡ to n
∃-proj₁∘ℕ→Can≡to {zero} = refl
∃-proj₁∘ℕ→Can≡to {suc n} with ∃-proj₁∘ℕ→Can≡to {n}
...                       | x = {!   !}

from∘∃-proj₁∘ℕ→Can≡id : ∀{n : ℕ} → (from ∘ ∃-proj₁ ∘ ℕ→Can) n ≡ n
from∘∃-proj₁∘ℕ→Can≡id {n} = {!   !}

ℕ≃∃Can : ℕ ≃ ∃[ b ]( Can b )
ℕ≃∃Can =
    record {
        to = ℕ→Can
      ; from = λ{ ⟨ b , cb ⟩ → Can→ℕ cb }
      ; from∘to = λ a → {!   !}
      ; to∘from = {!   !}
    }
