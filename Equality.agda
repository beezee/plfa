module plfa.Equality where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡_ {A : Set} (x : A): A -> Set where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≡_

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    -----------
  → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {a b : A} {c d : B}
  → a ≡ b
  → c ≡ d
    -----------------
  → (f a c) ≡ (f b c)
cong₂ f refl _ = refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    -----
  → (x : A) → f x ≡ g x
cong-app refl _ = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where

  infix 1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix 3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin refl = refl

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ refl = refl

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ xy ⟩ yz = trans xy yz

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  _∎ x = refl

open ≡-Reasoning

trans' : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans' {A} {x} {y} {z} xy yz =
  begin
    x
  ≡⟨ xy ⟩
    y
  ≡⟨ yz ⟩
    z
  ∎

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

postulate
  +-identity : ∀ (n : ℕ) → n + zero ≡ n
  +-suc : ∀ (m n : ℕ) → m + (suc n) ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm x zero = begin
    x + zero
  ≡⟨ +-identity x ⟩
    x
  ≡⟨⟩
    zero + x
  ∎
+-comm x (suc y) = begin
    x + suc y
  ≡⟨ +-suc x y ⟩
    suc (x + y)
  ≡⟨ cong (suc) (+-comm x y) ⟩
    suc (y + x)
  ∎

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' zero n rewrite +-identity n = refl
+-comm' (suc m) n rewrite +-suc n m | +-comm' m n = refl

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
     ----------
   → zero ≤ n

  s≤s : ∀ {m n : ℕ}
   → m ≤ n
     -------------
   → suc m ≤ suc n


infix 4 _≤_

module ≤-Reasoning where

  infix 1 ≤-begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix 3 _≤-∎

  ≤-trans : ∀ {m n p : ℕ}
    → m ≤ n
    → n ≤ p
      -----
    → m ≤ p
  ≤-trans z≤n np = z≤n
  ≤-trans (s≤s mn) (s≤s np) = s≤s (≤-trans mn np)

  ≤-refl : ∀ {m : ℕ}
      -----
    → m ≤ m
  ≤-refl {zero} = z≤n
  ≤-refl {suc m} = s≤s ≤-refl

  ≤-refl₂ : ∀ {m n : ℕ}
    → m ≡ n
      -----
    → m ≤ n
  ≤-refl₂ refl = ≤-refl

  ≤-suc : ∀ {m : ℕ}
      -------
    → m ≤ suc m
  ≤-suc {zero} = z≤n
  ≤-suc {suc m} = s≤s ≤-suc

  ≤-+ : ∀ {m n : ℕ}
      ---------
    → m ≤ n + m
  ≤-+ {m} {zero} = ≤-refl
  ≤-+ {m} {suc n} = ≤-trans ≤-+ ≤-suc

  ≤-begin_ : ∀ {x y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  ≤-begin xy = xy

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  x ≤⟨⟩ xy = xy

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤⟨ xy ⟩ yz = ≤-trans xy yz

  _≤-∎ : ∀ (x : ℕ)
      -----
    → x ≤ x
  _≤-∎ x = ≤-refl

  +-monoʳ-≤ : {m n p : ℕ}
    → m ≤ n
      -----------------
    → (p + m) ≤ (p + n)
  +-monoʳ-≤ {zero} {n} {p} mn = ≤-begin
      p + zero
    ≤⟨ ≤-refl₂ (+-identity p) ⟩
      p
    ≤⟨ ≤-+ ⟩
      n + p
    ≤⟨ ≤-refl₂ (+-comm n p) ⟩
      p + n
    ≤-∎
  +-monoʳ-≤ {suc m} {suc n} {p} (s≤s mn) = ≤-begin
      p + suc m
    ≤⟨ ≤-refl₂ (+-suc p m) ⟩
      suc (p + m)
    ≤⟨ s≤s (+-monoʳ-≤ mn) ⟩
      suc (p + n)
    ≤⟨ ≤-refl₂ (sym (+-suc p n)) ⟩
      p + suc n
    ≤-∎

  +-monoˡ-≤ : {m n p : ℕ}
    → m ≤ n
      -----------------
    → (m + p) ≤ (n + p)
  +-monoˡ-≤ {zero} {n} {p} mn =
    ≤-begin
      p
    ≤⟨ ≤-+ ⟩
      n + p
    ≤-∎
  +-monoˡ-≤ {suc m} {suc n} {p} (s≤s mn) = ≤-begin
      suc (m + p)
    ≤⟨ s≤s (+-monoˡ-≤ mn) ⟩
      suc (n + p)
    ≤-∎

  +-mono-≤ : {m n p q : ℕ}
    → m ≤ n
    → p ≤ q
      -------------
    → m + p ≤ n + q
  +-mono-≤ {m} {n} {p} {q} mn pq = ≤-begin
      m + p
    ≤⟨ +-monoʳ-≤ pq ⟩
      m + q
    ≤⟨ +-monoˡ-≤ mn ⟩
      n + q
    ≤-∎

open ≤-Reasoning

data even : ℕ → Set
data odd : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

even-comm : ∀ {m n : ℕ}
  → even (m + n)
    ------------
  → even (n + m)
even-comm {m} {n} emn rewrite +-comm n m = emn

even-comm' : ∀ {m n : ℕ}
  → even (m + n)
    ------------
  → even (n + m)
even-comm' {m} {n} emn with m + n | +-comm m n
...                     | .(n + m) | refl = emn

even-comm″ : ∀ {m n : ℕ}
  → even (m + n)
    ------------
  → even (n + m)
even-comm″ {m} {n} = subst even (+-comm m n)

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ {x} P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ {A} xy yz P Px = yz P (xy P Px)

sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {A} {x} {y} xy P = Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = xy Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
≡-implies-≐ xy P = subst P xy

≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} xy = Py
    where
      P : A → Set
      P a = x ≡ a
      Px : x ≡ x
      Px = refl
      Py : x ≡ y
      Py = xy P Px

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
    refl′ : x ≡′ x

sym-≡′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≡′ y
    -----
  → y ≡′ x
sym-≡′ refl′ = refl′

_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → (A → C)
_∘_ bc ab a = bc (ab a)  
