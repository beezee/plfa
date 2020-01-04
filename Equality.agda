module plfa.Equality where

data _≡_ {A : Set} (x : A): A -> Set where
  refl : x ≡ x

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
