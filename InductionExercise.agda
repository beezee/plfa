import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

_ : 3 + (4 + 5) ≡ (3 + 4) + 5
_ =
  begin
    3 + (4 + 5)
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    12
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    (3 + 4) + 5
  ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩ -- left identity elimination
    n + p
  ≡⟨⟩ -- left identity introduction
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    ((suc m) + n) + p
  ≡⟨⟩
    (suc (m + n)) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    (suc (1 + n)) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩
    suc 1 + (n + p)
  ≡⟨⟩
    2 + (n + p)
  ∎
  where
  +-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
  +-assoc-1 n p =
    begin
      (1 + n) + p
    ≡⟨⟩ -- inductive case +
      (suc (zero + n)) + p
    ≡⟨⟩ -- inductive case +
      suc ((zero + n) + p)
    ≡⟨ cong suc (+-assoc-0 n p) ⟩
      suc (zero + (n + p))
    ≡⟨⟩ -- inductive case +
      suc zero + (n + p)
    ≡⟨⟩
      1 + (n + p)
    ∎
    where
    +-assoc-0 : ∀ (n p : ℕ) → (zero + n) + p  ≡ zero + (n + p)
    +-assoc-0 n p =
      begin
        (zero + n) + p
      ≡⟨⟩ -- base case +
        n + p
      ≡⟨⟩ -- base case +
        zero + (n + p)
      ∎

identityʳ : ∀ (m : ℕ) → m + zero ≡ m
identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩ -- base case +
    zero
  ∎
identityʳ (suc m) =
  begin
    (suc m) + zero
  ≡⟨⟩ -- inductive case +
    suc (m + zero)
  ≡⟨ cong suc (identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩ -- base case +
    suc n
  ≡⟨⟩ -- base case +
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    (suc m) + (suc n)
  ≡⟨⟩ -- inductive case +
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩ -- inductive case +
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ identityʳ m ⟩
    m
  ≡⟨⟩ -- base case +
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩ -- inductive case +
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩ -- inductive case addition
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q = begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    m + (n + p) + q
  ∎

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

+-identity' : ∀ (n : ℕ) → (n + zero) ≡ n
+-identity' zero = refl
+-identity' (suc n) rewrite +-identity' n = refl

+-suc' : ∀ (m n : ℕ) → (m + suc n) ≡ suc (m + n)
+-suc' zero n = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero rewrite +-identity' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | +-comm' m n | +-assoc n m p = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ (m * p) + (n * p)
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc' p (m * p) (n * p) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

*-zap : ∀ (m : ℕ) → (m * zero) ≡ zero
*-zap zero = refl
*-zap (suc m) rewrite *-zap m = refl

*-identity : ∀ (m : ℕ) → (m * 1) ≡ m
*-identity zero = refl
*-identity (suc m) rewrite *-identity m = refl

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + (m * n)
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n | +-swap m n (m * n) = refl

*-comm : ∀ (m n : ℕ) → (m * n) ≡ (n * m)
*-comm zero n rewrite *-zap n = refl
*-comm (suc m) n rewrite *-suc n m | *-comm m n = refl

monus-zero : ∀ (n : ℕ) → 0 ∸ n ≡ 0
monus-zero zero = refl
monus-zero (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p rewrite monus-zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

_^_ : ℕ → ℕ → ℕ
n ^ suc m = n * (n ^ m)
n ^ zero = 1

coproduct-nat : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
coproduct-nat m zero p rewrite +-identity' (m ^ p) = refl
coproduct-nat m (suc n) p rewrite cong (m *_) (coproduct-nat m n p) | sym (*-assoc m (m ^ n) (m ^ p)) = refl

product-nat : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
product-nat m n zero = refl
product-nat m n (suc p) rewrite cong ((m * n) *_) (product-nat m n p)
                            | *-assoc m (m ^ p) (n * (n ^ p))
                            | sym (*-assoc (m ^ p) n (n ^ p))
                            | *-comm (m ^ p) n
                            | sym (*-assoc m (n * (m ^ p)) (n ^ p))
                            | sym (*-assoc m n (m ^ p))
                            | *-assoc (m * n) (m ^ p) (n ^ p) = refl

!-nat : ∀ (m : ℕ) → 1 ^ m ≡ 1
!-nat zero = refl
!-nat (suc m) rewrite +-identity' (1 ^ m) | !-nat m = refl

void-suc : ∀ (m : ℕ) → 0 ^ suc m ≡ 0
void-suc m = refl

curry-nat : ∀ (m n p : ℕ) → m ^ (n * p) ≡ (m ^ n) ^ p
curry-nat m n zero rewrite *-zap n = refl
curry-nat m n (suc p) = begin
    m ^ (n * suc p)
  ≡⟨ cong (m ^_) (*-comm n (suc p)) ⟩
    m ^ (suc p * n)
  ≡⟨⟩
    m ^ (n + (p * n))
  ≡⟨ cong (m ^_) (cong (n +_) (*-comm p n)) ⟩
    m ^ (n + (n * p))
  ≡⟨ coproduct-nat m n (n * p) ⟩
    m ^ n * m ^ (n * p)
  ≡⟨ cong (m ^ n *_) (curry-nat m n p) ⟩
    (m ^ n) * ((m ^ n) ^ p)
  ≡⟨⟩
    (m ^ n) ^ suc p
  ∎
