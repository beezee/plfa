import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm; +-suc; +-identityʳ)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
     ----------
   → zero ≤ n

  s≤s : ∀ {m n : ℕ}
   → m ≤ n
     -------------
   → suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
  ---------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {n : ℕ}
  → n ≤ zero
  ----------
  → n ≡ zero
inv-z≤n z≤n = refl

≤-suc : ∀ {m n : ℕ}
  → suc m ≤ n
    ---------
  → m ≤ n
≤-suc {zero} (s≤s smn) = z≤n
≤-suc {suc m} (s≤s smn) = s≤s (≤-suc smn)

≤-refl : ∀ {n : ℕ}
  -------
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
  -------
  → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
  -------
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s mn) (s≤s nm) rewrite ≤-antisym mn nm = refl

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      -----
    → Total m n

  flipped :
      n ≤ m
      -----
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                       | forward mn = forward (s≤s mn)
...                       | flipped nm = flipped (s≤s nm)

≤-total' : ∀ (m n : ℕ) → Total m n
≤-total' zero n = forward z≤n
≤-total' (suc m) zero = flipped z≤n
≤-total' (suc m) (suc n) = ≤-incr (≤-total' m n)
  where
  ≤-incr : Total m n → Total (suc m) (suc n)
  ≤-incr (forward x) = forward (s≤s x)
  ≤-incr (flipped x) = flipped (s≤s x)

+-monoʳ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → p + m ≤ p + n
+-monoʳ-≤ m n zero mn = mn
+-monoʳ-≤ m n (suc p) mn = s≤s (+-monoʳ-≤ m n p mn)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p mn rewrite +-comm m p | +-comm n p = +-monoʳ-≤ m n p mn

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q mn pq = ≤-trans (+-monoˡ-≤ m n p mn) (+-monoʳ-≤ p q n pq)

*-monoʳ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → p * m ≤ p * n
*-monoʳ-≤ m n zero mn = z≤n
*-monoʳ-≤ m n (suc p) mn = +-mono-≤ m n (p * m) (p * n) mn (*-monoʳ-≤ m n p mn)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m * p ≤ n * p
*-monoˡ-≤ m n p mn rewrite *-comm m p | *-comm n p = *-monoʳ-≤ m n p mn

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ m n p q mn pq = ≤-trans (*-monoˡ-≤ m n p mn) (*-monoʳ-≤ p q n pq)

data _<_ : ℕ → ℕ → Set where
  z<n : ∀ {n : ℕ}
     ----------
   → zero < suc n

  s<s : ∀ {m n : ℕ}
   → m < n
     -------------
   → suc m < suc n

inv-s<s : ∀ {m n : ℕ}
  → suc m < suc n
    -------------
  → m < n
inv-s<s (s<s smn) = smn

<-suc : ∀ (n : ℕ)
      -------
    → n < suc n
<-suc zero = z<n
<-suc (suc n) = s<s (<-suc n)

suc-≤-< : ∀ (m n : ℕ)
  → suc m ≤ n
    ---------
  → m < n
suc-≤-< zero (suc n) smn = z<n
suc-≤-< (suc m) (suc n) smn = s<s (suc-≤-< m n (inv-s≤s smn))

<-≤-suc : ∀ (m n : ℕ)
  → m < n
    ---------
  → suc m ≤ n
<-≤-suc zero (suc n) mn = s≤s z≤n
<-≤-suc (suc m) (suc n) mn = s≤s (<-≤-suc m n (inv-s<s mn))

<-trans : ∀ (m n p : ℕ)
  → m < n
  → n < p
    -----
  → m < p
<-trans m n p mn np = suc-≤-< m p (≤-trans (<-≤-suc m n mn) (≤-suc (<-≤-suc n p np)))

data Trichotomy (m n : ℕ) : Set where

  forward :
      m < n
      -----
    → Trichotomy m n

  flipped :
      n < m
      -----
    → Trichotomy m n

  equal :
      n ≡ m
      -----
    → Trichotomy m n

≡-suc : ∀ {m n : ℕ}
    → m ≡ n
      -----
    → (suc m) ≡ (suc n)
≡-suc {zero} {zero} mn = refl
≡-suc {suc m} {suc n} mn = cong suc mn

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = equal refl
<-trichotomy zero (suc n) = forward z<n
<-trichotomy (suc m) zero = flipped z<n
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                                 | forward mn = forward (s<s mn)
...                                 | flipped mn = flipped (s<s mn)
...                                 | equal mn = equal (≡-suc mn)

<-mono-+ : ∀ (m n p : ℕ)
    → m < n
      -------------
    → (m + p) < (n + p)
<-mono-+ m n zero mn rewrite +-identityʳ m | +-identityʳ n = mn
<-mono-+ m n (suc p) mn rewrite +-suc m p | +-suc n p = s<s (<-mono-+ m n p mn)
