import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)

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
