import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc : ℕ -> ℕ
{-# BUILTIN NATURAL ℕ #-}

seven = suc (suc (suc (suc (suc (suc (suc zero))))))
five : ℕ
five = 5

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)
{-# BUILTIN NATPLUS _+_ #-}

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩ -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩ -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩ -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩ -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩ -- is longhand for
    5
  ∎

_ : 2 + 5 ≡ 7
_ = refl

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩ -- is shorthand for
    ((suc (suc (suc zero))) +
     (suc (suc (suc (suc zero)))))
  ≡⟨⟩ -- inductive case
    suc ((suc (suc zero)) +
         (suc (suc (suc (suc zero)))))
  ≡⟨⟩ -- inductive case
    suc (suc ((suc zero) +
               (suc (suc (suc (suc zero))))))
  ≡⟨⟩ -- inductive case
    suc (suc (suc (zero +
                  (suc (suc (suc (suc zero)))))))
  ≡⟨⟩ -- base case
    suc (suc (suc (suc (suc (suc (suc zero))))))
  ≡⟨⟩ -- is longhand for
    7
  ∎

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)
{-# BUILTIN NATTIMES _*_ #-}

infixl 6 _+_ _∸_
infixl 7 _*_

_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩ -- inductive case
    3 + 1 * 3
  ≡⟨⟩ -- inductive case
    3 + 3 + 0 * 3
  ≡⟨⟩ -- base case
    3 + 3 + 0
  ≡⟨⟩ -- simplify
    6
  ∎

_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩ -- inductive case
    4 + 2 * 4
  ≡⟨⟩ -- inductive case
    4 + 4 + 1 * 4
  ≡⟨⟩ -- inductive case
    4 + 4 + 4 + 0 * 4
  ≡⟨⟩ -- base case
    4 + 4 + 4 + 0
  ≡⟨⟩ -- simplify
    12
  ∎

_∸_ : ℕ → ℕ → ℕ
n ∸ zero = n
zero ∸ (suc m) = zero
(suc m) ∸ (suc n) = m ∸ n
{-# BUILTIN NATMINUS _∸_ #-}

_ : 3 ∸ 2 ≡ 1
_ =
    begin
      3 ∸ 2
    ≡⟨⟩ -- inductive case
      2 ∸ 1
    ≡⟨⟩ -- inductive case
      1 ∸ zero
    ≡⟨⟩ -- base case
      1
    ∎

_ : 2 ∸ 3 ≡ 0
_ =
  begin
    2 ∸ 3
  ≡⟨⟩ -- inductive case
    1 ∸ 2
  ≡⟨⟩ -- inductive case
    0 ∸ 1
  ≡⟨⟩ -- base case
    0
  ∎

_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩ -- inductive case
    4 ∸ 2
  ≡⟨⟩ -- inductive case
    3 ∸ 1
  ≡⟨⟩ -- inductive case
    2 ∸ 0
  ≡⟨⟩ -- base case
    2
  ∎

_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩ -- inductive case
    2 ∸ 4
  ≡⟨⟩ -- inductive case
    1 ∸ 3
  ≡⟨⟩ -- inductive case
    0 ∸ 2
  ≡⟨⟩ -- base case
    0
  ∎
