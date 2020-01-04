import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

_ : inc ⟨⟩ ≡ ⟨⟩ I
_ =
  begin
    inc ⟨⟩
  ≡⟨⟩
    ⟨⟩ I
  ∎

_ : inc (inc ⟨⟩) ≡ ⟨⟩ I O
_ =
  begin
    inc (inc ⟨⟩)
  ≡⟨⟩
    inc (⟨⟩ I)
  ≡⟨⟩
    ⟨⟩ I O
  ∎

_ : inc (inc (inc ⟨⟩)) ≡ ⟨⟩ I I
_ =
  begin
    inc (inc (inc ⟨⟩))
  ≡⟨⟩
    inc (inc (⟨⟩ I))
  ≡⟨⟩
    inc (⟨⟩ I O)
  ≡⟨⟩
    ⟨⟩ I I
  ∎

_ : inc (inc (inc (inc ⟨⟩))) ≡ (((⟨⟩ I) O) O)
_ =
  begin
    inc (inc (inc (inc ⟨⟩)))
  ≡⟨⟩
    inc (inc (inc (⟨⟩ I)))
  ≡⟨⟩
    inc (inc (⟨⟩ I O))
  ≡⟨⟩
    inc (⟨⟩ I I)
  ≡⟨⟩
    (((⟨⟩ I) O) O)
  ∎

to : ℕ → Bin
to zero = ⟨⟩
to (suc b) = inc (to b)

_ : (to 0) ≡ ⟨⟩
_ = refl

_ : (to 1) ≡ ⟨⟩ I
_ =
  begin
    (to 1)
  ≡⟨⟩ -- is shorthand for
    (to (suc zero))
  ≡⟨⟩ -- inductive case to
    (inc (to zero))
  ≡⟨⟩ -- base case to
    inc ⟨⟩
  ≡⟨⟩ -- base case inc
    ⟨⟩ I
  ∎


_ : (to 2) ≡ ⟨⟩ I O
_ =
  begin
    (to 2)
  ≡⟨⟩ -- is shorthand for
    (to (suc (suc zero)))
  ≡⟨⟩ -- inductive case to
    (inc (to (suc zero)))
  ≡⟨⟩ -- inductive case to
    inc (inc (to zero))
  ≡⟨⟩ -- base case to
    inc (inc ⟨⟩)
  ≡⟨⟩ -- base case inc
    inc (⟨⟩ I)
  ≡⟨⟩ -- inductive case inc
    (inc ⟨⟩) O
  ≡⟨⟩ -- base case inc
    ⟨⟩ I O
  ∎

_ : (to 3) ≡ ⟨⟩ I I
_ =
  begin
    (to 3)
  ≡⟨⟩ -- is shorthand for
    (to (suc (suc (suc zero))))
  ≡⟨⟩ -- inductive case to
    (inc (to (suc (suc zero))))
  ≡⟨⟩ -- inductive case to
    inc (inc (to (suc zero)))
  ≡⟨⟩ -- inductive case to
    inc (inc (inc (to zero)))
  ≡⟨⟩ -- base case to
    inc (inc (inc ⟨⟩))
  ≡⟨⟩ -- base case inc
    inc (inc (⟨⟩ I))
  ≡⟨⟩ -- inductive case inc
    inc ((inc ⟨⟩) O)
  ≡⟨⟩ -- base case inc
    inc (⟨⟩ I O)
  ≡⟨⟩ -- base case inc
    ⟨⟩ I I
  ∎

_ : (to 4) ≡ ⟨⟩ I O O
_ =
  begin
    (to 4)
  ≡⟨⟩ -- is shorthand for
    (to (suc (suc (suc (suc zero)))))
  ≡⟨⟩ -- inductive case to
    (inc (to (suc (suc (suc zero)))))
  ≡⟨⟩ -- inductive case to
    inc (inc (to (suc (suc zero))))
  ≡⟨⟩ -- inductive case to
    inc (inc (inc (to (suc zero))))
  ≡⟨⟩ -- base case to
    inc (inc (inc (inc ⟨⟩)))
  ≡⟨⟩ -- base case inc
    inc (inc (inc (⟨⟩ I)))
  ≡⟨⟩ -- inductive case inc
    inc (inc ((inc ⟨⟩) O))
  ≡⟨⟩ -- base case inc
    inc (inc (⟨⟩ I O))
  ≡⟨⟩ -- base case inc
    inc (⟨⟩ I I)
  ≡⟨⟩ -- inductive case inc
    (inc (⟨⟩ I)) O
  ≡⟨⟩ -- inductive case inc
    (inc ⟨⟩) O O
  ≡⟨⟩ -- base case inc
    ⟨⟩ I O O
  ∎

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = 2 * (from b)
from (b I) = 1 + 2 * (from b)

_ : (from (⟨⟩ O)) ≡ zero
_ = refl

_ : (from (⟨⟩ I)) ≡ (suc zero)
_ =
  begin
    from (⟨⟩ I)
  ≡⟨⟩ -- inductive case
    1 + 2 * (from ⟨⟩)
  ≡⟨⟩ -- base case
    1 + 2 * zero
  ≡⟨⟩ -- simplify
    1
  ≡⟨⟩ -- is shorthand for
    suc zero
  ∎

_ : (from (⟨⟩ I O)) ≡ (suc (suc zero))
_ =
  begin
    from (⟨⟩ I O)
  ≡⟨⟩ -- inductive case
    2 * (from (⟨⟩ I))
  ≡⟨⟩ -- inductive case
    2 * (1 + 2 * (from ⟨⟩))
  ≡⟨⟩ -- base case
    2 * (1 + 2 * zero)
  ≡⟨⟩ -- simplify
    2 * 1
  ≡⟨⟩ -- simplify
    2
  ≡⟨⟩ -- is shorthand for
    suc (suc zero)
  ∎

_ : (from (⟨⟩ I I)) ≡ (suc (suc (suc zero)))
_ =
  begin
    from (⟨⟩ I I)
  ≡⟨⟩ -- inductive case
    1 + 2 * (from (⟨⟩ I))
  ≡⟨⟩ -- inductive case
    1 + 2 * (1 + 2 * (from ⟨⟩))
  ≡⟨⟩ -- base case
    1 + 2 * (1 + 2 * zero)
  ≡⟨⟩ -- simplify
    1 + 2 * 1
  ≡⟨⟩ -- simplify
    3
  ≡⟨⟩ -- is shorthand for
    suc (suc (suc zero))
  ∎

_ : (from (⟨⟩ I O O)) ≡ (suc (suc (suc (suc zero))))
_ =
  begin
    from (⟨⟩ I O O)
  ≡⟨⟩ -- inductive case
    2 * (from (⟨⟩ I O))
  ≡⟨⟩ -- inductive case
    2 * (2 * (from (⟨⟩ I)))
  ≡⟨⟩ -- inductive case
    2 * (2 * (1 + 2 * (from ⟨⟩)))
  ≡⟨⟩ -- base case
    2 * (2 * (1 + 2 * zero))
  ≡⟨⟩ -- simplify
    2 * 2 * 1 + 0
  ≡⟨⟩ -- simplify
    4
  ≡⟨⟩ -- is shorthand for
    suc (suc (suc (suc zero)))
  ∎
