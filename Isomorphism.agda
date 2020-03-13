module plfa.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; suc; zero; _+_; _*_)
open import Data.Nat.Properties using (+-comm)

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) a = g (f a)

_∘′_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f = λ a → g (f a)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (a : A) → f a ≡ g a)
      ----------------------
    → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = f m n
    where
      f : ∀ (m n : ℕ) → m +′ n ≡ n + m
      f m zero = refl
      f m (suc n) = cong suc (f m n)

same : _+′_ ≡ _+_
same = extensionality λ m → extensionality λ n → same-app m n

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → ∀(x : A) → f x ≡ g x
      ---------------------
    → f ≡ g

infix 0 _≃_
record _≃_ (A B : Set): Set where
  field
    to : A → B
    from : B → A
    from∘to : ∀(a : A) → from (to a) ≡ a
    to∘from : ∀(b : B) → to (from b) ≡ b
open _≃_

≃-refl : ∀ {A : Set}
    -----
  → A ≃ A
≃-refl {A} =
  record
    {   to = λ a → a
      ; from = λ a → a
      ; from∘to = λ a → refl
      ; to∘from = λ a → refl
    }

≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
≃-sym ab =
  record
    {   to = from ab
      ; from = to ab
      ; from∘to = to∘from ab
      ; to∘from = from∘to ab
    }

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans ab bc =
  record
    {   to = to bc ∘ to ab
      ; from = from ab ∘ from bc
      ; from∘to = λ a → begin
            from ab (from bc (to bc (to ab a)))
          ≡⟨ cong (from ab) (from∘to bc (to ab a)) ⟩
            from ab (to ab a)
          ≡⟨ from∘to ab a ⟩
            a
          ∎
      ; to∘from = λ b → begin
          to bc (to ab (from ab (from bc b)))
        ≡⟨ cong (to bc) (to∘from ab (from bc b)) ⟩
          to bc (from bc b)
        ≡⟨ to∘from bc b ⟩
          b
        ∎
    }

module ≃-Reasoning where

  infix 1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix 3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin ab = ab

  _≃⟨_⟩_ : ∀ (A : Set) {A B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  a ≃⟨ ab ⟩ bc = ≃-trans ab bc

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  a ≃-∎ = ≃-refl

open ≃-Reasoning

infix 0 _≤_
record _≤_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : ∀ (a : A) → from (to a) ≡ a

open _≤_

≤-refl : {A : Set} → A ≤ A
≤-refl {A} =
  record {
    to = λ x → x;
    from = λ x → x;
    from∘to = λ a → refl
  }

≤-trans : {A B C : Set}
    → A ≤ B
    → B ≤ C
      -----
    → A ≤ C
≤-trans ab bc =
    record {
      to = λ x → to bc (to ab x);
      from = λ x → from ab (from bc x);
      from∘to = λ a → begin
          from ab (from bc (to bc (to ab a)))
        ≡⟨ cong (from ab) (from∘to bc (to ab a)) ⟩
          from ab (to ab a)
        ≡⟨ from∘to ab a ⟩
          a
        ∎
    }

≤-antisym : {A B : Set}
    → (ab : A ≤ B)
    → (ba : B ≤ A)
    → (to ab ≡ from ba)
    → (from ab ≡ to ba)
      -----------------
    → A ≃ B
≤-antisym ab ba tofrom fromto =
    record {
      to = to ab;
      from = from ab;
      from∘to = from∘to ab;
      to∘from = λ b → begin
          to ab (from ab b)
        ≡⟨ cong (λ x → to ab (x b)) fromto ⟩
          to ab (to ba b)
        ≡⟨ cong (λ x → x (to ba b)) tofrom ⟩
          from ba (to ba b)
        ≡⟨ from∘to ba b ⟩
          b
        ∎
    }

module ≤-Reasoning where

    infix 1 ≤-begin
    infix 2 _≤⟨_⟩_
    infix 3 _≤-∎

    ≤-begin : {A B : Set}
      → A ≤ B
        -----
      → A ≤ B
    ≤-begin ab = ab

    _≤⟨_⟩_ : (A : Set) {B C : Set}
      → A ≤ B
      → B ≤ C
        -----
      → A ≤ C
    a ≤⟨ ab ⟩ bc = ≤-trans ab bc

    _≤-∎ : ∀ {A : Set}
        -----
      → A ≤ A
    _≤-∎ = ≤-refl

≃-implies-≤ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≤ B
≃-implies-≤ ab =
  record {
    to = to ab ;
    from = from ab ;
    from∘to = from∘to ab
  }

record _⇔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
open _⇔_

⇔-refl : {A : Set}
    -----
  → A ⇔ A
⇔-refl = record { to = λ x → x ; from = λ x → x }

⇔-sym : {A B : Set}
  → A ⇔ B
    -----
  → B ⇔ A
⇔-sym ab = record { to = from ab; from = to ab }

⇔-trans : {A B C : Set}
  → A ⇔ B
  → B ⇔ C
    ----
  → A ⇔ C
⇔-trans ab bc =
  record {
    to = λ x → to bc (to ab x) ;
    from = λ x → from ab (from bc x)
  }

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

nbin : ℕ → Bin
nbin zero = ⟨⟩
nbin (suc b) = inc (nbin b)

binn : Bin → ℕ
binn ⟨⟩ = zero
binn (b O) = 2 * (binn b)
binn (b I) = 1 + 2 * (binn b)

+-suc : ∀ (m n : ℕ) → (m + suc n) ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

binn∘inc : ∀{b : Bin} → binn (inc b) ≡ suc (binn b)
binn∘inc {⟨⟩} = refl
binn∘inc {b O} = refl
binn∘inc {b I} rewrite binn∘inc {b} | +-suc (binn b) (binn b + 0) = refl

binn∘nbin : ∀(n : ℕ) → binn (nbin n) ≡ n
binn∘nbin zero = refl
binn∘nbin (suc n) rewrite binn∘inc {nbin n} | binn∘nbin n = refl


ℕ≤Bin : ℕ ≤ Bin
ℕ≤Bin =
  record {
    to = nbin;
    from = binn;
    from∘to = binn∘nbin
  }
