module plfa.Lambda where

open import Relation.Binary.PropositionalEquality using (cong; _≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])
open import plfa.Isomorphism using (_≤_)

Id : Set
Id = String

infix 5 ƛ_⇒_
infix 5 μ_⇒_
infixl 7 _·_
infix 8 `suc_
infix 9 `_

data Term : Set where
  `_ :                    Id → Term
  ƛ_⇒_ :                  Id → Term → Term
  _·_ :                   Term → Term → Term
  `zero :                 Term
  `suc_ :                 Term → Term
  case_[zero⇒_|suc_⇒_] :  Term → Term → Id → Term → Term
  μ_⇒_ :                  Id → Term → Term

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
          ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc ` "n"

mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ `zero
          |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n")]

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
          plusᶜ · ` "n" · ` "z" · (plusᶜ · ` "m") · ` "z"

ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N = ƛ x ⇒ N
ƛ′ _ ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N = μ x ⇒ N
μ′ _ ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"

mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
        case′ m
          [zero⇒ `zero
          |suc m ⇒ plus′ · n · (* · m · n)]
  where
  * = ` "*"
  m = ` "m"
  n = ` "n"

data Value : Term → Set where
  V-ƛ : ∀ {x N}
        ---------------
      → Value (ƛ x ⇒ N)

  V-zero :
        ----------------
        Value `zero

  V-suc : ∀ {V}
      → Value V
        ----------------
      → Value (`suc V)

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
...               | yes _ = V
...               | no _ = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
...               | yes _ = ƛ x ⇒ N
...               | no _ = ƛ x ⇒ N [ y := V ]
(z · z₁) [ y := V ] = z [ y := V ] · z₁ [ y := V ]
`zero [ y := V ] = `zero
(`suc z) [ y := V ] = `suc z [ y := V ]
case z [zero⇒ z₁ |suc x ⇒ z₂ ] [ y := V ] with x ≟ y
(case z [zero⇒ z₁ |suc x ⇒ z₂ ] [ y := V ]) | yes p = case z [ y := V ] [zero⇒ z₁ [ y := V ] |suc x ⇒ z₂ ]
(case z [zero⇒ z₁ |suc x ⇒ z₂ ] [ y := V ]) | no ¬p = case z [ y := V ] [zero⇒ z₁ [ y := V ] |suc x ⇒ z₂ [ y := V ] ]
(μ x ⇒ z) [ y := V ] with x ≟ y
((μ x ⇒ z) [ y := V ]) | yes p = μ x ⇒ z
((μ x ⇒ z) [ y := V ]) | no ¬p = (μ x ⇒ z [ y := V ])

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z"))
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ (sucᶜ · (sucᶜ · `zero))
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ (ƛ "x" ⇒ `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ (ƛ "x" ⇒ ` "x")
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ (ƛ "y" ⇒ ` "y")
_ = refl

_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ] ≡ (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x"))
_ = refl

match : Id → Id → Term → Term → Term
match x y yup nope with x ≟ y
...             | yes _ = yup
...             | no _ = nope

_[_:=_]′ : Term → Id → Term → Term
(` x) [ y := V ]′ = match x y V (` x)
(ƛ x ⇒ N) [ y := V ]′ = match x y (ƛ x ⇒ N) (ƛ x ⇒ N [ y := V ]′)
(z · z₁) [ y := V ]′ = z [ y := V ]′ · z₁ [ y := V ]′
`zero [ y := V ]′ = `zero
(`suc z) [ y := V ]′ = `suc z [ y := V ]′
case z [zero⇒ z₁ |suc x ⇒ z₂ ] [ y := V ]′ with x ≟ y
(case z [zero⇒ z₁ |suc x ⇒ z₂ ] [ y := V ]′) | yes p = case z [ y := V ]′ [zero⇒ z₁ [ y := V ]′ |suc x ⇒ z₂ ]
(case z [zero⇒ z₁ |suc x ⇒ z₂ ] [ y := V ]′) | no ¬p = case z [ y := V ]′ [zero⇒ z₁ [ y := V ]′ |suc x ⇒ z₂ [ y := V ]′ ]
(μ x ⇒ z) [ y := V ]′ = match x y (μ x ⇒ z) (μ x ⇒ z [ y := V ]′)

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]′ ≡ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z"))
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ]′ ≡ (sucᶜ · (sucᶜ · `zero))
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ]′ ≡ (ƛ "x" ⇒ `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ]′ ≡ (ƛ "x" ⇒ ` "x")
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ]′ ≡ (ƛ "y" ⇒ ` "y")
_ = refl

_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ] ≡ (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x"))
_ = refl

infix 4 _—→_

data _—→_ : Term → Term → Set where
  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      -----------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      -------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
      ------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ---------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

_ : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") —→ (ƛ "x" ⇒ ` "x")
_ = β-ƛ V-ƛ

_ : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→ (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
_ = ξ-·₁ (β-ƛ V-ƛ)

_ : twoᶜ · sucᶜ · `zero —→ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
_ = ξ-·₁ (β-ƛ V-ƛ)

infix 2 _—↠_
infix 1 begin_
infixr 2 _—→⟨_⟩_
infix 3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
     ---------
   → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

trans—↠ : {L M N : Term} → L —↠ M → M —↠ N → L —↠ N
trans—↠ (M ∎) mn = mn
trans—↠ (L —→⟨ x ⟩ lm) mn = L —→⟨ x ⟩ (trans—↠ lm mn)

open _—↠_

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

data _—↠′_ : Term → Term → Set where
  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N

open _—↠′_

—↠≤—↠′ : ∀ {M N : Term} → M —↠ N ≤ M —↠′ N
—↠≤—↠′ = record {
  to = to ;
  from = from ;
  from∘to = from∘to }
  where

  to : ∀ {M N : Term} → M —↠ N → M —↠′ N
  to (M ∎) = refl′
  to (L —→⟨ x ⟩ M—↠N) = trans′ (step′ x) (to M—↠N)

  from : ∀ {M N : Term} → M —↠′ N → M —↠ N
  from {M} {N} (step′ x) = M —→⟨ x ⟩ N ∎
  from {M} {N} refl′ = M ∎
  from (trans′ x y) = trans—↠ (from x) (from y)

  from∘to : ∀ {M N : Term} → (mn : M —↠ N) → from (to mn) ≡ mn
  from∘to (M ∎) = refl
  from∘to (L —→⟨ x ⟩ mn) rewrite from∘to mn = refl

_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ = begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `zero)
  —→⟨ ξ-·₂ (β-ƛ V-zero) ⟩
    (ƛ "n" ⇒ `suc ` "n") · (`suc `zero)
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc `suc `zero
  ∎

_ : plus · two · two —↠ `suc `suc `suc `suc `zero
_ = begin
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
           case ` "m"
             [zero⇒ ` "n"
             |suc "m" ⇒ `suc (plus · ` "m" · ` "n")]) · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
       case two
         [zero⇒ ` "n"
         |suc "m" ⇒ `suc (plus · ` "m" · ` "n")]) · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
     case two
       [zero⇒ two
       |suc "m" ⇒ `suc (plus · ` "m" · two)]
  —→⟨ β-suc ⟩
     `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
           case ` "m"
             [zero⇒ ` "n"
             |suc "m" ⇒ `suc (plus · ` "m" · ` "n")]) · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ "n" ⇒
       case `suc `zero
         [zero⇒ ` "n"
         |suc "m" ⇒ `suc (plus · ` "m" · ` "n")]) · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
     `suc (case `suc `zero
       [zero⇒ two
       |suc "m" ⇒ `suc (plus · ` "m" · two)])
  —→⟨ ξ-suc β-suc ⟩
     `suc (`suc (plus · `zero · two))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc (`suc ((ƛ "m" ⇒ ƛ "n" ⇒
           case ` "m"
             [zero⇒ ` "n"
             |suc "m" ⇒ `suc (plus · ` "m" · ` "n")]) · `zero · two))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc (`suc ((ƛ "n" ⇒
       case `zero
         [zero⇒ ` "n"
         |suc "m" ⇒ `suc (plus · ` "m" · ` "n")]) · two))
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
     `suc (`suc (case `zero
       [zero⇒ two
       |suc "m" ⇒ `suc (plus · ` "m" · two)]))
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
     `suc (`suc (`suc (`suc `zero)))
  ∎
