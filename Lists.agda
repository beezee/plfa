module plfa.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Empty using (⊥)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-comm; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open _⊎_
open import Function using (_∘_)
open import Level using (Level)
open import plfa.Isomorphism using (_≃_; _⇔_; extensionality)

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

infixr 5 _::_

_ : List ℕ
_ = 0 :: 1 :: 2 :: []

data List′ : Set → Set where
  []′ : ∀ {A : Set} → List′ A
  _::′_ : ∀ {A : Set} → A → List′ A → List′ A

infixr 5 _::′_

_ : List′ ℕ
_ = 0 ::′ 1 ::′ 2 ::′ []′

{-# BUILTIN LIST List #-}

pattern [_] z = z :: []
pattern [_,_] y z = y :: z :: []
pattern [_,_,_] x y z = x :: y :: z :: []
pattern [_,_,_,_] w x y z = w :: x :: y :: z :: []
pattern [_,_,_,_,_] v w x y z = v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_] u v w x y z = u :: v :: w :: x :: y :: z :: []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ y = y
(x :: x₁) ++ y = x :: (x₁ ++ y)

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ = begin
    [ 0 , 1 , 2 ] ++ [ 3 , 4 ]
  ≡⟨⟩
    0 :: ([ 1 , 2 ] ++ [ 3 , 4 ])
  ≡⟨⟩
    0 :: 1 :: ([ 2 ] ++ [ 3 , 4 ])
  ≡⟨⟩
    0 :: 1 :: 2 :: ([] ++ [ 3 , 4 ])
  ≡⟨⟩
    0 :: 1 :: 2 :: [ 3 , 4 ]
  ≡⟨⟩
    [ 0 , 1 , 2 , 3 , 4 ]
  ∎

++-assoc : ∀ {A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x :: xs) ys zs = begin
    ((x :: xs) ++ ys) ++ zs
  ≡⟨⟩
    x :: ((xs ++ ys) ++ zs)
  ≡⟨ cong (λ q → x :: q) (++-assoc xs ys zs) ⟩
    x :: xs ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} → (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} → (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x :: xs) = begin
    x :: xs ++ []
  ≡⟨ cong (x ::_) (++-identityʳ xs) ⟩
    x :: xs
  ∎

length : ∀ {A : Set} → List A → ℕ
length [] = 0
length (x :: xs) = 1 + length xs

_ : length [ 0 , 1 , 2 ] ≡ 3
_ = begin
    length [ 0 , 1 , 2 ]
  ≡⟨⟩
    1 + length [ 1 , 2 ]
  ≡⟨⟩
    2 + length [ 2 ]
  ≡⟨⟩
    3 + (length {ℕ} [])
  ≡⟨⟩
    3 + 0
  ≡⟨⟩
    3
  ∎

length-++ : ∀ {A : Set} → (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x :: xs) ys rewrite (length-++ xs ys) = refl

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x :: xs) = (reverse xs) ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ = begin
    reverse [ 0 , 1 , 2 ]
  ≡⟨⟩
    (reverse [ 1 , 2 ]) ++ [ 0 ]
  ≡⟨⟩
    (reverse [ 2 ] ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨ cong (λ y → ((y) ++ [ 1 ]) ++ [ 0 ]) (++-identityˡ [ 2 ]) ⟩
    ([ 2 ] ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    [ 2 , 1 ] ++ [ 0 ]
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎

reverse-++-distrib : ∀ {A : Set} → (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys = begin
    reverse ([] ++ ys)
  ≡⟨ cong (reverse) (++-identityˡ ys) ⟩
    reverse ys
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    reverse ys ++ []
  ≡⟨⟩
    reverse ys ++ reverse []
  ∎
reverse-++-distrib (x :: xs) ys rewrite reverse-++-distrib xs ys
                                      | ++-assoc (reverse ys) (reverse xs) [ x ] = refl

reverse-involutive : ∀ {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x :: xs) = begin
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    reverse [ x ] ++ reverse (reverse xs)
  ≡⟨ cong (reverse [ x ] ++_) (reverse-involutive xs) ⟩
    reverse [ x ] ++ xs
  ≡⟨⟩
    (reverse [] ++ [ x ]) ++ xs
  ≡⟨⟩
    ([] ++ [ x ]) ++ xs
  ≡⟨⟩
    [ x ] ++ xs
  ≡⟨⟩
    x :: ([] ++ xs)
  ≡⟨ cong (x ::_) (++-identityˡ xs) ⟩
    x :: xs
  ∎

shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x :: xs) ys = shunt xs (x :: ys)

shunt-reverse : ∀ {A : Set} → (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x :: xs) ys rewrite shunt-reverse xs (x :: ys) | ++-assoc (reverse xs) [ x ] ys = refl

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} → (xs : List A) → reverse′ xs ≡ reverse xs
reverses xs = begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ = begin
    reverse′ [ 0 , 1 , 2 ]
  ≡⟨⟩
    shunt [ 0 , 1 , 2 ] []
  ≡⟨⟩
    shunt [ 1 , 2 ] (0 :: [])
  ≡⟨⟩
    shunt [ 2 ] (1 :: 0 :: [])
  ≡⟨⟩
    shunt [] (2 :: 1 :: 0 :: [])
  ≡⟨⟩
    2 :: 1 :: 0 :: []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎

map : ∀ {A B : Set} → (A → B) → (List A → List B)
map f [] = []
map f (x :: la) = f(x) :: (map f la)

_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ = begin
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    1 :: map suc [ 1 , 2 ]
  ≡⟨⟩
    1 :: 2 :: map suc (2 :: [])
  ≡⟨⟩
    1 :: 2 :: 3 :: map suc []
  ≡⟨⟩
    1 :: 2 :: 3 :: []
  ∎

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ = begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎

map-monotone-ev : ∀ {A B C : Set} → (f : A → B) → (g : B → C) → ∀ (a : List A) → map (g ∘ f) a ≡ (map g ∘ map f) a
map-monotone-ev f g [] = refl
map-monotone-ev f g (x :: xs) = begin
    map (g ∘ f) (x :: xs)
  ≡⟨⟩
    (g ∘ f) x :: map (g ∘ f) xs
  ≡⟨ cong ((g ∘ f) x ::_) (map-monotone-ev f g xs) ⟩
    (g ∘ f) x :: (map g ∘ map f) xs
  ≡⟨⟩
    (map g ∘ map f) (x :: xs)
  ∎

map-monotone : ∀ {A B C : Set} → (f : A → B) → (g : B → C) → map (g ∘ f) ≡ (map g) ∘ (map f)
map-monotone {A} f g = extensionality (map-monotone-ev f g)


map-++-distribute : ∀ {A B : Set} → (f : A → B) → (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x :: xs) ys rewrite map-++-distribute f xs ys = refl

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree ac bd (leaf x) = leaf (ac x)
map-Tree ac bd (node t b t₁) = node (map-Tree ac bd t) (bd b) (map-Tree ac bd t₁)

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree ac bc (leaf x) = ac x
fold-Tree ac bc (node t b t₁) = bc (fold-Tree ac bc t) b (fold-Tree ac bc t₁)

map-is-fold-Tree′ : ∀{A B C D : Set}
    → (f : A → C)
    → (g : B → D)
    → (t : Tree A B)
      --------------
    → map-Tree f g t ≡ fold-Tree (λ a → leaf (f a)) (λ c b c₁ → node c (g b) c₁) t
map-is-fold-Tree′ f g (leaf x) = refl
map-is-fold-Tree′ f g (node t x t₁) rewrite map-is-fold-Tree′ f g t | map-is-fold-Tree′ f g t₁ = refl

map-is-fold-Tree : ∀{A B C D : Set} → (f : A → C) → (g : B → D) → map-Tree f g ≡ fold-Tree (λ a → leaf (f a)) (λ c b c₁ → node c (g b) c₁)
map-is-fold-Tree f g = extensionality (map-is-fold-Tree′ f g)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e
foldr _⊗_ e (x :: xs) = x ⊗ foldr _⊗_ e xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ = begin
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    1 + (foldr _+_ 0 [ 2 , 3 , 4 ])
  ≡⟨⟩
    1 + 2 + (foldr _+_ 0 [ 3 , 4 ])
  ≡⟨⟩
    1 + 2 + 3 + (foldr _+_ 0 [ 4 ])
  ≡⟨⟩
    1 + 2 + 3 + 4 + (foldr _+_ 0 [])
  ≡⟨⟩
    1 + 2 + 3 + 4 + 0
  ≡⟨⟩
    10
  ∎

sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ = begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎

foldid : ∀{A : Set} → (xs : List A) → foldr _::_ [] xs ≡ xs
foldid [] = refl
foldid (x :: xs) rewrite foldid xs = refl

foldconcat : ∀{A : Set} → (xs ys : List A) → xs ++ ys ≡ foldr _::_ ys xs
foldconcat [] ys = refl
foldconcat (x :: xs) ys rewrite foldconcat xs ys = refl

product : List ℕ → ℕ
product = foldr _*_ 1

foldr-++ : ∀{A B : Set} → (xs ys : List A) → (_⊗_ : A → B → B) → (e : B)
            → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ [] ys _⊗_ e = refl
foldr-++ (x :: xs) ys _⊗_ e rewrite foldr-++ xs ys _⊗_ e = refl

foldconcat′ : ∀{ A : Set } → (xs ys : List A) → xs ++ ys ≡ foldr _::_ ys xs
foldconcat′ xs ys = begin
    xs ++ ys
  ≡⟨ sym (foldid (xs ++ ys)) ⟩
    foldr _::_ [] (xs ++ ys)
  ≡⟨ foldr-++ xs ys _::_ [] ⟩
    foldr _::_ (foldr _::_ [] ys) xs
  ≡⟨ cong (λ x → foldr _::_ x xs) (foldid ys) ⟩
    foldr _::_ ys xs
  ∎

map-is-foldr′ : ∀{A B : Set} → (f : A → B) → (as : List A) → map f as ≡ foldr (λ x xs → f x :: xs) [] as
map-is-foldr′ f [] = refl
map-is-foldr′ f (x :: as) rewrite map-is-foldr′ f as = refl

map-is-foldr : ∀{A B : Set} → (f : A → B) → map f ≡ foldr (λ x xs → f x :: xs) []
map-is-foldr f = extensionality (map-is-foldr′ f)

downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n :: downFrom n

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = begin
    downFrom 3
  ≡⟨⟩
    2 :: downFrom 2
  ≡⟨⟩
    2 :: 1 :: downFrom 1
  ≡⟨⟩
    2 :: 1 :: 0 :: downFrom 0
  ≡⟨⟩
    2 :: 1 :: 0 :: []
  ∎

downFrom-∸ : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
downFrom-∸ zero = refl
downFrom-∸ (suc zero) = refl
downFrom-∸ (suc (suc n)) =
   begin
    sum (suc n :: downFrom (suc n)) * 2
  ≡⟨⟩
    (suc n + sum (downFrom (suc n))) * 2
  ≡⟨ *-distribʳ-+ 2 (suc n) (sum (downFrom (suc n))) ⟩
    (suc n * 2) + (sum (downFrom (suc n)) * 2)
  ≡⟨ cong ((suc n * 2) +_) (downFrom-∸ (suc n)) ⟩
    (suc n * 2) + suc n * n
  ≡⟨ cong (_+ suc n * n) (*-comm (suc n) 2) ⟩
    (2 * suc n) + suc n * n
  ≡⟨⟩
    suc n + 1 * suc n + suc n * n
  ≡⟨ cong (λ x → suc n + x + suc n * n) (*-identityˡ (suc n)) ⟩
    suc n + suc n + suc n * n
  ≡⟨ cong (λ x → suc n + suc n + x) (*-comm (suc n) n) ⟩
    suc n + suc n + n * suc n
  ≡⟨ +-assoc (suc n) (suc n) (n * suc n) ⟩
    suc n + suc n * suc n
  ≡⟨ refl ⟩
    suc (suc n) * suc n
  ∎

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (a : A) → e ⊗ a ≡ a
    identityʳ : ∀ (a : A) → a ⊗ e ≡ a

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid = record {
    assoc = +-assoc;
    identityˡ = +-identityˡ;
    identityʳ = +-identityʳ }

*-monoid : IsMonoid _*_ 1
*-monoid = record {
    assoc = *-assoc ;
    identityˡ = *-identityˡ ;
    identityʳ = *-identityʳ }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid  = record {
    assoc = ++-assoc ;
    identityˡ = ++-identityˡ ;
    identityʳ = ++-identityʳ }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) → (e : A) → IsMonoid _⊗_ e →
                ∀ (xs : List A) → (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y = sym (identityˡ ⊗-monoid y)
foldr-monoid _⊗_ e ⊗-monoid (x :: xs) y
  rewrite foldr-monoid _⊗_ e ⊗-monoid xs y |
          sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) = refl

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) → (e : A) → IsMonoid _⊗_ e →
                    ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-monoid-++ _⊗_ e ⊗-monoid xs ys = foldr-++ xs ys _⊗_ e

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x :: xs) = foldl _⊗_ (e ⊗ x) xs

foldl-example : ∀ {A B : Set} → (_⊗_ : B → A → B) → (e : B) → (x y z : A) →
        foldl _⊗_ e [ x , y , z ] ≡ ((e ⊗ x) ⊗ y) ⊗ z
foldl-example _⊗_ e x y z = begin
      foldl _⊗_ e [ x , y , z ]
    ≡⟨⟩
      foldl _⊗_ (e ⊗ x) [ y , z ]
    ≡⟨⟩
      foldl _⊗_ ((e ⊗ x) ⊗ y) [ z ]
    ≡⟨⟩
      foldl _⊗_ (((e ⊗ x) ⊗ y) ⊗ z) []
    ≡⟨⟩
      ((e ⊗ x) ⊗ y) ⊗ z
    ∎

append-foldl-is-foldl-append : ∀ {A : Set} → (_⊗_ : A → A → A) → (e : A) → IsMonoid _⊗_ e →
                                (x : A) → (xs : List A) → x ⊗ (foldl _⊗_ e xs) ≡ foldl _⊗_ x xs
append-foldl-is-foldl-append _⊗_ e ⊗-monoid x [] = identityʳ ⊗-monoid x
append-foldl-is-foldl-append _⊗_ e ⊗-monoid x (x₁ :: xs) rewrite
  sym (append-foldl-is-foldl-append _⊗_ e ⊗-monoid (e ⊗ x₁) xs) |
  sym (append-foldl-is-foldl-append _⊗_ e ⊗-monoid (x ⊗ x₁) xs) |
  identityˡ ⊗-monoid x₁ |
  assoc ⊗-monoid x x₁ (foldl _⊗_ e xs) = refl

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) → (e : A) → IsMonoid _⊗_ e →
                      ∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl _⊗_ e ⊗-monoid [] = refl
foldr-monoid-foldl _⊗_ e ⊗-monoid (x :: xs) rewrite
  foldr-monoid-foldl _⊗_ e ⊗-monoid xs | identityˡ ⊗-monoid x = append-foldl-is-foldl-append _⊗_ e ⊗-monoid x xs

data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _::_ : {x : A} → {xs : List A} → P x → All P xs → All P (x :: xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n :: (s≤s z≤n) :: (s≤s (s≤s z≤n)) :: []

data Any {A : Set} (P : A → Set) : List A → Set where
  here : {x : A} → {xs : List A} → P x → Any P (x :: xs)
  there : {x : A} → {xs : List A} → Any P xs → Any P (x :: xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

_ : 3 ∉ [ 0 , 1 , 0 , 2 ]
_ = λ { (here ()); (there (here ())); (there (there (here ()))); (there (there (there (here ())))) }

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
            All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ = λ xs ys → record {
  to = to xs ys;
  from = from xs ys }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) → All P (xs ++ ys) → All P xs × All P ys
  to [] ys all-xs-ys = ⟨ [] , all-xs-ys ⟩
  to (x :: xs) ys (x₁ :: all-xs-ys) with to xs ys all-xs-ys
  to (x :: xs) ys (x₁ :: all-xs-ys) | ⟨ fst , snd ⟩ = ⟨ x₁ :: fst , snd ⟩

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) → All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ fst , snd ⟩ = snd
  from (x :: xs) ys ⟨ x₁ :: fst , snd ⟩ = x₁ :: from xs ys ⟨ fst , snd ⟩

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
            Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ = λ xs ys → record {
  to = to xs ys ;
  from = from xs ys }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  to [] ys any-xs-ys = inj₂ any-xs-ys
  to (x :: xs) ys (here x₁) = inj₁ (here x₁)
  to (x :: xs) ys (there any-xs-ys) with to xs ys any-xs-ys
  to (x :: xs) ys (there any-xs-ys) | inj₁ x₁ = inj₁ (there x₁)
  to (x :: xs) ys (there any-xs-ys) | inj₂ y = inj₂ y

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) → Any P xs ⊎ Any P ys → Any P (xs ++ ys)
  from [] ys (inj₂ y) = y
  from (x :: xs) ys (inj₁ (here x₁)) = here x₁
  from (x :: xs) ys (inj₁ (there x₁)) with from xs ys (inj₁ x₁)
  ...                                 | z = there z
  from (x :: xs) ys (inj₂ y) with from xs ys (inj₂ y)
  ...                                 | z = there z

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
            All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys = record {
  to = _⇔_.to (All-++-⇔ xs ys) ;
  from = _⇔_.from (All-++-⇔ xs ys) ;
  from∘to = fromto xs ys ;
  to∘from = tofrom xs ys }
  where

  fromto : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
              (a : All P (xs ++ ys)) →
                _⇔_.from (All-++-⇔ xs ys) (_⇔_.to (All-++-⇔ xs ys) a) ≡ a
  fromto [] ys all-xs-ys = refl
  fromto (x :: xs) ys (x₁ :: all-xs-ys) with fromto xs ys all-xs-ys
  ...                                     | z = cong (x₁ ::_) z

  tofrom : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
              (a : All P xs × All P ys) →
                _⇔_.to (All-++-⇔ xs ys) (_⇔_.from (All-++-⇔ xs ys) a) ≡ a
  tofrom [] ys ⟨ [] , snd ⟩ = refl
  tofrom (x :: xs) ys ⟨ x₁ :: fst , snd ⟩ with tofrom xs ys ⟨ fst , snd ⟩
  ...                                       | z = cong (λ { ⟨ f , s ⟩ → ⟨ x₁ :: f , s ⟩ }) z

¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs = record { to = to xs ; from = from xs }
  where

  to : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
  to [] not-any = []
  to {A} {P} (x :: xs) not-any = (λ x₁ → not-any (here x₁)) :: (to xs (λ x₁ → not-any (there x₁)))

  from : ∀ {A : Set} {P : A → Set} (xs : List A) → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
  from {A} {P} [] all-not ()
  from {A} {P} (x :: xs) (x₁ :: all-not) with from xs all-not
  ...                                       | z = λ{ (here x₂) →  x₁ x₂; (there x₃) → z x₃ }

¬Any≃All¬ : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs ≃ All (¬_ ∘ P) xs
¬Any≃All¬ xs = record {
  to = _⇔_.to (¬Any⇔All¬ xs) ;
  from = _⇔_.from (¬Any⇔All¬ xs) ;
  from∘to = λ a → from∘to xs a ;
  to∘from = λ b → to∘from xs b }
  where

  from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) → (a : (¬_ ∘ Any P) xs)
                → _⇔_.from (¬Any⇔All¬ xs) (_⇔_.to (¬Any⇔All¬ xs) a) ≡ a
  from∘to {A} {P} [] a = extensionality λ { () }
  from∘to {A} {P} (x :: xs) a = extensionality λ a₁ → ⊥-elim (a a₁)

  to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) → (a : All (¬_ ∘ P) xs)
                → _⇔_.to (¬Any⇔All¬ xs) (_⇔_.from (¬Any⇔All¬ xs) a) ≡ a
  to∘from [] [] = refl
  to∘from {A} {P} (x :: xs) (x₁ :: a) with to∘from xs a
  ...                                   | z = cong (x₁ ::_) z

postulate
  π-extensionality : ∀ {X : Set}{Y : X → Set}
                  → {f g : {x : X} → Y x}
                  → ((x : X) → f {x} ≡ g {x})
                  → (λ {x} → f {x}) ≡ g

All≃∀ : ∀ {A : Set} {P : A → Set} (xs : List A) → All P xs ≃ ∀ {x} → x ∈ xs → P x
All≃∀ xs = record {
  to = to xs ;
  from = from xs ;
  from∘to = from∘to xs ;
  to∘from = to∘from xs }
  where

  to : ∀ {A : Set} {P : A → Set} (xs : List A) → All P xs → (∀ {x : A} → x ∈ xs → P x)
  to [] [] ()
  to {A} {P} (x :: xs) (x₁ :: all-xs) {x₂} with to xs all-xs
  ...                           | z = λ{ (here refl) → x₁ ; (there x₃) → z x₃ }

  shrink-px : {A : Set} {P : A → Set} (x : A) → (xs : List A) → (∀ {x₁} → x₁ ∈ (x :: xs) → P x₁) → (∀ {x₁} → x₁ ∈ xs → P x₁)
  shrink-px x xs px x₁∈xs = px (there x₁∈xs)

  from : ∀ {A : Set} {P : A → Set} (xs : List A) → (∀ {x} → x ∈ xs → P x) → All P xs
  from [] px = []
  from (x :: xs) px = px (here refl) :: from xs (shrink-px x xs px)

  from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) → (a : All P xs) → (from xs) (to xs a) ≡ a
  from∘to [] [] = refl
  from∘to (x :: xs) (x₁ :: all-xs) rewrite from∘to xs all-xs = refl

  to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) → (a : ∀ {x} → x ∈ xs → P x)
                          → (λ {x} → (to xs) (from xs a) {x}) ≡ a
  to∘from [] px = π-extensionality λ x → extensionality λ { () }
  to∘from (x :: xs) px rewrite to∘from xs (shrink-px x xs px) =
    π-extensionality λ x₁ → extensionality λ{ (here refl) → refl; (there x₂) → refl }

Any≃∃ : ∀ {A : Set} {P : A → Set} (xs : List A) → Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
Any≃∃ = λ xs → record {
  to = to xs ;
  from = from xs ;
  from∘to = from∘to xs ;
  to∘from = to∘from xs }
  where

  to : ∀ {A : Set} {P : A → Set} (xs : List A) → Any P xs → ∃[ x ] (x ∈ xs × P x)
  to (x :: xs) (here x₁) = ⟨ x , ⟨ (here refl) , x₁ ⟩ ⟩
  to (x :: xs) (there px) with to xs px
  to (x :: xs) (there px) | ⟨ fst , snd ⟩ = ⟨ fst , ⟨ there (proj₁ snd) , proj₂ snd ⟩ ⟩

  from : ∀ {A : Set} {P : A → Set} (xs : List A) → ∃[ x ] (x ∈ xs × P x) → Any P xs
  from (x :: xs) ⟨ fst , ⟨ here refl , snd ⟩ ⟩ = here snd
  from (x :: xs) ⟨ fst , ⟨ there fst₁ , snd ⟩ ⟩ with from xs ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩
  ...                                            | z = there z

  to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) → (e : ∃[ x ] (x ∈ xs × P x)) → to xs (from xs e) ≡ e
  to∘from (x :: xs) ⟨ fst , ⟨ here refl , snd ⟩ ⟩  = refl
  to∘from (x :: xs) ⟨ fst , ⟨ there fst₁ , snd ⟩ ⟩ =
    cong (λ{ ⟨ x₁ , ⟨ x₂ , x₃ ⟩ ⟩ → ⟨ x₁ , ⟨ there x₂ , x₃ ⟩ ⟩ }) (to∘from xs ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩)

  from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) → (a : Any P xs) → from xs (to xs a) ≡ a
  from∘to (x :: xs) (here x₁) = refl
  from∘to (x :: xs) (there a) = cong (λ x → there x) (from∘to xs a)

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P = ∀ (x : A) → Dec (P x)

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all pred = foldr _∧_ true ∘ map pred

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? {A} {P} d [] = yes []
All? {A} {P} d (x :: xs) with d x | All? d xs
All? {A} {P} d (x :: xs) | yes p | yes p₁ = yes (p :: p₁)
All? {A} {P} d (x :: xs) | yes p | no ¬p = no λ { (p₁ :: p₂) → ¬p p₂ }
All? {A} {P} d (x :: xs) | no ¬p | z = no λ { (p₁ :: p₂) → ¬p p₁ }

any : ∀ {A : Set} → (A → Bool) → List A → Bool
any pred = foldr _∨_ false ∘ map pred

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? {A} {P} d [] = no λ { () }
Any? {A} {P} d (x :: xs) with d x | Any? d xs
Any? {A} {P} d (x :: xs) | yes p | _ = yes (here p)
Any? {A} {P} d (x :: xs) | no ¬p | yes p = yes (there p)
Any? {A} {P} d (x :: xs) | no ¬p | no ¬p₁ = no λ { (here x) → ¬p x; (there x) → ¬p₁ x }

data merge {A : Set} : (xs ys zs : List A) → Set where
  [] :
      --------------
      merge [] [] []

  left-:: : ∀ {x xs ys zs}
    → merge xs ys zs
      ----------------------------
    → merge (x :: xs) ys (x :: zs)

  right-:: : ∀ {y xs ys zs}
    → merge xs ys zs
      ----------------------------
    → merge xs (y :: ys) (y :: zs)

_ : merge [ 1 , 4 ] [ 2 , 3 ] [ 1 , 2 , 3 , 4 ]
_ = left-:: (right-:: (right-:: (left-:: [])))

split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) → (zs : List A)
  → ∃[ xs ] ∃[ ys ] ( merge xs ys zs × All P xs × All (¬_ ∘ P) ys )
split {A} {P} d [] = ⟨ [] , ⟨ [] , ⟨ [] , ⟨ [] , [] ⟩ ⟩ ⟩ ⟩
split {A} {P} d (x :: zs) with d x | split d zs
split {A} {P} d (x :: zs) | yes p | ⟨ fst , ⟨ fst₁ , ⟨ fst₂ , ⟨ fst₃ , snd ⟩ ⟩ ⟩ ⟩ =
  ⟨ x :: fst , ⟨ fst₁ , ⟨ left-:: fst₂ , ⟨ p :: fst₃ , snd ⟩ ⟩ ⟩ ⟩
split {A} {P} d (x :: zs) | no ¬p | ⟨ fst , ⟨ fst₁ , ⟨ fst₂ , ⟨ fst₃ , snd ⟩ ⟩ ⟩ ⟩ =
  ⟨ fst , ⟨ x :: fst₁ , ⟨ right-:: fst₂ , ⟨ fst₃ , ¬p :: snd ⟩ ⟩ ⟩ ⟩
