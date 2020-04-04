module plfa.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; suc; zero; _<_; _≤_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]; swap)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; extensionality)
open _≤_

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  →   A
    ---
  →   ⊥
¬-elim ¬a a = ¬a a

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  →     A
    -----
  → ¬ ¬ A
¬¬-intro a = λ ¬a → ¬-elim ¬a a

¬¬-intro′ : ∀ {A : Set}
  →     A
    -----
  → ¬ ¬ A
¬¬-intro′ a ¬a = ¬a a

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  →     ¬ A
¬¬¬-elim ¬¬¬a a = ¬¬¬a (¬¬-intro a)

contraposition : ∀ {A B : Set}
  →     (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition ab ¬ba a = ¬ba (ab a)

_≢_ : ∀ {A : Set} → A → A → Set
a ≢ a′ = ¬(a ≡ a′)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id⊥ : ⊥ → ⊥
id⊥ = λ()

id⊥′ : ⊥ → ⊥
id⊥′ x = x

id⊥≡id⊥′ : id⊥ ≡ id⊥′
id⊥≡id⊥′ = extensionality λ()

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ a → ⊥-elim (¬x a)

suc-≤-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
suc-≤-< (_≤_.s≤s _≤_.z≤n) = _≤_.s≤s _≤_.z≤n
suc-≤-< (_≤_.s≤s (_≤_.s≤s smn)) = _≤_.s≤s (_≤_.s≤s smn)

<-irreflexive : ∀ {n : ℕ} → ¬(n < n)
<-irreflexive {suc n} (_≤_.s≤s x) = <-irreflexive {n} (suc-≤-< x)

data Trichotomy (m n : ℕ) : Set where

  forward :
      m < n
    → ¬ n < m
    → ¬ m ≡ n
      -----
    → Trichotomy m n

  flipped :
      n < m
    → ¬ m < n
    → ¬ n ≡ m
      -----
    → Trichotomy m n

  equal :
      n ≡ m
    → ¬ n < m
    → ¬ m < n
      -----
    → Trichotomy m n

≡-suc : ∀ {m n : ℕ}
    → m ≡ n
      -----
    → (suc m) ≡ (suc n)
≡-suc {zero} {zero} mn = refl
≡-suc {suc m} {suc n} mn = cong suc mn

≡→≮ : ∀ {m n : ℕ} → (m ≡ n) → ¬(m < n)
≡→≮ refl = <-irreflexive

<→≯ : ∀ {m n : ℕ} → (m < n) → ¬(n < m)
<→≯ {zero} {suc n} m<n = λ()
<→≯ {suc m} {suc n} (_≤_.s≤s m<n) (_≤_.s≤s n<m) = <→≯ {m} {n} m<n n<m

<→≢ : ∀ {m n : ℕ} → (m < n) → m ≢ n
<→≢ {m} {n} m<n refl = <-irreflexive m<n

z<n : ∀ {n : ℕ} → zero < suc n
z<n = s≤s z≤n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = equal refl (≡→≮ refl) (≡→≮ refl)
<-trichotomy zero (suc n) = forward z<n (<→≯ z<n) (<→≢ z<n)
<-trichotomy (suc m) zero = flipped z<n (<→≯ z<n) (<→≢ z<n)
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                                 | forward mn n₁ n₂ = forward (s≤s mn) (
                                          λ{ (s≤s nm) → n₁ nm }) λ{ refl → n₂ refl }
...                                 | flipped mn n₁ n₂ = flipped (s≤s mn) (
                                          λ{ (s≤s nm) → n₁ nm }) λ{ refl → n₂ refl }
...                                 | equal mn n₁ n₂ = equal (≡-suc mn) (
                                          λ{ (s≤s nm) → n₁ nm }) (
                                          λ{ (s≤s mn) → n₂ mn })

dmgto : ∀ {A B : Set} → ¬(A ⊎ B) ≃ (¬ A) × (¬ B)
dmgto =
  record
    {   to = λ x → (λ x₁ → x (inj₁ x₁)) , (λ x₁ → x (inj₂ x₁))
      ; from = λ x → [ proj₁ x , proj₂ x ]
      ; from∘to = λ a → extensionality λ a₁ → ⊥-elim (a a₁)
      ; to∘from = λ{ (na , nb) → refl }
    }

dmgfrom : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬(A × B)
dmgfrom (inj₁ x) = x ∘ proj₁
dmgfrom (inj₂ y) = y ∘ proj₂

postulate
  em : ∀{A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ x → x (inj₂ (λ y → x (inj₁ y)))

em→¬¬-elim : ∀ {A : Set} → (A ⊎ ¬ A) → (¬ ¬ A → A)
em→¬¬-elim a⊎¬a x = [ (λ a → a) , ⊥-elim ∘ x ] a⊎¬a

em→pierce : ∀ {A B : Set} → (A ⊎ ¬ A) → ((A → B) → A) → A
em→pierce em aba = [ (λ a → a) , (λ ¬a → aba (λ a → ⊥-elim (¬a a))) ] em

em→arr→⊎ : ∀ {A B : Set} → (A ⊎ ¬ A) → (A → B) → ¬ A ⊎ B
em→arr→⊎ em ab = [ inj₂ ∘ ab , inj₁ ] em

em→demorgan : ({A : Set} → (A ⊎ ¬ A)) → {A B : Set} → ¬(¬ A × ¬ B) → A ⊎ B
em→demorgan em {A} {B} d with em {A} | em {B}
em→demorgan em d | inj₁ x | _ = inj₁ x
em→demorgan em d | _ | inj₁ x = inj₂ x
em→demorgan em d | inj₂ ¬a | inj₂ ¬b = ⊥-elim (d (¬a , ¬b))

¬¬-elim→em : ({A : Set} → (¬ ¬ A → A)) → ({A : Set} → A ⊎ ¬ A)
¬¬-elim→em nnaa = nnaa em-irrefutable

¬¬-elim→pierce : ({A : Set} → (¬ ¬ A → A)) → {A B : Set} → ((A → B) → A) → A
¬¬-elim→pierce nnaa = em→pierce (nnaa em-irrefutable)

¬¬-elim→arr→⊎ : ({A : Set} → (¬ ¬ A → A)) → {A B : Set} → (A → B) → ¬ A ⊎ B
¬¬-elim→arr→⊎ nnaa = em→arr→⊎ (nnaa em-irrefutable)

¬¬-elim→demorgan : ({A : Set} → (¬ ¬ A → A)) → {A B : Set} → ¬(¬ A × ¬ B) → A ⊎ B
¬¬-elim→demorgan nnaa = em→demorgan (nnaa em-irrefutable)

pierce→¬¬-elim : ({A B : Set} → ((A → B) → A) → A) → ({A : Set} → (¬ ¬ A → A))
pierce→¬¬-elim abaa = λ x → abaa (⊥-elim ∘ x)

pierce→em : ({A B : Set} → ((A → B) → A) → A) → {A : Set} → A ⊎ ¬ A
pierce→em abaa = ¬¬-elim→em (pierce→¬¬-elim abaa)

pierce→arr→⊎ : ({A B : Set} → ((A → B) → A) → A) → {A B : Set} → (A → B) → ¬ A ⊎ B
pierce→arr→⊎ abaa = ¬¬-elim→arr→⊎ (pierce→¬¬-elim abaa)

pierce→demorgan : ({A B : Set} → ((A → B) → A) → A) → {A B : Set} → ¬(¬ A × ¬ B) → A ⊎ B
pierce→demorgan abaa = ¬¬-elim→demorgan (pierce→¬¬-elim abaa)

arr→⊎→em : ({A B : Set} → (A → B) → ¬ A ⊎ B) → ({A : Set} → A ⊎ ¬ A)
arr→⊎→em abab = swap (abab λ a → a)

arr→⊎→¬¬-elim : ({A B : Set} → (A → B) → ¬ A ⊎ B) → ({A : Set} → ¬ ¬ A → A)
arr→⊎→¬¬-elim abab = em→¬¬-elim (arr→⊎→em abab)

arr→⊎→pierce : ({A B : Set} → (A → B) → ¬ A ⊎ B) → ({A B : Set} → ((A → B) → A) → A)
arr→⊎→pierce abab = em→pierce (arr→⊎→em abab)

arr→⊎→demorgan : ({A B : Set} → (A → B) → ¬ A ⊎ B) → {A B : Set} → ¬(¬ A × ¬ B) → A ⊎ B
arr→⊎→demorgan abab = em→demorgan (arr→⊎→em abab)

demorgan→¬¬-elim : ({A B : Set} → ¬(¬ A × ¬ B) → A ⊎ B) → ({A : Set} → ¬ ¬ A → A)
demorgan→¬¬-elim abab = λ x → [ (λ a → a) , (λ a → a) ] (abab (λ ¬a×¬a → x (proj₁ ¬a×¬a)))

demorgan→em : ({A B : Set} → ¬(¬ A × ¬ B) → A ⊎ B) → ({A : Set} → A ⊎ ¬ A)
demorgan→em abab = ¬¬-elim→em (demorgan→¬¬-elim abab)

demorgan→pierce : ({A B : Set} → ¬(¬ A × ¬ B) → A ⊎ B) → ({A B : Set} → ((A → B) → A) → A)
demorgan→pierce abab = ¬¬-elim→pierce (demorgan→¬¬-elim abab)

demorgan→arr→⊎ : ({A B : Set} → ¬(¬ A × ¬ B) → A ⊎ B) → ({A B : Set} → (A → B) → ¬ A ⊎ B)
demorgan→arr→⊎ abab = ¬¬-elim→arr→⊎ (demorgan→¬¬-elim abab)

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬→Stable : ∀ {A : Set} → ¬ A → Stable (¬ A)
¬→Stable ¬a = ¬¬¬-elim

Stable×Stable→Stable : ∀ {A B : Set} → Stable A × Stable B → Stable (A × B)
Stable×Stable→Stable {A} {B} (sa , sb) ¬¬ab = (a , b)
  where
    a = sa λ x → ¬¬ab λ x₁ → x (proj₁ x₁)
    b = sb λ x → ¬¬ab λ x₁ → x (proj₂ x₁)
