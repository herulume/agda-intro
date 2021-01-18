module example where

open import Level using (Level)
open import Data.Nat
open import Data.Bool hiding (_<?_)

-- Logic
{-
data   False : Set where
record True  : Set where

data Either (A : Set) (B : Set) : Set where
  Left  : A → Either A B
  Right : B → Either A B

data _×_ (A : Set) (B : Set) : Set where
  _,_ : A → B → A × B
-}

{-
infixr 3 ¬_
¬_ : Set → Set
¬ A = ?
-}

{-
absurd : {X : Set} → False → X
absurd = ?
-}

{-
notCurry : ∀ {P Q R : Set} → ((Q × P) → R) → P → Q → R
notCurry = ?
-}

{-
-- either
[_,_] : ∀ {A B C : Set} → (A → C) → (B → C) → Either A B → C
[ f , g ] (Left x)  = f x
[ f , g ] (Right x) = g x

-- split
<_,_> : ∀ {A B C : Set} → (A → B) → (A → C) → A → B × C
< f , g > a = f a , g a
-}

-- Lists
{-
infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

l1 : List Bool
l1 = true ∷ false ∷ []

length : ∀ {A} → List A → ℕ
length = ?

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr f b []       = b
foldr f b (x ∷ xs) = f x (foldr f b xs)
-}

-- Dependent types
{-

data _>=_ : ℕ → ℕ → Set where
  z>= : {y : ℕ} → y >= zero
  s>= : {x y : ℕ} → x >= y → suc x >= suc y

p : (n : ℕ) → n >= zero
p = ?

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

dif : (m : ℕ) → (n : ℕ)
    → m >= n
    → Σ ℕ (λ r → m ≡ (n + r))
dif = ?
-}

{-
data Vec {l : Level} (A : Set l) : ℕ → Set l where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (1 + n)
-}

{-
_++_ : ∀ {l} {m n} {A : Set l} → Vec A m → Vec A n → Vec A (m + n)
_++_  = ?
-}

{-
headᵛ : ∀ {l} {A : Set l} {n : ℕ} → Vec A (succ n) → A
headᵛ = ?
-}

{-
_<₀_ : ℕ → ℕ → Bool
n <₀ m = ?
-}

{-
_ <₀ zero = false
zero <₀ suc m = true
suc n <₀ suc m = n <₀ m
-}

{-
isTrue : Bool → Set
isTrue true = True
isTrue false = False

headˡ : ∀ {A} (l : List A) → isTrue (zero <₀ length l) → A
headˡ = ? -- split list first by hand
-}

{-
data _<₁_ : ℕ → ℕ → Set where
  z< : {y : ℕ} → zero <₁ suc y
  s< : {x y : ℕ} → x <₁ y → suc x <₁ suc y

headˡ₁ : ∀ {A} (l : List A) → zero <₁ length l → A
headˡ₁ (x ∷ _) z< = x
-}


-- https://mazzo.li/posts/AgdaSort.html

{-
Rel : Set → Set₁
Rel A = A → A → Set

Decidable : ∀ {A} → Rel A → Set
Decidable R = ∀ x y → Either (R x y) (¬ (R x y))

record Equivalence {X} (_≈_ : Rel X) : Set₁ where
  field
    refl  : ∀ {x}     → x ≈ x
    sym   : ∀ {x y}   → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

record TotalOrder {X} (_≈_ : Rel X) (_≤_ : Rel X) : Set₁ where
  field
    antisym     : ∀ {x y}   → x ≤ y → y ≤ x → x ≈ y
    trans       : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    total       : ∀ x y     → Either (x ≤ y) (y ≤ x)
    reflexive   : ∀ {x y}   → x ≈ y → x ≤ y
    equivalence : Equivalence _≈_


module Sort {A : Set} {_≈_ _≤_ : Rel A}
            (_≤?_ : Decidable _≤_) (ord : TotalOrder _≈_ _≤_) where

  open TotalOrder ord using (total; equivalence)
  open Equivalence equivalence using (refl)


  data ⊥A⊤ : Set where
    ⊤  : ⊥A⊤
    ⊥  : ⊥A⊤
    ⟦_⟧ : A → ⊥A⊤

  data _≤^_ : Rel ⊥A⊤ where
    ⊥≤^    : ∀ {x} → ⊥ ≤^ x
    ≤^⊤    : ∀ {x} → x ≤^ ⊤
    ≤-lift : ∀ {x y} → x ≤ y → ⟦ x ⟧ ≤^ ⟦ y ⟧

  data OList (l u : ⊥A⊤) : Set where
    nil  : l ≤^ u → OList l u
    cons : ∀ x (xs : OList ⟦ x ⟧ u) → l ≤^ ⟦ x ⟧ → OList l u

  toList : ∀ {l u} → OList l u → List A
  toList (nil _)       = []
  toList (cons x xs _) = x ∷ toList xs

  insert : ∀ {l u} x → OList l u → l ≤^ ⟦ x ⟧ → ⟦ x ⟧ ≤^ u → OList l u
  insert x (nil l≤u) l≤x x≤u = cons x (nil x≤u) l≤x
  insert x (cons x₁ xs l≤x₁) l≤x x≤u with x ≤? x₁
  ... | Left x≤x₁ = cons x (cons x₁ xs (≤-lift x≤x₁)) l≤x
  ... | Right x>x₁ = cons x₁ (insert x xs ([ ≤-lift , (λ x≤x₁ → absurd (x>x₁ x≤x₁)) ] (total x₁ x)) x≤u) l≤x₁

  isort : List A → List A
  isort l = toList (isort' l) where
   isort' : List A → OList ⊥ ⊤
   isort' = foldr (λ x xs → insert x xs ⊥≤^ ≤^⊤) (nil ⊥≤^)


≡-eq : ∀ {A} → Equivalence {A} (_≡_)
≡-eq = record { refl = refl ; sym = λ { refl → refl } ; trans = λ { refl refl → refl } }

data _≤₁_ : ℕ → ℕ → Set where
  z< : {y : ℕ} → zero ≤₁ y
  s< : {x y : ℕ} → x ≤₁ y → suc x ≤₁ suc y

_≤₁?_ : Decidable _≤₁_
zero ≤₁? _ = Left z<
suc n ≤₁? zero = Right (λ ())
suc n ≤₁? suc m with n ≤₁? m
... | Left x = Left (s< x)
... | Right x = Right (λ { (s< z) → x z })

=-<-ord : TotalOrder (_≡_) (_≤₁_)
=-<-ord = record
            { antisym = <-antisym
            ; trans = <-trans
            ; total = <-total
            ; reflexive = λ { refl → <-refl }
            ; equivalence = ≡-eq
            } where
            <-refl : ∀ {x} → x ≤₁ x
            <-refl {zero} = z<
            <-refl {suc x} = s< <-refl

            <-total : ∀ x y → Either (x ≤₁ y) (y ≤₁ x)
            <-total zero _ = Left z<
            <-total (suc x) zero = Right z<
            <-total (suc x) (suc y) with <-total x y
            ... | Left z = Left (s< z)
            ... | Right z = Right (s< z)

            <-trans : ∀ {x} {y} {z} (x₁ : x ≤₁ y) (y₁ : y ≤₁ z) → x ≤₁ z
            <-trans {zero} {zero}  {z} _ 0≤z = 0≤z
            <-trans {zero} {suc y} {z} z< _ = z<
            <-trans {suc x} {suc y} {.(suc _)} (s< x≤y1) (s< y≤y1) = s< (<-trans x≤y1 y≤y1)


            <-antisym : ∀ {x} {y} (x₁ : x ≤₁ y) (y₁ : y ≤₁ x) → x ≡ y
            <-antisym {zero} {zero} z< z< = refl
            <-antisym {suc x} {suc y} (s< x≤y) (s< y≤x) with <-antisym x≤y y≤x
            ... | refl = refl

list : List ℕ
list = 40 ∷ 2 ∷ 0 ∷ 23 ∷ 1 ∷ []

lists : List ℕ → List ℕ × List ℕ
lists l = l , isort l where
  open Sort _≤₁?_ =-<-ord

-}
