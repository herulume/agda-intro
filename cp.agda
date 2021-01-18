module cp where

open import Function using (_∘_; id)

infixr 50 _|+|_ _⊕_
infixr 60 _|*|_ _×_

record True : Set where

data Functor : Set₁ where
  |Id|  : Functor
  |K|   : Set → Functor
  _|+|_ : Functor → Functor → Functor
  _|*|_ : Functor → Functor → Functor

|1| = |K| True

data _⊕_ (A B : Set) : Set where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

-- Decode function
<[_]> : Functor → Set → Set
<[ |Id| ]> X = X
<[ |K| A ]> X = A
<[ F |+| G ]> X = <[ F ]> X ⊕ <[ G ]> X
<[ F |*| G ]> X = <[ F ]> X × <[ G ]> X

fmap : (F : Functor) {X Y : Set} → (X → Y) → <[ F ]> X → <[ F ]> Y
fmap |Id| f x = f x
fmap (|K| A) f x = x
fmap (F |+| G) f (inl x) = inl (fmap F f x)
fmap (F |+| G) f (inr x) = inr (fmap G f x)
fmap (F |*| G) f (x , y) = fmap F f x , fmap G f y


data List (A : Set) : Set where
  Nil : List A
  Cons : A → List A → List A

[_,_] : {A B C : Set} → (A → C) → (B → C) → A ⊕ B → C
[ f , g ] (inl x) = f x
[ f , g ] (inr y) = g y

_-|-_ : {A B C D : Set} → (A → C) → (B → D) → A ⊕ B → C ⊕ D
(f -|- g) = [ inl ∘ f , inr ∘ g ]

_><_ : {A B C D : Set} → (A → C) → (B → D) → A × B → C × D
(f >< g) (fst , snd) = (f fst , g snd)

uncurry : {A B C : Set} → (A → B → C) → A × B → C
uncurry f (x , x₁) = f x x₁

const : {A B : Set} → A → B → A
const x _ = x

ListF : (A : Set) → Functor
ListF A = |1| |+| (|K| A) |*| |Id|

recList : ∀ {A B C} → (B → C) → <[ ListF A ]> B  → <[ ListF A ]> C
recList f = id -|- (id >< f)

outList : ∀ {A} → List A → <[ ListF A ]> (List A)
outList Nil = inl _
outList (Cons a xs) = inr (a , xs)

inList : ∀ {A} → <[ ListF A ]> (List A) → List A
inList = [ const Nil , uncurry Cons ]

{-# TERMINATING #-}
cataList : ∀ {A B} → (<[ ListF A ]> B → B) → List A → B
cataList g = g ∘ recList (cataList g) ∘ outList

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr f acc  = cataList φ  where
  φ = [ const acc , uncurry f ]
