module AgdaBasics where

-- Definition of a Data Type
-- This looks a lot like GADTs in Haskell
data Bool : Set where
    true : Bool
    false : Bool

-- Simple function with pattern matching
not : Bool -> Bool
not true = false
not false = true

-- Inductive definition of the Natural numbers
data ℕ : Set where
    zero : ℕ
    succ : ℕ -> ℕ

-- An addition binary function using the mix-fix style
infixl 60 _*_
_+_ : ℕ -> ℕ -> ℕ
zero + n = n
m + zero = m
succ n + m = succ (n + m)

-- ^ but multiplication
infixl 40 _+_
_*_ : ℕ -> ℕ -> ℕ
zero * n = zero
m * zero = zero
succ n * m = m + n * m

-- mix-fix or
infixr 20 _or_
_or_ : Bool -> Bool -> Bool
true or _ = true
false or x = x

infix  5 if_then_else_
if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true then x else _ = x
if _ then _ else x = x

-- Definition of list looks different
infixr 40 _::_
data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A

-- Definition of a sequence
infixr 40 _◁_
data _* (α : Set) : Set where
    ε : α *
    _◁_ : α -> α * -> α *   

-- First dependent funtion
-- (A : Set) is like Pi_(A:Set) (Set is the universe of all sets as types)
id : (A : Set) -> A -> A
id A x = x

-- dependent function application
apply : (A : Set)(B : A -> Set) -> ((x : A) -> B x) -> (a : A) -> B a
apply A B f a = f a

-- dependent function composition
_◯_ : {A : Set}{B : A -> Set}{C : (x : A) -> B -> Set}(f : {x : A}(y : B x) -> C x y)(g : (x : A) -> B x)(x : A) -> C x (g x)
(f ◯ g) x = f (g x)

pluss-two : ℕ -> ℕ
pluss-two = succ ◯ succ

map : {A B : Set} -> (A -> B) -> List A -> List B
map _ [] = []
map f (x :: xs) = f x :: (map f xs)

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs + ys)

data Vec (A : Set) : ℕ -> Set where
    [] : Vec A zero
    _::_ : {n : ℕ} -> A -> Vec A n -> Vec A (succ n)

head : {A : Set}{n : ℕ} -> Vec A (succ n) -> A
x :: _ = x

vmap : {A B : Set}{n : ℕ} -> (A -> B) -> Vec A n -> Vec B n
vmap f [] = []
vmap f (x :: xs) = f x :: vmap f xs

data Image_∌_ : {A B : Set}(f : A -> B) : B -> Set where
    im : (x : A) -> Image f ∌ f x

inv : {A B : Set}(f : A -> B)(y : B) -> Image f ∌ y -> A
inv f .(f x) (im x) = x

data Fin : ℕ -> Set where
    fzero : {n : ℕ} -> Fin (succ n)
    fsucc : {n : ℕ} -> Fin n -> Fin (succ n)