{-# OPTIONS --without-K --exact-split --safe #-}

module MLTT where

open import Universes public

variable
    𝒰 𝒱 𝒲 𝒯 : Universe

-- The 1 type

data 𝟙 : 𝒰₀ ̇ where
    * : 𝟙

𝟙-induction : (A : 𝟙 -> 𝒰 ̇) -> A * -> (x : 𝟙) -> A x
𝟙-induction A a * = a

𝟙-recursion : (B : 𝒰 ̇) -> B -> (𝟙 -> B)
𝟙-recursion B b x = 𝟙-induction (λ _ -> B) b x

-- Her har vi eksplisitt sagt hva den avhengige typen er
!𝟙' : (X : 𝒰 ̇) -> X -> 𝟙
!𝟙' X x = *

-- Her blir det nevnt implisitt
!𝟙 : {X : 𝒰 ̇} -> X -> 𝟙
!𝟙 x = *

-- The zero type

data 𝟘 : 𝒰₀ ̇ where

𝟘-induction : {A : 𝟘 -> 𝒰 ̇} -> (x : 𝟘) -> A x
𝟘-induction ()

𝟘-recursion : {A : 𝒰 ̇} -> 𝟘 -> A
𝟘-recursion ()

!𝟘 = 𝟘-recursion

is-empty : 𝒰 ̇ -> 𝒰 ̇
is-empty X = X -> 𝟘

¬ : 𝒰 ̇ -> 𝒰 ̇
¬ X = X -> 𝟘

-- Natural numbers

data ℕ : 𝒰₀ ̇ where
    zero : ℕ
    succ : ℕ -> ℕ
{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : (A : ℕ -> 𝒰 ̇) -> A 0 -> ((n : ℕ) -> A n -> A (succ n)) -> (n : ℕ) -> A n
ℕ-induction A a₀ f = h
    where
        h : (n : ℕ) -> A n
        h 0 = a₀
        h (succ n) = f n (h n)

ℕ-recursion : (A : 𝒰 ̇) -> A -> (ℕ -> A -> A) -> ℕ -> A
ℕ-recursion A = ℕ-induction (λ _ -> A) -- This uses point free style to define recursion.
-- Notice how we take the type and make it into a constant dependent type with a lambda abstraction.

ℕ-iteration : (X : 𝒰 ̇) -> X -> (X -> X) -> ℕ -> X
ℕ-iteration X x fₓ n = ℕ-recursion X x (λ _ -> fₓ) n

    module Arithmetics where
    private
        _+_ _×_ : ℕ -> ℕ -> ℕ
        infixl 20 _+_
        infixl 21 _×_

        x + y = (ℕ-iteration ℕ x succ) y

        x × y = (ℕ-iteration ℕ 0 (x +_)) y

-- Coproduct types

data _+_ {𝒰 𝒱} (X : 𝒰 ̇) (Y : 𝒱 ̇) : 𝒰 ⊔ 𝒱  ̇ where
    inl : X -> X + Y
    inr : Y -> X + Y

+-induction : {X : 𝒰 ̇} {Y : 𝒱 ̇} (A : X + Y -> 𝒲 ̇) -> ((x : X) -> A (inl x)) -> ((y : Y) -> A (inr y)) -> (z : X + Y) -> A z
+-induction A f _ (inl x) = f x
+-induction A _ g (inr y) = g y

+-recursion : {X : 𝒰 ̇} {Y : 𝒱 ̇} {A : 𝒲 ̇} -> (X -> A) -> (Y -> A) -> X + Y -> A
+-recursion {𝒰} {𝒱} {𝒲} {X} {Y} {A} = +-induction (λ _ -> A)

𝟚 : 𝒰₀ ̇
𝟚 = 𝟙 + 𝟙

pattern ₀ = inl *
pattern ₁ = inr *

𝟚-induction : {A : 𝟚 -> 𝒰 ̇} -> A ₀ -> A ₁ -> (n : 𝟚) -> A n
𝟚-induction a₀ _ ₀ = a₀
𝟚-induction _ a₁ ₁ = a₁

-- We can also define 𝟚-induction with +-induction.
-- It will be cool to check if these are propositonally the same after making the identity type.

record Σ {𝒰 𝒱} {X : 𝒰 ̇} (Y : X -> 𝒱 ̇) : 𝒰 ⊔ 𝒱  ̇ where 
    constructor _,_
    field
        x : X
        y : Y x

infix 6 _,_

pr₁ : {X : 𝒰 ̇} {Y : X -> 𝒱 ̇} -> Σ Y -> X
pr₁ (x , _) = x

pr₂ : {X : 𝒰 ̇} {Y : X -> 𝒱 ̇} -> (z : Σ Y) -> Y (pr₁ z)
pr₂ (_ , y) = y

-Σ : {𝒰 𝒱 : Universe} (X : 𝒰 ̇) (Y : X -> 𝒱 ̇) -> 𝒰 ⊔ 𝒱  ̇
-Σ X Y = Σ Y

syntax -Σ X (λ x -> y) = Σ x :- X , y

Σ-induction : {X : 𝒰 ̇} {Y : X -> 𝒱 ̇} {A : Σ Y -> 𝒲 ̇} -> ((x : X) (y : Y x) -> A (x , y)) -> ((x , y) : Σ Y) -> A (x , y)
Σ-induction f (x , y) = f x y

curry : {X : 𝒰 ̇} {Y : X -> 𝒱 ̇} {A : Σ Y -> 𝒲 ̇} -> (((x , y) : Σ Y) -> A (x , y)) -> ((x : X) (y : Y x) -> A (x , y))
curry f x y = f (x , y)

-- We define Pair as a special case of the dependent sum type
_×_ : 𝒰 ̇ -> 𝒱 ̇ -> 𝒰 ⊔ 𝒱 ̇
X × Y = Σ x :- X , Y

-- Π types
Π : {X : 𝒰 ̇} (A : X -> 𝒱 ̇) -> 𝒰 ⊔ 𝒱 ̇
Π {𝒰} {𝒱} {X} A = (x : X) -> A x

-Π : {𝒰 𝒱 : Universe} (X : 𝒰 ̇) (Y : X -> 𝒱 ̇) -> 𝒰 ⊔ 𝒱 ̇
-Π X Y = Π Y

syntax -Π A (λ x -> b) = Π x :- A , b

id : {X : 𝒰 ̇} -> X -> X
id x = x

_∘_ : {X : 𝒰 ̇} {Y : 𝒱 ̇} {Z : Y -> 𝒲 ̇} -> ((y : Y) -> Z y) -> (f : X -> Y) -> (x : X) -> Z (f x)
g ∘ f = λ x -> g (f x)

domain : {X : 𝒰 ̇} {Y : 𝒱 ̇} -> (X -> Y) -> 𝒰 ̇
domain {𝒰} {𝒱} {X} {Y} _ = X

codomain : {X : 𝒰 ̇} {Y : 𝒱 ̇} -> (X -> Y) -> 𝒱 ̇
codomain {𝒰} {𝒱} {X} {Y} _ = Y

type-of : {X : 𝒰 ̇} -> X -> 𝒰 ̇
type-of {𝒰} {X} x = X

-- The identity type
data Id {𝒰} (X : 𝒰 ̇) : X -> X -> 𝒰 ̇ where
    refl : (x : X) -> Id X x x

_≡_ : {X : 𝒰 ̇} -> X -> X -> 𝒰 ̇
x ≡ y = Id _ x y

infix 8 _≡_

J : (X : 𝒰 ̇) (A : (x y : X) -> x ≡ y -> 𝒱 ̇) -> ((x : X) -> A x x (refl x)) -> (x y : X) (p : x ≡ y) -> A x y p
J X A f x x (refl x) = f x