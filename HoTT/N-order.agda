{-# OPTIONS --without-K --exact-split --safe #-}

module N-order where

open import Universes public
open import MLTT public
open Arithmetics renaming(_+_ to _+̇_)

_≤_ _≥_ : ℕ -> ℕ -> 𝒰₀ ̇

infix 10 _≤_
infix 10 _≥_

{-
-- wtf 
_≤_ = ℕ-iteration (ℕ -> 𝒰₀ ̇) (λ y -> 𝟙) (λ f -> ℕ-recursion (𝒰₀ ̇) 𝟘 (λ y P -> f y))
-}

zero ≤ y = 𝟙
succ x ≤ zero = 𝟘
succ x ≤ succ y = x ≤ y

x ≥ y = y ≤ x 

-- Strict inequalities
_<_ _>_ : ℕ -> ℕ -> 𝒰₀ ̇
infix 10 _<_
infix 10 _>_

x < zero = 𝟘
zero < succ y = 𝟙
succ x < succ y = x < y

x > y = y < x

-- Proving the rest of the Peano axioms for ℕ
familyℕ→𝒰 : ℕ -> 𝒰₀ ̇
familyℕ→𝒰 0 = 𝟘
familyℕ→𝒰 (succ n) = ℕ

positivesNotZero : (x : ℕ) -> (succ x) ≢ 0
positivesNotZero x p = transport familyℕ→𝒰 p x

-- Lifting succs
succUp : (x y : ℕ) -> x ≡ y -> (succ x) ≡ (succ y)
succUp zero zero eq = refl (succ 0)
succUp (succ x) (succ .x) (refl .(succ x)) = refl (succ (succ x))

succLess : {x y : ℕ} -> succ x ≡ succ y -> x ≡ y
succLess {x} {.x} (refl .(succ x)) = refl x

-- Note that the fith axiom is just ℕ-induction

ℕ-hasDecidableEquality : hasDecidableEq ℕ
ℕ-hasDecidableEquality zero zero = inl (refl 0)
ℕ-hasDecidableEquality zero (succ n1) = inr (≢-sym (positivesNotZero n1))
ℕ-hasDecidableEquality (succ n0) zero = inr (positivesNotZero n0)
ℕ-hasDecidableEquality (succ n0) (succ n1) = f (ℕ-hasDecidableEquality n0 n1)
    where
        f : decidable (n0 ≡ n1) -> decidable (succ n0 ≡ succ n1)
        f (inl p) = inl (ap succ p)
        f (inr fₚ) = inr (λ (s : succ n0 ≡ succ n1) -> fₚ (succLess s))

-- prove antisymmetry of strict ordering
<asym : (x y : ℕ) -> x < y -> ¬(y < x)
<asym zero (succ y) l = id
<asym (succ x) (succ y) l = <asym x y l

≤refl : {x : ℕ} -> x ≤ x -> x ≤ x
≤refl l = l

≤asym : (x y : ℕ) -> x ≤ y -> (x ≡ y -> 𝟘) -> (y ≤ x -> 𝟘) 
≤asym zero zero * ne = λ _ -> ne (refl 0)
≤asym zero (succ y) * ne = id
≤asym (succ x) (succ y) l ne = ≤asym x y l (λ eq -> ne (succUp x y eq))

≤trans : (x y z : ℕ) -> x ≤ y -> y ≤ z -> x ≤ z
≤trans zero zero zero l k = *
≤trans zero zero (succ z) l k = *
≤trans zero (succ y) (succ z) l k = *
≤trans (succ x) (succ y) (succ z) l k = ≤trans x y z l k

-- Prove the following: x ≤ y if and only if Σ z ꞉ ℕ , x + z ≡ y.

{-
≤ToΣ : (x y : ℕ) -> x ≤ y -> Σ z :- ℕ , (x +̇ z ≡ y)
≤ToΣ zero zero leq = (0 , refl 0)
≤ToΣ zero (succ y) leq = {!   !}
≤ToΣ (succ x) (succ y) leq = {!   !}
-}