{-# OPTIONS --without-K --exact-split --safe #-}

module N-order where

open import Universes public
open import MLTT public
open Arithmetics renaming(_+_ to _+̇_) renaming(_×_ to _×̇_)

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

-- Decidable equality of the naturals
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

≤succ : (x : ℕ) -> x ≤ succ x
≤succ zero = *
≤succ (succ x) = ≤succ x

zeroMin : (n : ℕ) -> 0 ≤ n
zeroMin zero = *
zeroMin (succ n) = zeroMin n

uniqueMin : (n : ℕ) -> n ≤ 0 -> n ≡ 0
uniqueMin zero l = refl 0
uniqueMin (succ n) l = !𝟘 (succ n ≡ 0) l

-- Associativity of addition
+-assoc : (x y z : ℕ) -> (x +̇ y) +̇ z ≡ x +̇ (y +̇ z)
+-assoc x y zero = ((x +̇ y) +̇ 0) ≡⟨ refl (x +̇ y) ⟩ ((x +̇ (y +̇ 0)) ■)
+-assoc x y (succ z) = ((x +̇ y) +̇ succ z) ≡⟨ refl _ ⟩
                        (succ ((x +̇ y) +̇ z) ≡⟨ ap succ (+-assoc x y z) ⟩
                        (succ (x +̇ (y +̇ z)) ≡⟨ refl _ ⟩
                        ((x +̇ (y +̇ succ z)) ■))) 

-- An alternate way of proving it using more of Agda's magic
+-assocAlt : (x y z : ℕ) -> (x +̇ y) +̇ z ≡ x +̇ (y +̇ z)
+-assocAlt x y zero = refl _
+-assocAlt x y (succ z) = ap succ (+-assocAlt x y z)

-- Proving 0 + x = x
0AddxIsx : (x : ℕ) -> 0 +̇ x ≡ x
0AddxIsx zero = refl 0
0AddxIsx (succ x) = ap succ (0AddxIsx x)

-- Proving succ x = 1 + x
succxIs1Addx : (x : ℕ) -> succ x ≡ 1 +̇ x
succxIs1Addx zero = refl 1
succxIs1Addx (succ x) = ap succ (succxIs1Addx x)

-- One more succ ability
+-stepOnFirst : (x y : ℕ) -> (succ x) +̇ y ≡ succ (x +̇ y)
+-stepOnFirst x zero = refl _
+-stepOnFirst x (succ y) = (succ x +̇ succ y) ≡⟨ refl _ ⟩ (
                            (succ (succ x +̇ y)) ≡⟨ ap succ (+-stepOnFirst x y) ⟩ (
                            (succ (x +̇ succ y)) ■))

-- Commutativity of addition
+-comm : (x y : ℕ) -> x +̇ y ≡ y +̇ x
+-comm zero y = (0 +̇ y) ≡⟨ 0AddxIsx y ⟩ (y ≡⟨ refl y ⟩ ((y +̇ 0) ■))
+-comm (succ x) y = (succ x +̇ y) ≡⟨ +-stepOnFirst x y ⟩ (
                    succ (x +̇ y) ≡⟨ ap succ (+-comm x y) ⟩ (
                    succ (y +̇ x) ≡⟨ refl _ ⟩ (
                    (y +̇ succ x)■)))

-- Proving that addition is left cancellative
+-lc : (x y z : ℕ) -> x +̇ y ≡ x +̇ z -> y ≡ z
+-lc zero y z pf = y ≡⟨ (0AddxIsx y) ⁻¹ ⟩ ((0 +̇ y) ≡⟨ pf ⟩ ((0 +̇ z) ≡⟨ 0AddxIsx z ⟩ (z ■)))
+-lc (succ x) y z pf = +-lc x y z (succLess ((succ (x +̇ y)) ≡⟨ (+-stepOnFirst x y) ⁻¹ ⟩ (
                                                (succ x +̇ y) ≡⟨ pf ⟩ (
                                                    (succ x +̇ z) ≡⟨ (+-stepOnFirst x z) ⟩ (
                                                        succ (x +̇ z) ■)))))

-- Prove the following: x ≤ y if and only if Σ z ꞉ ℕ , x + z ≡ y.

≤ToΣ : (x y : ℕ) -> x ≤ y -> Σ z :- ℕ , (x +̇ z ≡ y)
≤ToΣ 0 0 l = 0 , refl 0
≤ToΣ 0 (succ y) l = succ y , 0AddxIsx (succ y)
≤ToΣ (succ x) 0 l = !𝟘 (Σ z :- ℕ , ((succ x +̇ z) ≡ 0)) l
≤ToΣ (succ x) (succ y) l = let z : ℕ
                               z = pr₁ (≤ToΣ x y l) 
                           in z , ((succ x +̇ z) ≡⟨ +-stepOnFirst x z ⟩ (
                                    succ (x +̇ z) ≡⟨ ap succ (pr₂ (≤ToΣ x y l)) ⟩ (
                                    (succ y) ■)))

ΣTo≤ : (x y : ℕ) -> Σ z :- ℕ , (x +̇ z ≡ y) -> x ≤ y
ΣTo≤ zero zero _ = *
ΣTo≤ zero (succ y) _ = *
ΣTo≤ (succ x) zero (z , p) = positivesNotZero (x +̇ z) (succ (x +̇ z) ≡⟨ (+-stepOnFirst x z) ⁻¹ ⟩ ((succ x +̇ z) ≡⟨ p ⟩ (refl 0)) )
ΣTo≤ (succ x) (succ y) (z , p) = ΣTo≤ x y (z , succLess (succ (x +̇ z) ≡⟨ (+-stepOnFirst x z) ⁻¹ ⟩ ((succ x +̇ z) ≡⟨ p ⟩ (refl (succ y)))))