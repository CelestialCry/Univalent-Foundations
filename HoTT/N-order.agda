{-# OPTIONS --without-K --exact-split --safe #-}

module N-order where

open import Universes public
open import MLTT public

_≤_ _≥_ : ℕ -> ℕ -> 𝒰₀ ̇

infix 10 _≤_
infix 10 _≥_

-- wtf
_≤_ = ℕ-iteration (ℕ -> 𝒰₀ ̇) (λ y -> 𝟙) (λ f -> ℕ-recursion (𝒰₀ ̇) 𝟘 (λ y P -> f y))

{-
zero ≤ y = 𝟙
succ x ≤ zero = 𝟘
succ x ≤ succ y = x ≤ y
-}

x ≥ y = y ≤ x 
