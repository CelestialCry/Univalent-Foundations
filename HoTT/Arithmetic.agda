{-# OPTIONS --without-K --exact-split --safe #-}

module Arithmetic where

open import Universes public

variable
    𝒰 : Universe

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

ℕ-recursion : (X : 𝒰 ̇) -> X -> (ℕ -> X -> X) -> ℕ -> X
ℕ-recursion X = ℕ-induction (λ _ -> X)

_+_ _×_ : ℕ -> ℕ -> ℕ
infixl 20 _+_
infixl 21 _×_

zero + y = y
succ x + y = succ (x + y)

zero × y = 0
succ x × y = x + x × y
