{-# OPTIONS --without-K --exact-split --safe #-}

module Arithmetic where

open import MLTT hiding(_+_) public
-- Arithmetic using pattern matching and not induction

_+_ _×_ : ℕ -> ℕ -> ℕ
infixl 20 _+_
infixl 21 _×_

x + zero = x
x + succ y = succ (x + y)

x × zero = 0
x × succ y = x + x × y
