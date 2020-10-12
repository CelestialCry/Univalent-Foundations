{-# OPTIONS --without-K --exact-split --safe #-}

module TwinPrimes where

open import N-order public

isPrime : ℕ -> 𝒰₀ ̇
isPrime n = (n ≥ 2) × ((x y : ℕ) -> x ×̇ y ≡ n -> (x ≡ 1) + (x ≡ n))

twinPrimeConjecture : 𝒰₀ ̇
twinPrimeConjecture = (n : ℕ) -> Σ p :- ℕ , ((p ≥ n) × ((isPrime p) × isPrime (p +̇ 2)))