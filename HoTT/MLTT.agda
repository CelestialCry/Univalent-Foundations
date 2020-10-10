{-# OPTIONS --without-K --exact-split --safe #-}

module MLTT where

open import Universes public

variable
    𝒰 𝒱 𝒲 𝒯 : Universe

data 𝟙 : 𝓤₀ ̇ where
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