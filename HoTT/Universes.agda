{-# OPTIONS --without-K --exact-split --safe #-}

module Universes where

open import Agda.Primitive public
 renaming (
            Level to Universe -- We speak of universes rather than of levels.
          ; lzero to 𝒰₀       -- Our first universe is called 𝒰₀
          ; lsuc to _⁺        -- The universe after 𝒰 is 𝒰 ⁺
          ; Setω to 𝒰ω        -- There is a universe 𝒰ω strictly above 𝒰₀, 𝒰₁, ⋯ , 𝒰ₙ, ⋯
          )
 using    (_⊔_)               -- Least upper bound of two universes, e.g. 𝒰₀ ⊔ 𝒰₁ is 𝒰₁

Type = λ ℓ → Set ℓ

_̇   : (𝒰 : Universe) → Type (𝒰 ⁺)

𝒰 ̇  = Type 𝒰

𝒰₁ = 𝒰₀ ⁺
𝒰₂ = 𝒰₁ ⁺
𝒰₃ = 𝒰₂ ⁺

_⁺⁺ : Universe → Universe
𝒰 ⁺⁺ = 𝒰 ⁺ ⁺

universe-of : {𝒰 : Universe} (X : 𝒰 ̇ ) → Universe
universe-of {𝒰} X = 𝒰

infix  1 _̇