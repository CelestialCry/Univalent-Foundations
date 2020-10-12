{-# OPTIONS --without-K --exact-split --safe #-}

module Logic where

open import MLTT public

¬¬ ¬¬¬ : 𝒰 ̇ -> 𝒰 ̇
¬¬ A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)

-- Double negations
dni : {A : 𝒰 ̇} -> A -> ¬¬ A
dni a u = u a

contrapositive : {A : 𝒰 ̇} {B : 𝒱 ̇} -> (A -> B) -> (¬ B -> ¬ A)
contrapositive f v a = v (f a)

-- trippel negation imply one negation
tno : {A : 𝒰 ̇} -> ¬¬¬ A -> ¬ A
tno = contrapositive (dni)

-- One possible definition of implication
_⇔_ : 𝒰 ̇ -> 𝒱 ̇ -> 𝒰 ⊔ 𝒱 ̇
X ⇔ Y = (X -> Y) × (Y -> X)

lr-implication : {X : 𝒰 ̇} {Y : 𝒱 ̇} -> (X ⇔ Y) -> X -> Y
lr-implication = pr₁

rl-implication : {X : 𝒰 ̇} {Y : 𝒱 ̇} -> (X ⇔ Y) -> Y -> X
rl-implication = pr₂

-- room for a tangent here
𝟙-isNot-𝟘 : 𝟙 ≢ 𝟘 -- 𝟙 ≡ 𝟘 -> 𝟘
𝟙-isNot-𝟘 p = Id→Fun p *

₁-isNot-₀ : ₁ ≢ ₀
₁-isNot-₀ p = 𝟙-isNot-𝟘 q
    where
        f : 𝟚 -> 𝒰₀ ̇
        f ₀ = 𝟘
        f ₁ = 𝟙

        q : 𝟙 ≡ 𝟘
        q = ap f p

𝟚-hasDecidableEq : hasDecidableEq 𝟚
𝟚-hasDecidableEq (inl *) (inl *) = inl (refl (inl *))
𝟚-hasDecidableEq (inl *) (inr *) = inr (≢-sym ₁-isNot-₀)
𝟚-hasDecidableEq (inr *) (inl *) = inr (₁-isNot-₀)
𝟚-hasDecidableEq (inr *) (inr *) = inl (refl (inr *))

notZeroIsOne : (x : 𝟚) -> x ≢ ₀ -> x ≡ ₁
notZeroIsOne ₀ p = !𝟘 (₀ ≡ ₁) (p (refl ₀))
notZeroIsOne ₁ p = refl ₁

-- coproduct gives inequalites
copNeq : {X : 𝒰 ̇} {Y : 𝒱 ̇} {x : X} {y : Y} -> (inl x) ≢ (inr y)
copNeq {𝒰} {𝒱} {X} {Y} p = 𝟙-isNot-𝟘 q
    where
        f : X + Y -> 𝒰₀ ̇
        f (inl x) = 𝟙
        f (inr y) = 𝟘

        q : 𝟙 ≡ 𝟘
        q = ap f p