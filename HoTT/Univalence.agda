{-# OPTIONS --without-K --exact-split --safe #-}

module Univalence where

open import MLTT public
open import Logic public

{-
We want to define what it means for a type to be contractible.
We say that a type is contractible if it is a singleton type.
These types are also called -2-types.
-}
isCenter : (X : 𝒰 ̇) -> X -> 𝒰 ̇
isCenter X c = (x : X) -> c ≡ x

isSingleton : 𝒰 ̇ -> 𝒰 ̇
isSingleton X = Σ c :- X , isCenter X c
-- We say that c is the center of contraction for the singleton.

𝟙-isSingleton : isSingleton 𝟙
𝟙-isSingleton = * , 𝟙-induction (λ y -> * ≡ y) (refl *)
-- We will see that a type is a singleton if and only if it is equivalent to 𝟙

center : (X : 𝒰 ̇) -> isSingleton X -> X
center _ (c , _) = c

centrality : (X : 𝒰 ̇) (i : isSingleton X) (x : X) -> center X i ≡ x
centrality X (c , φ) = φ
-- We define fancy name for the two prjections of isSingleton to easier see what is going on

{-
The next notion of type are types with at most one element, i.e. any two elements are identified.
We say a type is a subsingleton if this is satisfied.
These types are also called -1-typse.
-}
isSubsingleton : 𝒰 ̇ -> 𝒰 ̇
isSubsingleton X = (x y : X) -> x ≡ y

𝟘-isSubsingleton : isSubsingleton 𝟘
𝟘-isSubsingleton x y = 𝟘!-induction (λ z -> x ≡ z) y

singletonsAreSubsingletons : (X : 𝒰 ̇) -> isSingleton X -> isSubsingleton X
singletonsAreSubsingletons X (c , φ) x y = ((φ x) ⁻¹) · (φ y)

𝟙-isSubsingleton : isSubsingleton 𝟙
𝟙-isSubsingleton = singletonsAreSubsingletons 𝟙 (𝟙-isSingleton)

pointedSubsingletonsAreSingletons : (X : 𝒰 ̇) -> X -> isSubsingleton X -> isSingleton X
pointedSubsingletonsAreSingletons X x f = x , f x

singletonIffPointedAndSubsingleton : {X : 𝒰 ̇} -> (isSingleton X) ⇔ (X × isSubsingleton X)
singletonIffPointedAndSubsingleton {𝒰} {X} = ((λ p -> (center X p , singletonsAreSubsingletons X p))) , λ (x , p) -> pointedSubsingletonsAreSingletons X x p

{-
We use the terminology subsingleton as -1-types acts as a subtype of a -2-type.
It follows that a type X is a subsingleton if and only if the map X -> 𝟙 is an embedding.
Under univalent excluded middle, the empty type 𝟘 and the singleton type 𝟙 are the only subsingletons, up to equivalence, or up to identity if we further assume univalence.
Subsingletons are also called propositions or truth values:
-}

isProp isTruthValue : 𝒰 ̇ -> 𝒰 ̇
isProp = isSubsingleton
isTruthValue = isSubsingleton
-- These are now simply synonyms for subsingletons

{-
The terminology is-subsingleton is more mathematical and avoids the clash with the slogan propositions as types, which is based on the interpretation of mathematical statements as arbitrary types, rather than just subsingletons. In these notes we prefer the terminology subsingleton, but we occasionally use the terminologies proposition and truth value. When we wish to emphasize this notion of proposition adopted in univalent mathematics, as opposed to “propositions as (arbitrary) types”, we may say univalent proposition.

In some formal systems, for example set theory based on first-order logic, one can tell that something is a proposition by looking at its syntactical form, e.g. “there are infinitely many prime numbers” is a proposition, by construction, in such a theory.

In univalent mathematics, however, propositions are mathematical, rather than meta-mathematical, objects, and the fact that a type turns out to be a proposition requires mathematical proof. Moreover, such a proof may be subtle and not immediate and require significant preparation. An example is the proof that the univalence axiom is a proposition, which relies on the fact that univalence implies function extensionality, which in turn implies that the statement that a map is an equivalence is a proposition. Another non-trivial example, which again relies on univalence or at least function extensionality, is the proof that the statement that a type X is a proposition is itself a proposition, which can be written as is-prop (is-prop X).

Singletons and subsingletons are also called -2-groupoids and -1-groupoids respectively.
-}

{-
Sets, 0-types or 0-groupoids is a nice type.
A type is a set if there is at most one way for two elements to be equal.
-}

isSet : 𝒰 ̇ -> 𝒰 ̇
isSet X = (x y : X) -> isSubsingleton (x ≡ y)
-- Now we are closing in on what is happening inside the field of univalent mathematics, but we're not quite there yet (as the univalence axiom haven't been introduced)

-- The law of univalent excluded middle
EM EM' : ∀ 𝒰 -> 𝒰 ⁺  ̇
EM 𝒰 = (X : 𝒰 ̇) -> isSubsingleton X -> X + ¬ X
EM' 𝒰 = (X : 𝒰 ̇) -> isSubsingleton X -> isSingleton X + is-empty X

EM-gives-EM' : EM 𝒰 → EM' 𝒰
EM-gives-EM' em X s = γ (em X s)
 where
  γ : X + ¬ X → isSingleton X + is-empty X
  γ (inl x) = inl (pointedSubsingletonsAreSingletons X x s)
  γ (inr x) = inr x


EM'-gives-EM : EM' 𝒰 → EM 𝒰
EM'-gives-EM em' X s = γ (em' X s)
 where
  γ : isSingleton X + is-empty X → X + ¬ X
  γ (inl i) = inl (center X i)
  γ (inr x) = inr x
-- This shows that excluded middle under univalence says that either X is 𝟙 or X is 𝟘. Note that we cannot in general prove that a -1-type follows LEM.

module magmas where
  -- As usual a magma is a type, which is a set together with a binary operator
  Magma : (𝒰 : Universe) -> 𝒰 ⁺ ̇
  Magma 𝒰 = Σ X :- 𝒰 ̇ , ((isSet X) × (X -> X -> X))
  -- The type Magma is a collection of all magmas in 𝒰. Thus if X : 𝒰 is a magma, (X, _ , _) : Magma 𝒰.

  -- We define to easier see what is going on:
  ⟨_⟩ : Magma 𝒰 -> 𝒰 ̇
  ⟨ X , (_ , _) ⟩ = X

  magmaIsSet : (M : Magma 𝒰) -> isSet ⟨ M ⟩
  magmaIsSet (_ , (i , _)) = i

  magmaOperation : (M : Magma 𝒰) -> ⟨ M ⟩ -> ⟨ M ⟩ -> ⟨ M ⟩
  magmaOperation (_ , (_ , _<>_)) = _<>_

  syntax magmaOperation M x y = x < M > y

  private
    -- Looking at homomorphisms and isomorphisms of magmas
    isMagmaHom : (M N : Magma 𝒰) -> (⟨ M ⟩ -> ⟨ N ⟩) -> 𝒰 ̇
    isMagmaHom M N f = (x y : ⟨ M ⟩) -> f (x < M > y) ≡ f x < N > f y

    idIsMagmaHom : (M : Magma 𝒰) -> isMagmaHom M M id
    idIsMagmaHom M x y = refl (x < M > y)

    isMagmaIso : (M N : Magma 𝒰) -> (⟨ M ⟩ -> ⟨ N ⟩) -> 𝒰 ̇
    isMagmaIso M N f = (isMagmaHom M N f) × (Σ g :- (⟨ N ⟩ -> ⟨ M ⟩) , ((isMagmaHom N M g) × (((g ∘ f) ~ 𝒾𝒹 ⟨ M ⟩) × ((f ∘ g) ~ 𝒾𝒹 ⟨ N ⟩))))

    idIsMagmaIso : (M : Magma 𝒰) -> isMagmaIso M M (𝒾𝒹 ⟨ M ⟩)
    idIsMagmaIso M = idIsMagmaHom M , (𝒾𝒹 ⟨ M ⟩ , (idIsMagmaHom M , (refl , refl)))

    -- We can transport identifications of magmas to isomorphisms of magmas
    Id→Iso : {M N : Magma 𝒰} -> M ≡ N -> ⟨ M ⟩ -> ⟨ N ⟩
    Id→Iso eq = transport ⟨_⟩ eq

    Id→IsoIsIso : {M N : Magma 𝒰} (p : M ≡ N) -> isMagmaIso M N (Id→Iso p)
    Id→IsoIsIso (refl M) = idIsMagmaIso M

    _≅ₘ_ : Magma 𝒰 -> Magma 𝒰 -> 𝒰 ̇
    M ≅ₘ N = Σ f :- (⟨ M ⟩ -> ⟨ N ⟩), isMagmaIso M N f

module monoids where
  -- Defining monoids
  
  leftNeutral : {X : 𝒰 ̇} -> X -> (X -> X -> X) -> 𝒰 ̇
  leftNeutral e _<>_ = ∀ x -> e <> x ≡ x

  rightNeutral : {X : 𝒰 ̇} -> X -> (X -> X -> X) -> 𝒰 ̇
  rightNeutral e _<>_ = ∀ x -> x <> e ≡ x

  associative : {X : 𝒰 ̇} -> (X -> X -> X) -> 𝒰 ̇
  associative _<>_ = ∀ x y z -> (x <> y) <> z ≡ x <> (y <> z)

  -- Definition of all monoids
  Monoid : (𝒰 : Universe) -> 𝒰 ⁺  ̇
  Monoid 𝒰 = 
    Σ X :- 𝒰 ̇ , (
      isSet X × (
        Σ _<>_ :- (X -> X -> X) , (
          Σ e :- X , (
            (leftNeutral e _<>_) × (rightNeutral e _<>_) × (associative _<>_)
            )   
          )
        )
      )