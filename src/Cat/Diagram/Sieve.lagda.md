<!--
```agda
{-# OPTIONS -vtactic.hlevel:30 #-}
open import Cat.Instances.Functor
open import Cat.Functor.Hom
open import Cat.Prelude

open import Data.Power

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Sieve where
```

<!--
```agda
module _ {o κ : _} (C : Precategory o κ) (c : ⌞ C ⌟) where
  private module C = Precategory C
```
-->

# Sieves

Given a category $\cC$, a **sieve** on an object $c$ Is a subset of
the maps $a \to c$ closed under composition: If $f \in S$, then $(f
\circ g) \in S$. The data of a sieve on $c$ corresponds to the data of a
subobject of $\yo(c)$, considered as an object of $\psh(\cC)$.

Here, the subset is represented as the function `arrows`{.agda}, which,
given an arrow $f : a \to c$ (and its domain), yields a proposition
representing inclusion in the subset.

```agda
  record Sieve : Type (o ⊔ κ) where
    field
      arrows : ∀ {y} → ℙ (C.Hom y c)
      closed : ∀ {y z f} (g : C.Hom y z) → f ∈ arrows → (f C.∘ g) ∈ arrows
  open Sieve public
```

<!--
```agda
instance
  Membership-Sieve : ∀ {o ℓ} {C : Precategory o ℓ} {c d} → Membership (C .Precategory.Hom d c) (Sieve C c) _
  Membership-Sieve = record { _∈_ = λ x S → x ∈ S .Sieve.arrows }
```
-->

The `maximal`{.agda} sieve on an object is the collection of _all_ maps
$a \to c$; It represents the identity map $\yo(c) \to \yo(c)$ as a
subfunctor. A [$\kappa$-small] family of sieves can be intersected (the
underlying predicate is the "$\kappa$-ary conjunction" $\Pi$ --- the
universal quantifier), and this represents a wide pullback of
subobjects.

[$\kappa$-small]: 1Lab.intro.html#universes-and-size-issues

<!--
```agda
module _ {o κ : _} (C : Precategory o κ) (c : ⌞ C ⌟) where
  private
    module C   = Cat.Reasoning C
    module PSh = Cat.Reasoning (PSh κ C)

  open PSh._↪_
  open _=>_
  open Functor
```
-->

```agda
  maximal' : Sieve C c
  maximal' .arrows x = ⊤Ω
  maximal' .closed g x = tt

  intersect : ∀ {I : Type κ} (F : I → Sieve C c) → Sieve C c
  intersect {I = I} F .arrows h = elΩ ((x : I) → h ∈ F x)
  intersect {I = I} F .closed g x = inc λ i → F i .closed g (out! x i)
```

## Representing subfunctors

Let $S$ be a sieve on $\cC$. We show that it determines a presheaf
$S'$, and that this presheaf admits a monic natural transformation $S'
\mono \yo(c)$. The functor determined by a sieve $S$ sends each object
$d$ to the set of arrows $d \xto{f} c$ s.t. $f \in S$; The functorial
action is given by composition, as with the $\hom$ functor.

```agda
  to-presheaf : Sieve C c → PSh.Ob
  to-presheaf sieve .F₀ d = el! (Σ[ f ∈ C.Hom d c ] (f ∈ sieve))
  to-presheaf sieve .F₁ f (g , s) = g C.∘ f , sieve .closed _ s
```

<!--
```agda
  to-presheaf sieve .F-id    = funext λ _ → Σ-prop-path! (C.idr _)
  to-presheaf sieve .F-∘ f g = funext λ _ → Σ-prop-path! (C.assoc _ _ _)
```
-->

That this functor is a subobject of $\yo$ follows straightforwardly: The
injection map $S' \mono \yo(c)$ is given by projecting out the first
component, which is an embedding (since "being in a sieve" is a
proposition). Since natural transformations are monic if they are
componentwise monic, and embeddings are monic, the result follows.

```agda
  to-presheaf↪よ : {S : Sieve C c} → to-presheaf S PSh.↪ よ₀ C c
  to-presheaf↪よ {S} .mor .η x (f , _) = f
  to-presheaf↪よ {S} .mor .is-natural x y f = refl
  to-presheaf↪よ {S} .monic g h path = ext λ i x → Σ-prop-path! (unext path i x)
```
