---
description: We establish that left adjoints preserve colimits.
---
<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Colimit.Finite
open import Cat.Functor.Adjoint.Kan
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Initial
open import Cat.Functor.Kan.Base
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
```
-->

```agda
module Cat.Functor.Adjoint.Cocontinuous where
```

<!--
```agda
module _
    {o o' ℓ ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    {L : Functor C D} {R : Functor D C}
    (L⊣R : L ⊣ R)
  where
  private
    module L = Func L
    module R = Func R
    module C = Precategory C
    module D = Precategory D
    module adj = _⊣_ L⊣R
    open _=>_
```
-->

# Continuity of adjoints

We prove that every functor $L : \cC \to \cD$ admitting a [[right
adjoint]] $L \dashv R$ preserves every co-limit which exists in $\cD$.
We then instantiate this theorem to the "canonical" shapes of limit:
[[initial objects]], [[coproducts]], [[pushout]] and [[coequalisers]].

This follows directly from the fact that [adjoints preserve Kan
extensions].

[adjoints preserve Kan extensions]: Cat.Functor.Adjoint.Kan.html


```agda
  right-adjoint-is-continuous
    : ∀ {os ℓs} → is-continuous os ℓs R
  right-adjoint-is-continuous lim =
    right-adjoint→right-extension lim L⊣R

  left-adjoint-is-cocontinuous
    : ∀ {os ℓs} → is-cocontinuous os ℓs L
  left-adjoint-is-cocontinuous colim =
    left-adjoint→left-extension colim L⊣R

  module _ {od ℓd} {J : Precategory od ℓd} where
    right-adjoint-limit : ∀ {F : Functor J D} → Limit F → Limit (R F∘ F)
    right-adjoint-limit lim =
      to-limit (right-adjoint-is-continuous (Limit.has-limit lim))

    left-adjoint-colimit : ∀ {F : Functor J C} → Colimit F → Colimit (L F∘ F)
    left-adjoint-colimit colim =
      to-colimit (left-adjoint-is-cocontinuous (Colimit.has-colimit colim))
```

## Concrete colimits

We now show that adjoint functors preserve "concrete limits". We could
show this using general abstract nonsense, but we can avoid transports
if we do it by hand.

<!--
```agda
  open import Cat.Diagram.Coequaliser
  open import Cat.Diagram.Pushout
  open import Cat.Diagram.Coproduct
```
-->

```agda
  left-adjoint→is-coproduct : ∀ {x a b} {p1 : C.Hom a x} {p2 : C.Hom b x}
    → is-coproduct C p1 p2
    → is-coproduct D (L.₁ p1) (L.₁ p2)
  left-adjoint→is-coproduct {x = x} {a} {b} {p1} {p2} c-coprod = d-coprod where
    open is-coproduct

    d-coprod : is-coproduct D (L.₁ p1) (L.₁ p2)
    d-coprod .[_,_] f g 
      = R-adjunct L⊣R (c-coprod .[_,_] (L-adjunct L⊣R f) (L-adjunct L⊣R g))
    d-coprod .in₀∘factor 
      = L.pullr (c-coprod .in₀∘factor) ∙ R-L-adjunct L⊣R _
    d-coprod .in₁∘factor 
      = L.pullr (c-coprod .in₁∘factor) ∙ R-L-adjunct L⊣R _
    d-coprod .unique other p q =
      sym (R-L-adjunct L⊣R other)
      ∙ ap (R-adjunct L⊣R)
           (c-coprod .unique _ (L-adjunct-ap L⊣R p) (L-adjunct-ap L⊣R q))
    

  left-adjoint→is-pushout
    : ∀ {p x y z}
    → {p1 : C.Hom p x} {f : C.Hom x z} {p2 : C.Hom p y} {g : C.Hom y z}
    → is-pushout C p1 f p2 g
    → is-pushout D (L.₁ p1) (L.₁ f) (L.₁ p2) (L.₁ g)
  left-adjoint→is-pushout {p1 = p1} {f} {p2} {g} c-po = d-po where
    open is-pushout

    d-po : is-pushout D (L.₁ p1) (L.₁ f) (L.₁ p2) (L.₁ g)
    d-po .square = L.weave (c-po .square)
    d-po .universal sq = 
      R-adjunct L⊣R (c-po .universal (L-adjunct-square L⊣R sq))
    d-po .i₁∘universal =
      L.pullr (c-po .i₁∘universal) ∙ R-L-adjunct L⊣R _
    d-po .i₂∘universal = 
      L.pullr (c-po .i₂∘universal) ∙ R-L-adjunct L⊣R _
    d-po .unique {_} {_} {_} {_} {other} p q =
      sym (R-L-adjunct L⊣R other)
      ∙ ap (R-adjunct L⊣R)
           (c-po .unique (L-adjunct-ap L⊣R p) (L-adjunct-ap L⊣R q)) 

  left-adjoint→is-coequaliser
    : ∀ {e a b} {f g : C.Hom a b} {equ : C.Hom b e}
    → is-coequaliser C f g equ
    → is-coequaliser D (L.₁ f) (L.₁ g) (L.₁ equ)
  left-adjoint→is-coequaliser {f = f} {g} {coequ} c-coequal = d-coequal where
    open is-coequaliser

    d-coequal : is-coequaliser D (L.₁ f) (L.₁ g) (L.₁ coequ)
    d-coequal .coequal = L.weave (c-coequal .coequal)
    d-coequal .universal sq =
      R-adjunct L⊣R (c-coequal .universal (L-adjunct-square L⊣R sq))
    d-coequal .factors = 
      L.pullr (c-coequal .factors) ∙ R-L-adjunct L⊣R _ 
    d-coequal .unique p = 
      sym (R-L-adjunct L⊣R _)
      ∙ ap (R-adjunct L⊣R)
           (c-coequal .unique (L-adjunct-ap L⊣R p))

```