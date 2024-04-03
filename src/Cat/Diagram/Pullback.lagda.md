<!--
```agda
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Pullback {ℓ ℓ'} (C : Precategory ℓ ℓ') where
```

# Pullbacks {defines=pullback}

<!--
```agda
open Cat.Reasoning C
private variable
  P' X Y Z : Ob
  h p₁' p₂' : Hom X Y
```
-->

A **pullback** $X \times_Z Y$ of $f : X \to Z$ and $g : Y \to Z$ is the
[[product]] of $f$ and $g$ in the category $\cC/Z$, the category of
objects fibred over $Z$. We note that the fibre of $X \times_Z Y$ over
some element $x$ of $Z$ is the product of the fibres of $f$ and $g$ over
$x$; Hence the pullback is also called the **fibred product**.

```agda
record is-pullback {P} (p₁ : Hom P X) (f : Hom X Z) (p₂ : Hom P Y) (g : Hom Y Z)
  : Type (ℓ ⊔ ℓ') where

  no-eta-equality
  field
    square   : f ∘ p₁ ≡ g ∘ p₂
```

The concrete incarnation of the abstract nonsense above is that a
pullback turns out to be a universal square like the one below. Since it
is a product, it comes equipped with projections $\pi_1$ and $\pi_2$
onto its factors; Since isn't merely a product of $X$ and $Y$, but
rather of $X$ and $Y$ considered as objects over $Z$ in a specified way,
overall square has to commute.

~~~{.quiver}
\[\begin{tikzcd}
  P && Y \\
  \\
  X && Z
  \arrow["g", from=1-3, to=3-3]
  \arrow["f"', from=3-1, to=3-3]
  \arrow["{\pi_1}"', from=1-1, to=3-1]
  \arrow["{\pi_2}", from=1-1, to=1-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
    universal : ∀ {P'} {p₁' : Hom P' X} {p₂' : Hom P' Y}
             → f ∘ p₁' ≡ g ∘ p₂' → Hom P' P
    p₁∘universal : {p : f ∘ p₁' ≡ g ∘ p₂'} → p₁ ∘ universal p ≡ p₁'
    p₂∘universal : {p : f ∘ p₁' ≡ g ∘ p₂'} → p₂ ∘ universal p ≡ p₂'

    unique : {p : f ∘ p₁' ≡ g ∘ p₂'} {lim' : Hom P' P}
           → p₁ ∘ lim' ≡ p₁'
           → p₂ ∘ lim' ≡ p₂'
           → lim' ≡ universal p

  unique₂
    : {p : f ∘ p₁' ≡ g ∘ p₂'} {lim' lim'' : Hom P' P}
    → p₁ ∘ lim' ≡ p₁' → p₂ ∘ lim' ≡ p₂'
    → p₁ ∘ lim'' ≡ p₁' → p₂ ∘ lim'' ≡ p₂'
    → lim' ≡ lim''
  unique₂ {p = o} p q r s = unique {p = o} p q ∙ sym (unique r s)
```

<!--
```agda
  pullback-univ
    : ∀ {O} → Hom O P ≃ (Σ (Hom O X) λ h → Σ (Hom O Y) λ h' → f ∘ h ≡ g ∘ h')
  pullback-univ .fst h = p₁ ∘ h , p₂ ∘ h , extendl square
  pullback-univ .snd = is-iso→is-equiv λ where
    .is-iso.inv (f , g , α) → universal α
    .is-iso.rinv x → Σ-pathp p₁∘universal $ Σ-prop-pathp (λ _ _ → hlevel 1) p₂∘universal
    .is-iso.linv x → sym (unique refl refl)
```
-->

By universal, we mean that any other "square" (here the second "square"
has corners $P'$, $X$, $Y$, $Z$ --- it's a bit bent) admits a unique
factorisation that passes through $P$; We can draw the whole situation
as in the diagram below. Note the little corner on $P$, indicating that
the square is a pullback.

~~~{.quiver}
\[\begin{tikzcd}
  {P'} \\
  & P && Y \\
  \\
  & X && Z
  \arrow["g", from=2-4, to=4-4]
  \arrow["f"', from=4-2, to=4-4]
  \arrow["{\pi_1}"', from=2-2, to=4-2]
  \arrow["{\pi_2}", from=2-2, to=2-4]
  \arrow["{\exists! }", dashed, from=1-1, to=2-2]
  \arrow["{p_2}", curve={height=-12pt}, from=1-1, to=2-4]
  \arrow["{p_1}", curve={height=12pt}, from=1-1, to=4-2]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=2-2, to=4-4]
\end{tikzcd}\]
~~~

We provide a convenient packaging of the pullback and the projection
maps:

```agda
record Pullback {X Y Z} (f : Hom X Z) (g : Hom Y Z) : Type (ℓ ⊔ ℓ') where
  no-eta-equality
  field
    {apex} : Ob
    p₁ : Hom apex X
    p₂ : Hom apex Y
    has-is-pb : is-pullback p₁ f p₂ g

  open is-pullback has-is-pb public
```

# Categories with all pullbacks

We also provide a helper module for working with categories that have all
pullbacks.

```agda
has-pullbacks : Type _
has-pullbacks = ∀ {A B X} (f : Hom A X) (g : Hom B X) → Pullback f g

module Pullbacks (all-pullbacks : has-pullbacks) where
  module pullback {x y z} (f : Hom x z) (g : Hom y z) =
    Pullback (all-pullbacks f g)

  Pb : ∀ {x y z} → Hom x z → Hom y z → Ob
  Pb = pullback.apex
```

## Stability {defines="pullback-stability pullback-stable"}

Pullbacks, in addition to their nature as limits, serve as the way of
"changing the base" of a family of objects: if we think of an arrow
$f : A \to B$ as encoding the data of a family over $B$ (think of the
special case where $A = \Sigma_{x : A} F(x)$, and $f = \pi_1$), then we
can think of pulling back $f$ along $g : X \to B$ as "the universal
solution to making $f$ a family over $X$, via $g$". One way of making
this intuition formal is through the [[fundamental fibration]] of a
category with pullbacks.

In that framing, there is a canonical choice for "the" pullback of an
arrow along another: We put the arrow $f$ we want to pullback on the
right side of the diagram, and the pullback is the right arrow. Using
the type `is-pullback`{.Agda} defined above, the arrow which results
from pulling back is adjacent _to the adjustment_: `is-pullback f⁺ g _ f`.
To help keep this straight, we define what it means for a class of
arrows to be **stable under pullback**: If `f` has a given property,
then so does `f⁺`, for any pullback of `f`.

```agda
is-pullback-stable
  : ∀ {ℓ'} → (∀ {a b} → Hom a b → Type ℓ') → Type _
is-pullback-stable P =
  ∀ {p A B X} (f : Hom A B) (g : Hom X B) {f⁺ : Hom p X} {p2}
  → P f → is-pullback f⁺ g p2 f → P f⁺
```

<!--
```agda
is-pullback-is-prop
  : ∀ {w x y z : Ob} {p1 : Hom w x} {f : Hom x z} {p2 : Hom w y} {g : Hom y z}
  → is-prop (is-pullback p1 f p2 g)
is-pullback-is-prop {w = W} {X} {Y} {Z} {p1} {f} {p2} {g} x y = p where
  module x = is-pullback x
  module y = is-pullback y
  open is-pullback

  lims
    : ∀ {P'} {p1' : Hom P' X} {p2' : Hom P' Y} (p : f ∘ p1' ≡ g ∘ p2')
    → x.universal p ≡ y.universal p
  lims p = y.unique x.p₁∘universal x.p₂∘universal

  p : x ≡ y
  p i .square = is-prop→pathp (λ i → Hom-set W Z (f ∘ p1) (g ∘ p2))
    x.square y.square i
  p i .universal p = lims p i
  p i .p₁∘universal {p = p} = is-prop→pathp (λ i → Hom-set _ X (p1 ∘ lims p i) _)
    x.p₁∘universal y.p₁∘universal i
  p i .p₂∘universal {p = p} = is-prop→pathp (λ i → Hom-set _ _ (p2 ∘ lims p i) _)
    x.p₂∘universal y.p₂∘universal i
  p i .unique {P' = P'} {p₁' = p₁'} {p₂' = p₂'} {p = p'} {lim' = lim'} =
    is-prop→pathp
      (λ i   → Π-is-hlevel {A = Hom P' W} 1
       λ lim → Π-is-hlevel {A = p1 ∘ lim ≡ p₁'} 1
       λ p   → Π-is-hlevel {A = p2 ∘ lim ≡ p₂'} 1
       λ q   → Hom-set P' W lim (lims p' i))
      (λ lim → x.unique {lim' = lim})
      (λ lim → y.unique {lim' = lim})
      i lim'

instance
  H-Level-is-pullback
    : ∀ {w x y z : Ob} {p1 : Hom w x} {f : Hom x z} {p2 : Hom w y} {g : Hom y z} {n}
    → H-Level (is-pullback p1 f p2 g) (suc n)
  H-Level-is-pullback = prop-instance is-pullback-is-prop

```
-->
