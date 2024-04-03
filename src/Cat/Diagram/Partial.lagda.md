<!--
```agda
open import Cat.Prelude

import Cat.Displayed.Instances.Subobjects as Sub
import Cat.Diagram.Pullback as Pb
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Diagram.Partial
```

<!--
```agda
  {o ℓ} (C : Precategory o ℓ)
  where

open Sub C
open Cat C
open Pb C
```
-->

# Partial map classifiers

```agda

record _⇁_ (A B : Ob) : Type (o ⊔ ℓ) where
  field
    sub : Subobject A
    map : Hom (sub .domain) B

  open Subobject sub renaming (map to mono) public

open _⇁_ 
```

```agda
record is-partial-map-classifier {B : Ob} (B⊥ : Ob) (incl : Hom B B⊥) : Type (o ⊔ ℓ) where
  field
    name   : ∀ {A} → A ⇁ B → Hom A B⊥
    names  : ∀ {A} → (f : A ⇁ B)
                   → is-pullback (f .mono) (name f) (f .map) incl

    unique : ∀ {A} → (f : A ⇁ B) → {n : Hom A B⊥}
                   → is-pullback (f .mono) n (f .map) incl
                   → n ≡ name f
    
record Partial-map-classifier (B : Ob) : Type (o ⊔ ℓ) where
  field
    B⊥      : Ob
    incl    : Hom B B⊥
    is-mono : is-monic incl
    is-pmc  : is-partial-map-classifier B⊥ incl

  open is-partial-map-classifier is-pmc

has-partial-map-classifiers : Type (o ⊔ ℓ)
has-partial-map-classifiers = ∀ x → Partial-map-classifier x
```
