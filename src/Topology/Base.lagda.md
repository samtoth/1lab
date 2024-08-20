 # Topology



```agda
open import Cat.Prelude
open import Cat.Functor.Subcategory
open import Cat.Functor.Adjoint
open import Cat.Functor.Adjoint.Hom
open import Cat.Displayed.Base
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Total.Op
open import Cat.Displayed.Instances.Subobjects
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Univalence.Thin
open import Cat.Instances.Shape.Interval 
open import Cat.Displayed.Cartesian
open import Cat.Functor.Properties
open import Order.Frame
open import Order.Base
open import Order.Instances.Pointwise.Diagrams 
open import Order.Cat
open import Order.Frame
open import Order.Diagram.Meet
open import Order.Diagram.Top
open import Order.Subposet
open import Data.Power hiding (_∩_;_∪_)
open import Data.Bool

import Cat.Displayed.Reasoning
import Cat.Reasoning
import Cat.Morphism as Cm

module Topology.Base {ℓ} where
    
private module Sets = Precategory (Sets ℓ)
module ℙ {ℓ} (x : Type ℓ)  = is-frame (Power-frame x .snd) 
```

 Topology is the study of topological spaces

 ## topological Space

```
-- Power-frames : Functor (Sets ℓ) (Loc ℓ ℓ)
-- Power-frames .Functor.F₀ x = Power-frame ⌞ x ⌟
-- Power-frames .Functor.F₁ f = sub-hom 
--     (record { hom = λ x i → x (f i) ; pres-≤ = λ g y p → g (f y) p })
--     (record { ∩-≤ = λ _ _ _ x → x ; top-≤ = _ ; ⋃-≤ = λ _ _ x → x })
-- Power-frames .Functor.F-id = trivial!
-- Power-frames .Functor.F-∘ _ _ = trivial!

-- module 𝓟 = Functor Power-frames

record Topology (S : Type ℓ) : Type (lsuc ℓ) where
    open ℙ S
    field
        is-open   : ℙ S → Ω
    is-open' : ℙ S → Type
    is-open' x = ⌞ is-open x ⌟
    field
        top-open   : is-open' top
        meet-open  : ∀ {U V} → is-open' U → is-open' V → is-open' (U ∩ V)
        join-open  : ∀ {I : Type ℓ} → (fam : I → ℙ ⌞ S ⌟) 
                     → (∀ i → is-open' (fam i))
                     → is-open' (⋃ fam)

    bot-open : is-open' bot
    bot-open = subst is-open' empty-join-bot empty-join-open where
        empty-join-open : is-open' (λ x → ∃Ω (Lift ℓ ⊥) (λ ()))
        empty-join-open = join-open {Lift _ ⊥} (λ ()) (λ ())
 
        empty-join-bot : (λ _ → ∃Ω (Lift ℓ ⊥) (λ ())) ≡ bot
        empty-join-bot = ext (λ s → Ω-ua (rec! (λ ())) (¡ {λ i → el ⌞ ∃Ω (Lift ℓ ⊥) (λ ()) ⌟ (hlevel 1)} s))
```

Two topologies are equal when there set of opens are equal

```agda
Topology-path : ∀ {X} {x y : Topology X} → (x .Topology.is-open ≡ y .Topology.is-open) → x ≡ y
Topology-path {X} {x} {y} p i .Topology.is-open = p i
Topology-path {X} {x} {y} p i .Topology.top-open = pa i where
    pa : PathP (λ i → ∣ p i (ℙ.top _) ∣) (Topology.top-open x) (Topology.top-open y)
    pa = prop!
Topology-path {X} {x} {y} p i .Topology.meet-open {U} {V} = pa i where
    pa : PathP (λ i → ∣ p i U ∣ → ∣ p i V ∣ → ∣ p i ((_ ℙ.∩ U) V) ∣) (Topology.meet-open x) (Topology.meet-open y)
    pa = prop!
Topology-path {X} {x} {y} p i .Topology.join-open {I = J} = pa i where
    pa : PathP (λ i → (fam : J → ℙ _) → ((j : J) → ∣ p i (fam j) ∣) → ∣ p i (ℙ.⋃ _ fam) ∣)
            (Topology.join-open x) (Topology.join-open y)
    pa = prop!

instance
    Extensional-topology : ∀ {X} → Extensional (Topology X) ℓ
    Extensional-topology = injection→extensional (hlevel 2) Topology-path Extensional-Π


```



A map between $f$ between sets $X$ and $Y$ with topological structures $T$ and $U$
respectively is said to be a continuous map of topological spaces when
the preimage of any open set in Y is an open set in X. This is a *property* not 
a structure on the map f.

```agda

is-continuous : ∀ {X Y : Type ℓ}  (f : X → Y) (T : Topology X) (U : Topology Y) → Type ℓ
is-continuous {X} {Y} f T U = let module T = Topology {X} T
                                  module U = Topology {Y} U
                              in  (∀ (A : ℙ ⌞ Y ⌟) → U.is-open' A → T.is-open' (A ⊙ f)) 

is-continuous-is-prop : ∀ {X Y : Type ℓ} (f : X → Y) (T : Topology X) (U : Topology Y)
                        → is-prop (is-continuous f T U)
is-continuous-is-prop f T U = hlevel 1
```

This data assembles into a displayed category over Sets, 


```agda
Top-structure : Thin-structure ℓ Topology
Top-structure .is-hom f x y = el! (is-continuous f x y)
Top-structure .id-is-hom _ x = x
Top-structure .∘-is-hom f g fc gc A o = gc (A ⊙ f) (fc A o)
Top-structure .id-hom-unique f g = ext (λ A → Ω-ua (g A) (f A))

Tops : Precategory (lsuc ℓ) ℓ
Tops = Structured-objects Top-structure

Tops-over : Displayed (Sets ℓ) (lsuc ℓ) ℓ
Tops-over = Thin-structure-over Top-structure

Tops-is-category : is-category Tops
Tops-is-category = Structured-objects-is-category Top-structure

Tops↪Set : Functor Tops (Sets ℓ)
Tops↪Set = Forget-structure Top-structure

Tops↪Sets-is-faithful : is-faithful (Tops↪Set)
Tops↪Sets-is-faithful = Structured-hom-path Top-structure

``` 

Because being continuous is a property on homs, the fibres of `Top`.{agda}
are all in fact posets. When given two topologies $X$ and $Y$ on some set, you have
$X \leq Y$, you say that $X$ is coarser than $Y$ (or is it the other way round)

```agda
Tops-on : (X : Type ℓ) → Poset (lsuc ℓ) ℓ
Tops-on X = (Structured-fibre Top-structure X) ^opp
```