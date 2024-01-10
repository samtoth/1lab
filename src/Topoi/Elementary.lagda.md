<!--
```agda
open import Algebra.Prelude hiding (∫)

open import Cat.Functor.Equivalence.Complete
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Adjoint.Reflective
open import Cat.Instances.Sets.Cocomplete
open import Cat.Instances.Functor.Limits
open import Cat.Instances.Slice.Presheaf
open import Cat.CartesianClosed.Locally
open import Cat.Functor.Adjoint.Compose
open import Cat.Functor.Adjoint.Monadic
open import Cat.Instances.Sets.Complete
open import Cat.Functor.Adjoint.Monad
open import Cat.Functor.Hom.Coyoneda
open import Cat.Functor.Equivalence
-- open import Cat.Diagram.Everything
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Product
open import Cat.Diagram.Terminal
open import Cat.Diagram.Exponential
open import Cat.Diagram.Partial
open import Cat.Diagram.Power
open import Cat.Diagram.Subobject
import Cat.Diagram.Congruence as Cong
import Cat.Displayed.Instances.Subobjects as Sub
open import Cat.Functor.Properties
open import Cat.Instances.Elements
open import Cat.Functor.Pullback
open import Cat.Instances.Slice
open import Cat.Instances.Lift
open import Cat.Functor.Slice

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning
```
-->

```agda
module Topoi.Elementary where
```

<!--
```agda
open _=>_
```
-->

# Elementary topoi

```agda
record Topos {o} {κ} (𝓔 : Precategory o κ) : Type (lsuc (o ⊔ κ)) where
    field has-is-lex : Finitely-complete 𝓔
    open Finitely-complete has-is-lex public hiding (_⊗₀_)

    field cartesian  : Cartesian-closed 𝓔 products terminal
    field has-subobject-classifier : Subobject-classifier 𝓔 terminal


    open Binary-products 𝓔 products public
    open Cartesian-closed cartesian public hiding (unique₂)
    open Subobject-classifier has-subobject-classifier public
``` 

# Enough monos

```agda
module _ {o ℓ} {𝓔 : Precategory o ℓ} (E : Topos 𝓔) where
  private
    module E = Cat.Reasoning 𝓔
    module T = Topos E
  

  open Sub 𝓔
  open Cong (T.has-is-lex)
  open Topos
  open Functor
  open Terminal T.terminal

  Ω^_ : E.Ob → E.Ob
  Ω^ x = T.Exp.B^A x T.Ω

  singleton : ∀ {x} → E.Hom x (Ω^ x)
  singleton {x} = T.ƛ (T.generic .is-generic-subobject.name Δ) where
    Δ : Subobject (x T.⊗₀ x)
    Δ .Sub.domain = x
    Δ .Sub.map = diagonal
    Δ .Sub.monic = diagonal-is-monic

  singleton-is-monic : ∀ {x} → E.is-monic (singleton {x})
  singleton-is-monic = {!   !}

  subsingleton : ∀ {x} → Subobject (Ω^ x)
  subsingleton = record { map = singleton ; monic = singleton-is-monic }

  Topos-power-objects : has-power-objects 𝓔 T.has-is-lex
  Topos-power-objects x = pos where
    open Power-object

    pos : Power-object 𝓔 _ x
    pos .PA = Ω^ x
    pos .∋ = record { map = singleton T.⊗₁ E.id ; monic = {!   !} }
    pos .is-power = {!   !}
  
  Topos-partials : has-partial-map-classifiers 𝓔
  Topos-partials x = clas where
    open Partial-map-classifier
    
    clas : Partial-map-classifier 𝓔 x
    clas .B⊥ = {!   !}
    clas .incl = {!   !}
    clas .is-mono = {!   !}
    clas .is-pmc = {!   !}

```

# Relation to Grothendieck topoi

Every Grothendeik topoi is also an elementary topos (note the converse is not true).
There are many interesting examples of Elementary topoi that are not Grothendeik topoi

```agda
import Topoi.Base as G
module _ {o} κ (𝓒 : Precategory o κ) (𝓣 : G.Topos κ 𝓒) where
  private
    module T = G.Topos 𝓣
    module C = Cat.Reasoning 𝓒

  open Topos

  Grothendeik→Elementary : Topos 𝓒
  Grothendeik→Elementary .has-is-lex = is-complete→finitely 𝓒 (G.Topos-is-complete 𝓣)
  Grothendeik→Elementary .cartesian = {!   !}
  Grothendeik→Elementary .has-subobject-classifier = {!   !}

```

# Slicing Topoi
```agda
module _ {o ℓ} {𝓔 : Precategory o ℓ} (E : Topos 𝓔) (X : Precategory.Ob 𝓔) where
  private
    module E = Cat.Reasoning 𝓔
    module Eo = Cat.Reasoning (Slice 𝓔 X)
    module T = Topos E
  

  open Topos
  open Functor
  open Terminal T.terminal

  private
    module EoC = Finitely-complete {C = Slice 𝓔 X}
                 (Slice-lex (T.has-is-lex .Finitely-complete.pullbacks))
        
  sliceTer : Functor 𝓔 (Slice 𝓔 top)
  sliceTer = {!   !}

  X* : Functor 𝓔 (Slice 𝓔 X) 
  X* = Base-change T.pullbacks ! F∘ sliceTer

  Slice-closed : Cartesian-closed (Slice 𝓔 X) EoC.products EoC.terminal
  Slice-closed = {!   !}

  Slice-subobject-classifier : Subobject-classifier (Slice 𝓔 X) EoC.terminal
  Slice-subobject-classifier = {!   !}
  
  Slice-topos : Topos (Slice 𝓔 X)
  Slice-topos .has-is-lex = Slice-lex T.pullbacks
  Slice-topos .cartesian = Slice-closed
  Slice-topos .has-subobject-classifier = Slice-subobject-classifier


```


# Properties of elementary topoi

```agda
module _ {o ℓ} {𝓔 : Precategory o ℓ} (E : Topos 𝓔) where
    module E = Topos E
    module E/ x = Topos (Slice-topos E x)

    lcc : Locally-cartesian-closed 𝓔
    lcc .Locally-cartesian-closed.has-is-lex = E.has-is-lex
    lcc .Locally-cartesian-closed.slices-cc x = {! E/.cartesian x  !}
  
     
```
      