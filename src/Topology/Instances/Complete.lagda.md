---
description: |
  Products of topological spaces.
---
<!--
```agda
open import Cat.Displayed.Total 
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Sets.Complete
open import Cat.Prelude

open import Topology.Instances.Induced
open import Topology.Instances.Union
open import Topology.Base
```
-->
```agda
module Topology.Instances.Equaliser where
```

# The category of topological spaces is complete

<!--
```agda
private variable
  ℓ ℓ' : Level
  X Y : Type ℓ
  S T : Topology-on X

open Topology-on
open Total-hom
open is-continuous
```
-->

```agda
Topologies-is-complete : ∀ {ι κ o} → is-complete ι κ (Topologies (ι ⊔ κ ⊔ o))
Topologies-is-complete {o = o} {J} F = to-limit (to-is-limit lim) where
  open Limit (Sets-is-complete {o = o} (Topologies↪Sets F∘ F))
  module F = Functor F

  apex' : Topology-on ∣ apex ∣
  apex' = ⋃ᵗ {I = ⌞ J ⌟} (λ j → Induced (ψ j) (F.₀ j .snd))

  lim : make-is-limit F (apex , apex')
  lim .make-is-limit.ψ j = total-hom (ψ j) (⋃-continuous {Sᵢ = λ j → Induced (ψ j) (F.₀ j .snd)}
                                             j induced-continuous)
  lim .make-is-limit.commutes f = ext (λ _ p  → p _ _ f)
  lim .make-is-limit.universal {x} eps₁ p = total-hom (universal {x = x .fst} (λ j → eps₁ j .hom) λ f → ap hom (p f))
                                             (⋃-universal {Tᵢ = λ j → Induced (ψ j) (F.₀ j .snd)} (λ j → 
                                              induced-universal (eps₁ j .preserves)))
  lim .make-is-limit.factors eps₁ p = trivial!
  lim .make-is-limit.unique eps₁ p other x = ext (happly (unique (λ j → eps₁ j .hom) (λ f → ap (λ r → hom r) (p f)) (other .hom) λ j → ap hom (x j)))

```