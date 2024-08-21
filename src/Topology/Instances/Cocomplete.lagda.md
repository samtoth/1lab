---
description: |
  Products of topological spaces.
---
<!--
```agda
open import Cat.Displayed.Total 
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Sets.Cocomplete
open import Cat.Prelude

open import Topology.Instances.Coinduced
open import Topology.Instances.Intersection
open import Topology.Base
```
-->
```agda
module Topology.Instances.Cocomplete where
```

# The category of topological spaces is cocomplete

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
Topologies-is-cocomplete : ∀ {ι κ o} → is-cocomplete ι κ (Topologies (ι ⊔ κ ⊔ o))
Topologies-is-cocomplete {o = o} {J} F = to-colimit (to-is-colimit colim) where
  open Colimit (Sets-is-cocomplete {o = o} (Topologies↪Sets F∘ F))
  module F = Functor F

  coapex' : Topology-on ∣ coapex ∣
  coapex' = ⋂ᵗ {I = ⌞ J ⌟} (λ j → Coinduced (ψ j) (F.₀ j .snd))

  colim : make-is-colimit F (coapex , coapex')
  colim .make-is-colimit.ψ j = total-hom (ψ j) 
    (⋂-continuous j (record { reflect-open = λ x → x }))
  colim .make-is-colimit.commutes f = ext (happly (commutes f))
  colim .make-is-colimit.universal {x} eta₁ p 
    = total-hom (universal {x = x .fst} (hom ⊙ eta₁) λ f → ap hom (p f))
        (record { reflect-open = λ U∈X → inc (λ j → eta₁ j .preserves .reflect-open U∈X) })
  colim .make-is-colimit.factors _ _ = trivial!
  colim .make-is-colimit.unique {X} eta₁ p other x 
    = ext (λ j Fj → happly (unique {el! ∣ X .fst ∣}
        (λ j → eta₁ j .hom)
        (λ f → ap hom (p f))
        (other .hom) 
        λ j → ap hom (x j)) (inc (j , Fj)))
``` 