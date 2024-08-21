---
description: |
  Induced topologies
---
<!--
```agda
open import Cat.Displayed.Cocartesian
open import Cat.Prelude

open import Data.Power

open import Topology.Base
```
-->
```agda
module Topology.Instances.Coinduced where
```

# Co-induced topologies

<!--
```agda
private variable
  ℓ ℓ' : Level
  X Y Z : Type ℓ

open Topology-on
open is-continuous
```
-->

```agda
Coinduced
  : ∀ {X : Type ℓ} {Y : Type ℓ'}
  → (f : X → Y)
  → Topology-on X
  → Topology-on Y
Coinduced {X = X} {Y} f X-top = Y-top where
  module X = Topology-on X-top

  Y-top : Topology-on Y
  Y-top .Opens A = X.Opens (Preimage f A)
  Y-top .maximal-open = X.maximal-open
  Y-top .∩-open = X.∩-open
  Y-top .⋃ˢ-open = ⋃-open→⋃ˢ-open (X.Opens ⊙ Preimage f) λ where 
    Uᵢ → X.⋃-open (Preimage f ⊙ Uᵢ)
```    

```agda
coinduced-continuous
  : ∀ {X : Type ℓ} {Y : Type ℓ'} {f : X → Y}
  → {X-top : Topology-on X}
  → is-continuous f X-top (Coinduced f X-top)
coinduced-continuous .reflect-open {U = U} U-open = U-open

coinduced-universal
  : ∀ {S : Topology-on X} {T : Topology-on Z}
  → {f : Y → Z} {g : X → Y}
  → is-continuous (f ⊙ g) S T
  → is-continuous f (Coinduced g S) T
coinduced-universal {S = S} {T = T} {g = g} fg-cont .reflect-open {U} = fg-cont .reflect-open
```

```agda
Topologies-opfibration : ∀ {ℓ} → Cocartesian-fibration (Topologies-on ℓ)
Topologies-opfibration {ℓ} .Cocartesian-fibration.has-lift f X-top = cart where
  open Cocartesian-lift
  open is-cocartesian

  cart : Cocartesian-lift (Topologies-on ℓ) f X-top
  cart .y' = Coinduced f X-top
  cart .lifting = coinduced-continuous
  cart .cocartesian .universal _ = coinduced-universal
  cart .cocartesian .commutes _ _ = prop!
  cart .cocartesian .unique _ _ = prop!
```
  