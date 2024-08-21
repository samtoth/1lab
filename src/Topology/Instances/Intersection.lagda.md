---
description: |
  The intersection of topologies.
---
<!--
```agda
open import Cat.Prelude

open import Data.Power
open import Data.Sum

open import Topology.Instances.Cofree
open import Topology.Base
```
-->
```agda
module Topology.Instances.Intersection where
```

# Unions of topologies

<!--
```agda
private variable
  ℓ : Level
  X Y : Type ℓ

open is-continuous
open Topology-on
```
-->

```agda
_∩ᵗ_ : Topology-on X → Topology-on X → Topology-on X
(S ∩ᵗ T) .Opens = S .Opens ∩ T .Opens
(S ∩ᵗ T) .maximal-open = (S .maximal-open , T .maximal-open)
(S ∩ᵗ T) .∩-open (U∈S , U∈T) (V∈S , V∈T) = (S .∩-open U∈S V∈S , T .∩-open U∈T V∈T)
(S ∩ᵗ T) .⋃ˢ-open  = ⋃-open→⋃ˢ-open (S .Opens ∩ T .Opens) λ 
                        Uᵢ x → (⋃-open S Uᵢ (fst ⊙ x) , ⋃-open T Uᵢ (snd ⊙ x))

∩-continuousl
  : {S : Topology-on X} {T T' : Topology-on Y}
  → {f : X → Y}
  → is-continuous f S T
  → is-continuous f S (T ∩ᵗ T')
∩-continuousl f-cont .reflect-open = f-cont .reflect-open ⊙ fst

∩-continuousr
  : {S : Topology-on X} {T T' : Topology-on Y}
  → {f : X → Y}
  → is-continuous f S T'
  → is-continuous f S (T ∩ᵗ T')
∩-continuousr f-cont .reflect-open = f-cont .reflect-open ⊙ snd

∩-continuous
  : ∀ {S S' : Topology-on X} {T : Topology-on Y}
  → {f : X → Y}
  → is-continuous f S T
  → is-continuous f S' T
  → is-continuous f (S ∩ᵗ S') T
∩-continuous T-cont T'-cont .reflect-open U∈T 
  = (T-cont .reflect-open U∈T , T'-cont .reflect-open U∈T)

```

```agda
⋂ᵗ : ∀ {κ} {I : Type κ} → (I → Topology-on X) → Topology-on X
⋂ᵗ Tᵢ .Opens = ⋂ (λ i → Tᵢ i .Opens)
⋂ᵗ Tᵢ .maximal-open = inc (λ i → Tᵢ i .maximal-open)
⋂ᵗ Tᵢ .∩-open = rec! (λ U∈T V∈T → inc (λ i → Tᵢ i .∩-open (U∈T i) (V∈T i)))
⋂ᵗ Tᵢ .⋃ˢ-open S S⊆⋂T = inc (λ i → ⋃ˢ-open (Tᵢ i) S (⋂-⊆ (Opens ⊙ Tᵢ) S S⊆⋂T i))

⋂-continuous
  : ∀ {κ} {I : Type κ}
  → {S : Topology-on X} {Tᵢ : I → Topology-on Y}
  → {f : X → Y}
  → (i : I) → is-continuous f S (Tᵢ i)
  → is-continuous f S (⋂ᵗ Tᵢ)
⋂-continuous {f = f} i f-cont .reflect-open 
  = rec! (λ U∈Ti → f-cont .reflect-open (U∈Ti i))

⋂-universal
  : ∀ {κ} {I : Type κ}
  → {Sᵢ : I → Topology-on X} {T : Topology-on Y}
  → {f : X → Y}
  → (∀ i → is-continuous f (Sᵢ i) T)
  → is-continuous f (⋂ᵗ Sᵢ) T
⋂-universal f-cont .reflect-open 
  = rec! (λ U∈T → inc (λ i → f-cont i .reflect-open U∈T))
```
