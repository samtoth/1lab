# Lattice structure of the topology order



### Latice structure of topologies

Thi poset of topologies on a particular set has the structure of a complete lattice, however
it isn't simply inherited pointwise from the lattice structure of subsets. In general an
arbritary union of open sets of topological spaces fails to be a valid set of opens for
a topological space, consider for example, the union of the topological spaces:
$\{\{\}, \{a\}, \{a,b,c\}\}$ and $\{\{\}, \{c\} \{a,b,c\}\}$. 

```agda
open import Cat.Prelude
open import Order.Lattice
open import Topology.Base
open import Topology.Subbasis
open import Data.Power hiding (_∩_; _∪_)
open import Order.Diagram.Meet
open import Order.Diagram.Join
open import Order.Diagram.Top
open import Order.Diagram.Bottom
open import Order.Diagram.Lub
open import Order.Diagram.Glb
open import Order.Base
open import Order.Instances.Pointwise
open import Order.Instances.Pointwise.Diagrams
open import Order.Instances.Props

module Topology.Order.Lattice {ℓ} (X : Type ℓ) where

open ℙ {ℓ} (ℙ X)
private module free = Monotone (Subsets→Top X)

Tops-∩ : Topology X → Topology X → Topology X
Tops-∩ x y = do
    let module x = Topology x
    let module y = Topology y

    λ where .Topology.is-open → x.is-open ∩ y.is-open
            .Topology.top-open → (x.top-open , y.top-open)
            .Topology.meet-open (xU , yU) (xV , yV) → (x.meet-open xU xV , y.meet-open yU yV)
            .Topology.join-open fam op → (x.join-open fam (λ i → op i .fst) , y.join-open fam (λ i → op i .snd))

Tops-∩-meets : ∀ x y → is-meet (Tops-on X) x y (Tops-∩ x y)
Tops-∩-meets x y = do
    let module x = Topology x
    let module y = Topology y
    let open is-meet (∩-meets x.is-open y.is-open)

    λ where .is-meet.meet≤l A (x , _) → x
            .is-meet.meet≤r A (_ , y) → y
            .is-meet.greatest lb' f g A o → (f A o , g A o)

Tops-top : Top (Tops-on X)
Tops-top .Top.top .Topology.is-open = top
Tops-top .Top.top .Topology.top-open = tt
Tops-top .Top.top .Topology.meet-open = λ _ _ → tt
Tops-top .Top.top .Topology.join-open = λ fam _ → tt
Tops-top .Top.has-top = λ x A _ → tt

Tops-∪ : Topology X → Topology X → Topology X
Tops-∪ x y = do
    let module x = Topology x
    let module y = Topology y

    free.hom (x.is-open ∪ y.is-open)

Tops-∪-joins : ∀ x y → is-join (Tops-on X) x y (Tops-∪ x y)
Tops-∪-joins x y = do
    let module x = Topology x
    let module y = Topology y

    let open is-join (∪-joins x.is-open y.is-open)
    
    λ where .is-join.l≤join A A∈x → inc (inc-op (l≤join A A∈x))
            .is-join.r≤join A A∈y → inc (inc-op (r≤join A A∈y))
            .is-join.least ub' x≤ub' y≤ub' A → Free⊣Forget X {_} {ub'}
                 .snd (λ B B∈x∪y → least (ub' .Topology.is-open) x≤ub' y≤ub' B B∈x∪y) A


Tops-bot : Bottom (Tops-on X)
Tops-bot .Bottom.bot = free.hom bot
Tops-bot .Bottom.has-bottom x A = Free⊣Forget X {_} {x} .snd 
    (λ B B∈bot → ¡ {Topology.is-open x} B B∈bot) A

Tops-lattice : is-lattice (Tops-on X)
Tops-lattice .is-lattice._∩_ = Tops-∩
Tops-lattice .is-lattice.∩-meets = Tops-∩-meets
Tops-lattice .is-lattice._∪_ = Tops-∪
Tops-lattice .is-lattice.∪-joins = Tops-∪-joins
Tops-lattice .is-lattice.has-top = Tops-top
Tops-lattice .is-lattice.has-bottom = Tops-bot
```

We can also take arbritary joins and meets.


```agda
Tops-⋃ : ∀ {I : Type ℓ} (fam : I → Topology X) → Topology X
Tops-⋃ fam = free.hom (⋃ λ i → Topology.is-open (fam i))

Tops-⋃-lubs : ∀ {I : Type ℓ} (fam : I → Topology X) → is-lub (Tops-on X) fam (Tops-⋃ fam)
Tops-⋃-lubs fam .is-lub.fam≤lub i _ o = inc (inc-op (inc (i , o)))
Tops-⋃-lubs fam .is-lub.least ub' α = Free⊣Forget X {_} {ub'} .snd λ A A∈fam → 
                                        □-rec (hlevel 1) (λ where (i , A∈fam) → α i A A∈fam) A∈fam

private 
    -- TODO: Move somewhere more sensible
    subset-has-glbs : {I : Type ℓ} → (fam : I → ℙ X) → is-glb (Subsets X) fam (λ A → ∀Ω[ i ∈ I ] fam i A)
    subset-has-glbs fam = is-glb-pointwise fam _ (λ x → Props-has-glbs λ i → fam i x)

Tops-⋂ : ∀ {I : Type ℓ} (fam : I → Topology X) → Topology X
Tops-⋂ {I} fam = do
    let module fam i = Topology (fam i)
    λ where .Topology.is-open A → ∀Ω[ i ∈ I ] fam.is-open i A
            .Topology.top-open → inc (λ i → fam.top-open i)
            .Topology.meet-open a b → do
                a ← a
                b ← b
                inc (λ i → fam.meet-open i (a i) (b i))
            .Topology.join-open {J} fam' fam'∈fam → do 
                inc (λ i → fam.join-open i fam' (λ j 
                    → □-rec (hlevel 1) (λ fam'∈fam → fam'∈fam i) (fam'∈fam j)))

Tops-⋂-glbs : ∀ {I : Type ℓ} (fam : I → Topology X) → is-glb (Tops-on X) fam (Tops-⋂ fam)
Tops-⋂-glbs fam .is-glb.glb≤fam i A = □-rec (hlevel 1) (λ f → f i)
Tops-⋂-glbs fam .is-glb.greatest lb' α A A∈lb' = inc (λ i → α i A A∈lb')
  
``` 