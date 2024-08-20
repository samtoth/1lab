# (Co)induced topologies

Given a set $X$, a topological space $Y$ and a map $f : X \to |Y|$, we can give
a topology to $X$, such that the map $f : X \to Y$ is continuos. If instead we have
a set $Y$ and a topology on $X$, then we can give X a topology which is the finest
that makes $f$ continuous.

If you recall our setup of the category Top displayed over Set, then this property 
has a pre-existing notion. Namely cartesian (resp. co-cartesian) fibrations.

```agda
open import Cat.Prelude
open import Topology.Base
open import Topology.Subbasis
open import Data.Power hiding (_∪_ ; _∩_)
open import Order.Base
open import Cat.Displayed.Cartesian

private
  module Tops {ℓ} = Precategory (Tops {ℓ})

module Topology.Induced where

module _ {ℓ} (X : Type ℓ) where

  private
    module free = Monotone (Subsets→Top X)

  open Poset (Tops-on X)
  module Induced {k} {I : Type k} (Y : I → Tops.Ob {ℓ}) (f : (i : I) → X → ⌞ Y i ⌟) where
    private module Y i = Topology (Y i .snd)

    private
      OX' : ℙ X → Ω
      OX' A = ∃Ω[ i ∈ I ] ∃Ω[ fA ∈ ℙ ⌞ Y i ⌟ ] (Y.is-open i fA ∧Ω elΩ (fA ⊙ f i ≡ A))

    induced : Topology X
    induced = free.hom OX'

    induced-cont : (i : I) → is-continuous (f i) induced (Y i .snd)
    induced-cont i A A∈Yi = inc (inc-op (inc (i , (inc (A , (A∈Yi , (inc refl)))))))

    induced-least : (T' : Topology X) → (f-cont : (i : I) → is-continuous (f i) T' (Y i .snd))
                  → induced ≤ T'
    induced-least T' fc = Free⊣Forget X {_} {T'} .snd (λ A → □-rec (hlevel 1) λ where 
            (i , op) → □-rec (hlevel 1) (λ where (fA , op , fib) → □-rec (hlevel 1) (λ where 
                p → subst (Topology.is-open' T') p (fc i fA op)) fib) op)

    {-# TERMINATING #-}
    induced-initial :  (x' : Type ℓ) ⦃ _ : H-Level x' 2 ⦄ → (X' : Topology x') → (g : x' → X) 
                     →  (f∘gc : (i : I) → is-continuous (f i ⊙ g) X' (Y i .snd))
                     →  is-continuous g X' induced
    induced-initial x' X' g f∘gc A = go' where
      module X' = Topology X'
      go' : ∀ {N} → □ (subbase-completion X _ N) → Topology.is-open' X' (N ⊙ g)
      go : ∀ {N} → subbase-completion X _ N → Topology.is-open' X' (N ⊙ g)
      
      go' = □-rec (hlevel 1) go
      go (inc-op x) = □-rec (hlevel 1) (uncurry 
                       (λ i → □-rec (hlevel 1) (uncurry 
                         (λ A' → uncurry
                           (λ A'∈Yi → □-rec (hlevel 1) 
                             λ p → subst (λ p → Topology.is-open' X' p) (ap (_⊙ g) p) (f∘gc i A' A'∈Yi)))))) x
      go top-op = X'.top-open
      go (int-op x y) = X'.meet-open (go' x) (go' y)
      go (uni-op {_} {fam} x) = X'.join-open (λ i → fam i ⊙ g) λ i → go' (x i)

  module Coinduced {k} {I : Type k} (Y : I → Tops.Ob {ℓ}) (f : (i : I) → ⌞ Y i ⌟ → X) where
    module Y i = Topology (Y i .snd)

    coinduced : Topology X
    coinduced .Topology.is-open A = ∀Ω[ i ∈ I ] Y.is-open i (A ⊙ f i)
    coinduced .Topology.top-open  = inc (λ i → Y.top-open i)
    coinduced .Topology.meet-open a b = a >>= λ a → b >>= λ b → inc (λ i → Y.meet-open i (a i) (b i))
    coinduced .Topology.join-open fam fam∈Y = inc (λ i → Y.join-open i (λ j → fam j ⊙ f i) λ where 
                                                j → □-rec (hlevel 1) (λ fam∈- → fam∈- i) (fam∈Y j))

    coinduced-continuous : (i : I) → is-continuous (f i) (Y i .snd) coinduced
    coinduced-continuous i A = □-rec (hlevel 1) λ op → op i

    coinduced-greatest : (T' : Topology X) → (f-cont : (i : I) → is-continuous (f i) (Y i .snd) T')
                       → T' ≤ coinduced
    coinduced-greatest T' fc A A∈T' = inc (λ i → fc i A A∈T')

    coinduced-terminal : (x' : Type ℓ) ⦃ _ : H-Level x' 2 ⦄ → (X' : Topology x') → (g : X → x') 
                     →  (f∘gc : (i : I) → is-continuous (g ⊙ f i) (Y i .snd) X')
                     →  is-continuous g coinduced X'
    coinduced-terminal x' X' g f∘gc A x = inc (λ i → f∘gc i A x)
```



To show we have a bi-fibration we need to do a bit more work. We need the more general theorem that
for any Topology on some other set $X'$ with a function $g : X' \to X$, such that $f_i \circ g$ is a
continuous map for all $Y_i$, we have that $g$ is continuous.

 
```agda
  
```