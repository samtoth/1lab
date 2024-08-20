 # Subbasis

Given a Topological space X, we can define a functor to the poset
of subsets ordered by inclusion.



```agda
open import Cat.Prelude
open import Order.Base
open import Order.Instances.Pointwise
open import Order.Frame
open import Topology.Base
open import Data.Power hiding (_∩_ ; _∪_)
open import Cat.Displayed.Univalence.Thin
open import Cat.Displayed.Adjoint
open import Cat.Displayed.Functor
open import Cat.Displayed.Cartesian
open import Cat.Functor.Adjoint
open import Cat.Functor.Adjoint.Hom

import Cat.Displayed.Reasoning

module Topology.Subbasis where
```

```agda
module _ {ℓ} (X : Type ℓ) where
  Top→Subsets : Monotone (Tops-on X) (Subsets (ℙ X))
  Top→Subsets .hom = Topology.is-open
  Top→Subsets .pres-≤ f A o = f A o

  open is-frame (Power-frame X .snd)

  data subbase-completion (S : ℙ X → Ω) : ℙ X → Type (lsuc ℓ) where
      inc-op : ∀ {A} → ∣ S A ∣ → subbase-completion S A
      top-op : subbase-completion S top
      int-op : ∀ {A B : ℙ X} 
                → □ (subbase-completion S A)
                → □ (subbase-completion S B)
                → subbase-completion S (A ∩ B)
      uni-op : ∀ {I : Type ℓ} {fam : I → ℙ X} 
                → ((i : I) → □ (subbase-completion S (fam i)))
                → subbase-completion S (⋃ fam)
  
  subbase-topology : ℙ (ℙ X) → Topology X
  subbase-topology S .Topology.is-open A = elΩ (subbase-completion S A)
  subbase-topology S .Topology.top-open = inc top-op
  subbase-topology S .Topology.meet-open a b = inc (int-op a b)
  subbase-topology S .Topology.join-open fam op = inc (uni-op op)

  {-# TERMINATING #-}
  Subsets→Top : Monotone (Subsets (ℙ X)) (Tops-on X)
  Subsets→Top .hom = subbase-topology
  Subsets→Top .pres-≤ f A o = go f o
    where
      go : ∀ {x y} (f : (A : ℙ X) → ∣ x A ∣ → ∣ y A ∣) {A}
          → □ (subbase-completion x A) → □ (subbase-completion y A)
      go f o = do
        (inc-op o) ← o
            where top-op → inc top-op
                  (int-op x y) → inc (int-op (go f x) (go f y))
                  (uni-op x) → inc (uni-op (λ i → go f (x i)))
        inc (inc-op (f _ o))
``` 

These pair of functors form something called a [galois connection](https://ncatlab.org/nlab/show/Galois+connection).
This is simply an adjunction in the posetal world.

```agda
  {-# TERMINATING #-}
  subbase-rec : ∀  {x : ℙ X → Ω} {y : Topology X} → let open Topology y
            in (f : (A : ℙ X) → ∣ x A ∣ → is-open' A) → (A : ℙ X)
            →  (o : □ (subbase-completion x A)) → is-open' A
  subbase-rec {x} {y} f A o = let open Topology y 
    in □-rec (hlevel 1) 
    (λ where (inc-op x) → f A x
             top-op → top-open
             (int-op {A} {B} a b) → meet-open (subbase-rec {_} {y} f A a) (subbase-rec {_} {y} f B b)
             (uni-op {I} {fam} x) → join-open fam (λ i → subbase-rec {_} {y} f (fam i) (x i))) o


  Free⊣Forget : ∀ {x y} 
              → (Tops-on X .Poset._≤_ (Subsets→Top .hom x) y 
                  → Subsets (ℙ X) .Poset._≤_ x (Top→Subsets .hom y))
              × (Subsets (ℙ X) .Poset._≤_ x (Top→Subsets .hom y) 
                  → Tops-on X .Poset._≤_ (Subsets→Top .hom x) y )
  Free⊣Forget {_} {y} = (λ f A o → f A (inc (inc-op o))) ,
                         λ f A o → subbase-rec {_} {y} f A o

``` 

This galois connection extends to a displayed adjunction between the subset fibration
and Topological spaces. We could use the Subobject fibration over set, which is encoded
with monos $A \hookrightarrow X$, but instaed we will give a bespoke subset category
where objects are instead $X \to \Omega$, which makes the formalisation smoother.

We also note that both the displayed category of subbases and of topology are both 
displayed over sets, so we can use a vertical adjunction, again making life easier.

```agda

is-subcontinuous : ∀ {ℓ} {X Y : Type ℓ} (f : X → Y) → ℙ (ℙ X) → ℙ (ℙ Y) → Type ℓ
is-subcontinuous {Y = Y} f A B = ∀ (S : ℙ Y) →  ∣ B S ∣ → ∣ A (S ⊙ f) ∣ 

Subbase-structure : ∀ {ℓ} → Thin-structure {ℓ} ℓ (ℙ ⊙ ℙ)
Subbase-structure .is-hom {_} {y} f A B = el! (is-subcontinuous f A B)
Subbase-structure .id-is-hom _ x = x
Subbase-structure .∘-is-hom f g p q S z = q (S ⊙ f) (p S z)
Subbase-structure .id-hom-unique p q = ext (λ x → Ω-ua (q x) (p x))

Subbases-over : ∀ {ℓ} → Displayed (Sets ℓ) ℓ ℓ
Subbases-over = Thin-structure-over Subbase-structure

module subbase {ℓ} = Displayed (Subbases-over {ℓ})

Forgetᵈ : ∀ {ℓ} → Vertical-functor {B = Sets ℓ} Tops-over Subbases-over
Forgetᵈ .Vertical-functor.F₀' = Topology.is-open
Forgetᵈ .Vertical-functor.F₁' x = x
Forgetᵈ .Vertical-functor.F-id' = refl
Forgetᵈ .Vertical-functor.F-∘' = refl

{-# TERMINATING #-}
map-subbase-topology : ∀ {ℓ} {X Y : Type ℓ} {f : X → Y} (X' : ℙ (ℙ X)) (Y' : ℙ (ℙ Y))
    → is-subcontinuous f X' Y' 
    → is-continuous f (subbase-topology X X') (subbase-topology Y Y')
map-subbase-topology {ℓ} X' Y' fc A = □-rec (hlevel 1) λ where 
  (inc-op A∈Y) → inc (inc-op (fc A A∈Y))
  top-op → inc top-op
  (int-op {A} {B} a b) → do
      a ← a
      b ← b
      inc (int-op (map-subbase-topology X' Y' fc A (inc a)) (map-subbase-topology X' Y' fc B (inc b)))
  (uni-op {I} {fam} fam') → inc (uni-op (λ i → □-rec (hlevel 1) (λ fam∈Y → map-subbase-topology X' Y' fc (fam i) (fam' i)) (fam' i)))

Freeᵈ : ∀ {ℓ} → Vertical-functor {B = Sets ℓ} Subbases-over Tops-over
Freeᵈ .Vertical-functor.F₀' {X} = Subsets→Top ∣ X ∣ .hom
Freeᵈ .Vertical-functor.F₁' = map-subbase-topology _ _
Freeᵈ .Vertical-functor.F-id' = prop!
Freeᵈ .Vertical-functor.F-∘' = prop!


Free⊣ᵈForget : ∀ {ℓ} → Forgetᵈ ⊣↓ Freeᵈ {ℓ}
Free⊣ᵈForget ._⊣↓_.unit' ._=>↓_.η' {x} x' = subbase-rec ∣ x ∣ {x' .Topology.is-open} {x'} λ _ x → x
Free⊣ᵈForget ._⊣↓_.unit' ._=>↓_.is-natural' _ _ _ = prop!
Free⊣ᵈForget ._⊣↓_.counit' ._=>↓_.η' _ _ x = inc (inc-op x)
Free⊣ᵈForget ._⊣↓_.counit' ._=>↓_.is-natural' _ _ _ = prop!
Free⊣ᵈForget ._⊣↓_.zig' = refl
Free⊣ᵈForget ._⊣↓_.zag' = ext (λ _ _ → prop!)

L-adjoint : ∀ {ℓ} {X Y : Type ℓ} ⦃ _ : H-Level X 2 ⦄ ⦃ _ : H-Level Y 2 ⦄
              {f : X → Y} → (X' : Topology X) → (Y' : ℙ (ℙ Y))
          → is-subcontinuous f (X' .Topology.is-open) Y'
          → is-continuous f X' (subbase-topology Y Y')
L-adjoint {ℓ} {X} {Y} {f} X' Y' fsc = let cnt : is-continuous f (subbase-topology X (X' .is-open)) (subbase-topology Y Y')
                                          cnt =  map-subbase-topology (X' .is-open) Y' fsc
                                          eta : is-continuous (λ x → x) X' (subbase-topology X (X' .is-open))
                                          eta = unit'.η' {el! X} X'
                                          res : is-continuous f X' (subbase-topology Y Y')
                                          res A A∈Y' = eta (A ⊙ f) (cnt A A∈Y')
                                      in  res
  where open Topology
        open _⊣↓_ {lsuc ℓ} Free⊣ᵈForget
        open Displayed (Tops-over {ℓ})
        open Cat.Displayed.Reasoning (Tops-over {ℓ})

-- Tops-over-fibration : ∀ {ℓ} → Cartesian-fibration (Tops-over {ℓ})
-- Tops-over-fibration .Cartesian-fibration.has-lift f y' .Cartesian-lift.x' = {!   !}
-- Tops-over-fibration .Cartesian-fibration.has-lift f y' .Cartesian-lift.lifting = {!   !}
-- Tops-over-fibration .Cartesian-fibration.has-lift f y' .Cartesian-lift.cartesian = {!   !}
```       