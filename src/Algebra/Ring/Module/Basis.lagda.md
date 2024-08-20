

```agda
open import Cat.Prelude
open import Cat.Functor.Adjoint
open import Cat.Displayed.Total
open import Cat.Abelian.Base
open import Cat.Diagram.Zero
open import Order.Base
open import Order.Subposet
open import Order.Instances.Pointwise
open import Order.Diagram.Bottom
open import Order.Diagram.Lub
open import Order.DCPO
open import Order.DCPO.Pointed
open import Algebra.Ring
open import Algebra.Ring.Module
open import Algebra.Ring.Module.Free
open import Algebra.Ring.Module.Category

import Cat.Morphism

module Algebra.Ring.Module.Basis {ℓ} (R : Ring ℓ) where

open Ring-on (R .snd) hiding (_↪_; is-monic)
```


We will establish what it means for a module to have a basis,
and define the poset of linearly independent subsets.

```agda

module _ (M : Module R ℓ) where
  open Module-on (M .snd)
  module Free-module where
    open Functor (Free-module R {ℓ}) public
    ^ : ∀ {S : Set ℓ} → (⌞ S ⌟ → ⌞ M ⌟) → R-Mod.Hom (F₀ S) M
    ^ {S} f = R-adjunct (Free⊣Forget R {ℓ}) {S} {M} f

  module FreeMod S = Module-on (Free-Mod {ℓ} R {ℓ} S .snd)

  is-linearly-independent : (S : ⌞ M ⌟ → Ω) → Type (lsuc ℓ)
  is-linearly-independent S = R-Mod.is-monic (Free-module.^ {S = S'} emb) where
    S' : Set ℓ
    S' = el! (Σ[ m ∈ ⌞ M ⌟ ] ⌞ S m ⌟)
    emb : ⌞ S' ⌟ → ⌞ M ⌟
    emb = fst
  
  is-linearly-independent-is-prop : ∀ (S : ⌞ M ⌟ → Ω) → is-prop (is-linearly-independent S)
  is-linearly-independent-is-prop S = R-Mod.is-monic-is-prop _

  emptyLInd : is-linearly-independent (λ _ → ⊥Ω)
  emptyLInd f g x = !-unique₂ _ _ where
    -- the argument here is that Free {} is initial (left adjoints preserve limits) and therefor a zero object
    -- We don't have great abelian category stuff yet so it seemed easier to just show that it's a zero object
    -- directly
    opaque
      Free⊥-is-0 : is-zero (R-Mod R ℓ) (Free-module.F₀ (el! (Σ ⌞ M ⌟ λ _ → ⌞ ⊥Ω ⌟)))
      Free⊥-is-0 = id-zero→zero (R-Mod-ab-category R) (ext (λ 
        where x → Free-elim-prop.elim {P = λ x → x ≡ 0m}
                    (λ where 
                      .Free-elim-prop.has-is-prop _ → squash _ _
                      .Free-elim-prop.P-0m → refl
                      .Free-elim-prop.P-neg _ p → ap neg p ∙ FreeMod.ab.neg-0 _
                      .Free-elim-prop.P-inc ()
                      .Free-elim-prop.P-· _ _ p →
                        subst (λ y → FreeMod._⋆_ _ _ y ≡ 0m) (sym p) (FreeMod.⋆-idr _)
                      .Free-elim-prop.P-+ _ _ p q → 
                        subst (λ (x , y) → FreeMod._+_ _ x y ≡ 0m) (sym p ,ₚ sym q) (FreeMod.+-idl _)) 
                    x))

    open Zero (record { ∅ = (Free-module.F₀ (el! (Σ ⌞ M ⌟ λ _ → ⌞ ⊥Ω ⌟))) ; has-is-zero = Free⊥-is-0 })


  LIndSubsets : Poset (lsuc ℓ) ℓ
  LIndSubsets = Subposet (Subsets ⌞ M ⌟) λ x → el (is-linearly-independent x) (is-linearly-independent-is-prop x)



  LIndDCPO : is-dcpo LIndSubsets
  LIndDCPO .is-dcpo.directed-lubs {Ix = Ix} fam directed = lub where
```
We take the normal union operation on subsets
```agda
    union : ⌞ M ⌟ → Ω
    union m = ∃Ω Ix λ i → fam i .fst m

```
Now we need to show that the union of any directed set of linearly independant subsets
is itself linearly independant.
```agda
    unionLI : is-linearly-independent union
    unionLI = {!   !}

    lub : Lub LIndSubsets fam
    lub .Lub.lub = union , unionLI
    lub .Lub.has-lub .is-lub.fam≤lub i m pim = inc (i , pim)
    lub .Lub.has-lub .is-lub.least ub' is-ub' m un = □-elim (λ _ → ub' .fst m .is-tr) (λ (i , p) → is-ub' i m p) un

  has-bot : Bottom LIndSubsets
  has-bot = subposet-bottom subsets-bot emptyLInd where
    subsets-bot : Bottom (Subsets ⌞ M ⌟)
    subsets-bot .Bottom.bot _ = ⊥Ω
    subsets-bot .Bottom.has-bottom x x₁ ()
  
  LIndPointed : is-pointed-dcpo (LIndSubsets , LIndDCPO)
  LIndPointed = has-bot
    
```  