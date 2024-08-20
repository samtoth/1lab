
```agda

open import Cat.Prelude
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Sets.Complete
open import Topology.Base as Top
open import Topology.Induced
open import Cat.Functor.Kan.Base
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Instances.Identity
open import Cat.Instances.Shape.Terminal

import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM
import Cat.Reasoning as CR

module Topology.Limits where

```

We can use the induced and coinduced topologies to define limits
and co limits respectively.

Looking at a particular example, say products, we can define 
the topology on $X × Y$ as the topology induced by the maps
$\pi_1 : X \times Y \to X$ and $\pi_2 : X \times Y \to Y$.

We can verify that given the following arrangement of morphisms,
$\langle f,g\rangle$ is continuous iff both f and g are continuous.


~~~{.quiver}
% https://q.uiver.app/#q=WzAsNCxbMiwwLCJRIl0sWzIsMiwiWCBcXHRpbWVzIFkiXSxbMCwyLCJYIl0sWzQsMiwiWSJdLFswLDIsImYiLDJdLFsxLDIsIlxccGlfMSJdLFsxLDMsIlxccGlfMiIsMl0sWzAsMywiZyJdLFswLDEsIlxcbGFuZ2xlIGYsZ1xccmFuZ2xlIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d
\[\begin{tikzcd}
	&& Q \\
	\\
	X && {X \times Y} && Y
	\arrow["f"', from=1-3, to=3-1]
	\arrow["{\langle f,g\rangle}"{description}, dashed, from=1-3, to=3-3]
	\arrow["g", from=1-3, to=3-5]
	\arrow["{\pi_1}", from=3-3, to=3-1]
	\arrow["{\pi_2}"', from=3-3, to=3-5]
\end{tikzcd}\]
~~~



```agda

Testing : ∀ {ι κ o ι' κ' : Level} → {J : Precategory ι κ} {J' : Displayed J ι' κ'}
          → (D  : Functor J (Sets (ι ⊔ κ ⊔ o)))
          → (D' : Displayed-functor J' Tops-over D)
          → Limit D
          → ⊤
Testing {ι} {κ} {o} {J = J} {J'} D D' lim = tt where
    open Limit lim
    module J = Precategory J
    module J' = Displayed J'
    module D = Functor D
    module D' = Displayed-functor D'
    open _=>_

    lvl = o ⊔ ι ⊔ κ

    open Displayed (Tops-over {lvl})
    open DR (Tops-over {lvl})

    open Induced ∣ apex ∣ {I = Σ J.Ob J'.Ob[_]} 
                (λ where (j , j') → D.₀ j , D'.F₀' j')
                 (λ where (j , _)  → cone .η j)

    apex' : Topology ∣ apex ∣
    apex' = induced


    ConstD : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {Ext : Functor ⊤Cat C}
            → (C' : Displayed C o' ℓ' ) 
            → ⦃ _ : ∀ {a b} {a' : Displayed.Ob[_] C' a} {b' : Displayed.Ob[_] C' b} {f}
                       → H-Level (Displayed.Hom[ C' ] f a' b') 1 ⦄
            → (apex' : C' .Displayed.Ob[_] (Functor.₀ Ext tt))
            → Displayed-functor (IdD ⊤Cat) C' Ext
    ConstD C' apex' .Displayed-functor.F₀' _ = apex'
    ConstD {C = C} {Ext} C' apex' .Displayed-functor.F₁' {f = tt} tt = subst
                 (λ p₁ → Displayed.Hom[ C' ] p₁ apex' apex') (sym p)
                  (Displayed.id' C') where
        p : Functor.₁ Ext tt ≡ Precategory.id C
        p = Functor.F-id Ext
    ConstD C' apex' .Displayed-functor.F-id' = prop!
    ConstD C' apex' .Displayed-functor.F-∘' = prop!

    Ext' : Displayed-functor (IdD ⊤Cat) Tops-over Ext
    Ext' = ConstD (Tops-over {lvl}) apex'

    module Ext' = Displayed-functor Ext'

    !D : Displayed-functor J' (IdD ⊤Cat) !F
    !D .Displayed-functor.F₀' = λ _ → tt
    !D .Displayed-functor.F₁' = λ _ → tt
    !D .Displayed-functor.F-id' = prop!
    !D .Displayed-functor.F-∘' = prop!

    ε : Ext' F∘' !D =[ eps ]=> D'
    ε ._=[_]=>_.η' j' = induced-cont (_ , j')
    ε ._=[_]=>_.is-natural' _ _ _ = prop!

    module _ (M : Set lvl) (T' : Topology ∣ M ∣)
             (α : const! M F∘ !F => D)
             (α' : ConstD (Tops-over) T' F∘' !D =[ α ]=> D') where

        module α' = _=[_]=>_ α'
        open _=[_]=>_
        module Tops = Displayed (Tops-over {lvl})
        
            
        σ' : ConstD _ T' =[ σ α ]=> Ext'
        σ' ._=[_]=>_.η' {x = tt} tt = induced-initial ∣ M ∣ T' (σ α .η tt) (λ where 
            (j , j') → need j') where
                have : ∀ {j} j' → Top.is-continuous (α .η j) T' (D'.F₀' j')
                have = α'.η'
                comm : ∀ j → eps .η j ⊙ σ α .η tt ≡ η α j
                comm = happly (ap η (σ-comm {β = α}))
                need : ∀ {j} (j' : J'.Ob[ j ] ) → Top.is-continuous (eps .η j ⊙ σ α .η tt) T' (D'.F₀' j')
                need {j} j' = subst (λ p → Top.is-continuous p T' (D'.F₀' j')) (sym $ comm j) (have j')
        σ' ._=[_]=>_.is-natural' x' y' f' = prop!



```
