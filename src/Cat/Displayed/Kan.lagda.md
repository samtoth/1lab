 # Displayed Kan Extensions


In categories Kan extensions provide a way of talking
universal properties; in particular the 1Lab uses them
as a basis for defining Limits and colimits. The concept
generalises easily to the displayed case. We define a
displayed Kan extension in the obvious way over a kan
extension in the base.


```agda

open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Diagram.Limit.Base
open import Cat.Displayed.Total
open import Cat.Displayed.Functor
open import Cat.Functor.Kan.Base
open import Cat.Instances.Shape.Terminal

import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM
import Cat.Reasoning as CR

module Cat.Displayed.Kan 
    {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o ℓ} {C' : Precategory o ℓ}
    (𝓔 : Displayed C o' ℓ') (𝓕 : Displayed D o' ℓ') (𝓔' : Displayed C' o' ℓ')
    where
    
private kan-lvl = o ⊔ ℓ ⊔ o' ⊔ ℓ'

private
    module Disp {C : Precategory o ℓ} (C' : Displayed C o' ℓ') where
        open CR C public
        open Displayed C' public
        open DR C' public
        open DM C' public
        
    module C = Disp 𝓔
    module D = Disp 𝓕
    module C' = Disp 𝓔'
```

```agda
record is-ranᵈ {p : Functor C C'} (p' : Displayed-functor 𝓔 𝓔' p)
               {F : Functor C D} (F' : Displayed-functor 𝓔 𝓕 F) 
               (ran : Ran p F) (Ext' : Displayed-functor 𝓔' 𝓕 (ran .Ran.Ext))
               (eps' : Ext' F∘' p' =[ ran .Ran.eps  ]=> F') : Type (kan-lvl) where
    open Ran ran
    field
        σ' : {M : Functor C' D} (M' : Displayed-functor 𝓔' 𝓕 M)
            {α : M F∘ p => F} (α' : M' F∘' p' =[ α ]=> F')
            → M' =[ σ α ]=> Ext'

        σ-comm' : eps' ∘nt' ? 
```

```agda
record Displayed-ran {p : Functor C C'} (p' : Displayed-functor 𝓔 𝓔' p)
                     {F : Functor C D} (F' : Displayed-functor 𝓔 𝓕 F) 
                     (ran : Ran p F) : Type (kan-lvl) where
    open Ran ran
    
    field
        Ext'     : Displayed-functor 𝓔' 𝓕 Ext
        eps'     : Ext' F∘' p' =[ eps ]=> F'
        has-ran' : is-ranᵈ p' F' ran Ext' eps'

```
