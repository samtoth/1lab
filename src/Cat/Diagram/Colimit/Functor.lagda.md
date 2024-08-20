# The colimit functor

The operation of taking colimits can be seen as a functor from
$C^I \to C$.

```agda
open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Functor.Adjoint
open import Cat.Functor.Kan.Base
open import Cat.Instances.Functor
open import Cat.Diagram.Colimit.Base
import Cat.Reasoning

module Cat.Diagram.Colimit.Functor {o ℓ jo jℓ : Level}
     (C : Precategory o ℓ) (cocompl : is-cocomplete jo jℓ C) where

open Cat.Reasoning C

private
     FreeColim : ∀ {𝓙 : Precategory jo jℓ} D → Free-object (ConstD {C = C} {J = 𝓙}) D
     FreeColim D = λ where
      .Free-object.free       → coapex
      .Free-object.unit       → cocone
      .Free-object.fold α     → universal (α .η) λ f → α .is-natural _ _ f ∙ idl _
      .Free-object.commute    → ext (λ j → factors _ _)
      .Free-object.unique g p → unique _ _ g λ j → happly (ap η p) j 
          where
          open Colimit (cocompl D) 
          open _=>_
  
ColimitF : ∀ {𝓙 : Precategory jo jℓ} → Functor Cat[ 𝓙 , C ] C
ColimitF = free-objects→functor FreeColim

Colimit⊣Const : ∀ {𝓙 : Precategory jo jℓ} → (ColimitF {𝓙}) ⊣ ConstD
Colimit⊣Const = free-objects→left-adjoint FreeColim

```