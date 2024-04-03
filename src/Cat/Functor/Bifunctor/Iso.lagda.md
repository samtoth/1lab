<!--
```agda
open import Cat.Prelude
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Functor.Bifunctor
open import Cat.Functor.Naturality
import Cat.Morphism
```
-->

```agda
module Cat.Functor.Bifunctor.Iso 
  {o₁ h₁ o₂ h₂ o₃ h₃ : _}
  {C : Precategory o₁ h₁}
  {D : Precategory o₂ h₂}
  {E : Precategory o₃ h₃}
  (F : Functor (C ×ᶜ D) E)
  where
```

<!--
```agda
private
  module C = Precategory C
  module D = Precategory D
  module E = Precategory E

open Functor F public
```
-->




```agda
Left-iso : ∀ (G : Functor (C ×ᶜ D) E) → F ≅ⁿ G → ∀ A → Left F A ≅ⁿ Left G A
Left-iso G α A = the-iso where
    open _=>_ (α .Isoⁿ.to) using (η) renaming (is-natural to η-nat)
    open _=>_ (α .Isoⁿ.from) renaming (η to ε ; is-natural to ε-nat)

    open Cat.Morphism using (_≅_; Inverses)

    the-iso : (Left F A) ≅ⁿ (Left G A)
    the-iso ._≅_.to = NT (λ _ → η _) λ _ _ _ → η-nat _ _ _
    the-iso ._≅_.from = NT (λ _ → ε _) (λ _ _ _ → ε-nat _ _ _)
    the-iso ._≅_.inverses .Inverses.invl = ext (λ _ → α .Isoⁿ.invl ηₚ _)
    the-iso ._≅_.inverses .Inverses.invr = ext (λ _ → α .Isoⁿ.invr ηₚ _)
 
```

```agda
Left∘-F×- : ∀ {o4 o5 h4 h5} {A : Precategory o4 h4} {B : Precategory o5 h5} → (G0 : Functor A C) (G1 : Functor B D)
        → ∀ a → Left (F F∘ (G0 F× G1)) a ≅ⁿ Left F (G1 .Functor.F₀ a) F∘ G0
Left∘-F×- G0 G1 a = the-iso where
    open Cat.Morphism using (_≅_; Inverses)

    the-iso : Left (F F∘ (G0 F× G1)) a ≅ⁿ (Left F (G1 .Functor.F₀ a) F∘ G0)
    the-iso ._≅_.to = NT (λ _ → E.id) (λ _ _ f → E.idl _ ∙ (λ i → F .Functor.F₁ (G0 .Functor.F₁ f , G1 .Functor.F-id i)) ∙ sym (E.idr _))
    the-iso ._≅_.from = NT (λ _ → E.id) λ x y f → E.idl _ ∙ (λ i → F .Functor.F₁ (G0 .Functor.F₁ f , G1 .Functor.F-id (~ i))) ∙ sym (E.idr _)
    the-iso ._≅_.inverses .Inverses.invl = ext (λ _ → E.idl _)
    the-iso ._≅_.inverses .Inverses.invr = ext (λ _ → E.idr _)

-∘Left : ∀ {o4 h4} {A : Precategory o4 h4} → (G : Functor E A)
       → ∀ a → Left (G F∘ F) a ≅ⁿ G F∘ Left F a
-∘Left {A = A} G a = the-iso where
    open Cat.Morphism using (_≅_; Inverses)
    module A = Precategory A
    
    the-iso : Left (G F∘ F) a ≅ⁿ (G F∘ Left F a)
    the-iso ._≅_.to = NT (λ _ → A.id) λ _ _ _ → A.idl _ ∙  sym (A.idr _)
    the-iso ._≅_.from = NT (λ _ → A.id) λ _ _ _ → A.idl _ ∙  sym (A.idr _)
    the-iso ._≅_.inverses .Inverses.invl = ext (λ _ → A.idl _)
    the-iso ._≅_.inverses .Inverses.invr = ext (λ _ → A.idr _)
```
