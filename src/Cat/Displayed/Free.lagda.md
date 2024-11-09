```agda
open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Functor.Adjoint.Hom

module Cat.Displayed.Free where
```

```agda
record Free-objects
    {o ℓ o' ℓ'} {B : Precategory o ℓ}
    (D : Displayed B o' ℓ') : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') 
  where
  
  open Displayed D
  module B = Precategory B

  field
    free : ∀ {X} → Ob[ X ]
    fold : ∀ {X Y} → (Y' : Ob[ Y ]) → (f : B.Hom X Y) → Hom[ f ] free Y'

    unique : ∀ {x} {y} {Y : Ob[ y ]} (f : B.Hom x y) 
      → (g : Hom[ f ] free Y)
      → fold Y f  ≡[ refl ] g

module _ {o ℓ o' ℓ'} {B : Precategory o ℓ}
    (D : Displayed B o' ℓ') (Free : Free-objects D) where

  open Free-objects Free
  open Displayed D

  Free-objects→Functor : Functor B (∫ D)
  Free-objects→Functor = func where

    func : Functor B (∫ D)
    func .Functor.F₀ X = X , free
    func .Functor.F₁ f = total-hom f (fold free f)
    func .Functor.F-id = total-hom-path D refl (unique B.id id')
    func .Functor.F-∘ f g = total-hom-path D refl 
      (unique (f B.∘ g) _)

  forget-is-equiv : ∀ {X Y} {Y' : Ob[ Y ]} 
    → is-equiv {A = Total-hom D (X , free) (Y , Y')} (λ f → f .Total-hom.hom)
  forget-is-equiv .is-eqv f .centre = (total-hom f (fold _ f)) , refl
  forget-is-equiv .is-eqv f .paths (total-hom hom pres , p) 
    = total-hom-path D (sym p) (J (λ a p → fold _ a ≡[ sym p ] pres) (unique _ pres) p)
    ,ₚ is-prop→pathp (λ i → hlevel 1) refl p

  Free-objects→left-adjoint : Free-objects→Functor ⊣ πᶠ D
  Free-objects→left-adjoint = hom-iso→adjoints (λ x → x .Total-hom.hom) forget-is-equiv
     λ g h x → refl
 
```