<!--
```agda
open import Cat.Prelude
open import Cat.Functor.Equivalence
```
-->

```agda
module Cat.Instances.Lift where
```

# Lifting categories across universes

Suppose you have a category $\cC$ with objects in $o$ and homs in
$\ell$, but you really need it to have objects in some larger universe
$o \sqcup o'$ and homs in $\ell \sqcup \ell'$. Fortunately you can
uniformly lift the precategory $\cC$ to this bigger universe.

```agda
Lift-cat : ∀ {o ℓ} o' ℓ' → Precategory o ℓ → Precategory (o ⊔ o') (ℓ ⊔ ℓ')
Lift-cat o' ℓ' C = liftc where
  open Precategory C
  liftc : Precategory _ _
  liftc .Precategory.Ob = Lift o' Ob
  liftc .Precategory.Hom (lift x) (lift y) = Lift ℓ' (Hom x y)
  liftc .Precategory.Hom-set x y = hlevel 2
  liftc .Precategory.id = lift id
  liftc .Precategory._∘_ (lift f) (lift g) = lift (f ∘ g)
  liftc .Precategory.idr (lift f) = ap lift (idr f)
  liftc .Precategory.idl (lift f) = ap lift (idl f)
  liftc .Precategory.assoc (lift f) (lift g) (lift h) = ap lift (assoc f g h)

Lift-functor-l
  : ∀ {so sℓ} bo bℓ {o ℓ} {C : Precategory so sℓ} {D : Precategory o ℓ}
  → Functor C D
  → Functor (Lift-cat bo bℓ C) D
Lift-functor-l bo bℓ G = F where
  open Functor
  F : Functor _ _
  F .F₀ (lift x) = G .F₀ x
  F .F₁ (lift f) = G .F₁ f
  F .F-id = G .F-id
  F .F-∘ (lift f) (lift g) = G .F-∘ f g

Lift-functor-r
  : ∀ {so sℓ} bo bℓ {o ℓ} {C : Precategory so sℓ} {D : Precategory o ℓ}
  → Functor C D
  → Functor C (Lift-cat bo bℓ D)
Lift-functor-r bo bℓ G = F where
  open Functor
  F : Functor _ _
  F .F₀ x = lift $ G .F₀ x
  F .F₁ f = lift $ G .F₁ f
  F .F-id = ap lift $ G .F-id
  F .F-∘ f g = ap lift $ G .F-∘ f g
```

```agda
is-iso→Lift-functor-l-is-iso : ∀ {so sℓ} bo bℓ {o ℓ} {C : Precategory so sℓ} {D : Precategory o ℓ}
  → (F : Functor C D) → is-precat-iso F
  → is-precat-iso (Lift-functor-l bo bℓ F)
is-iso→Lift-functor-l-is-iso bo bℓ F i = eqv where
  -- open Functor F
  open is-precat-iso i
  
  eqv : is-precat-iso _
  eqv .is-precat-iso.has-is-ff .is-eqv f =
    contr (lift (has-is-ff .is-eqv f .centre .fst) , has-is-ff .is-eqv f .centre .snd)
       λ where (lift g , p) → ap₂ _,_ (ap lift (ap fst $ has-is-ff .is-eqv f .paths (g , p)))
                               (ap snd $ has-is-ff .is-eqv f .paths (g , p))
  eqv .is-precat-iso.has-is-iso .is-eqv y = contr 
    ((lift $ has-is-iso .is-eqv y .centre .fst) , has-is-iso .is-eqv y .centre .snd)
     λ where (lift x , p) → ap (λ where (x , y) → (lift x , y)) $ has-is-iso .is-eqv y .paths (x , p)
 
```