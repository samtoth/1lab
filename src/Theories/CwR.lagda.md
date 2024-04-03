
 Constructing Uemeras notion of categories with representable maps

```agda
module Theories.CwR where

open import Cat.Prelude
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.WideSubcategory
open import Cat.Diagram.Everything
open import Cat.Functor.Pullback
open import Cat.Instances.Slice
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Functor.FullSubcategory
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Total
open import Cat.Displayed.Functor
open import Cat.Displayed.Composition

import Cat.Reasoning
```

First we note that a CwR is a cartesian category with a class $\cR$ of representable maps,
which is stable under pullback.

```agda
record CwR-structure {o ℓ} r (𝓒 : Precategory o ℓ) : Type (o ⊔ ℓ ⊔ lsuc r) where
    open Cat.Reasoning 𝓒 public

    field
      has-is-lex : Finitely-complete 𝓒
      R          : Wide-subcat {C = 𝓒} r

    open Finitely-complete has-is-lex public

    module R = Wide-subcat R

    field
      R-stable : is-pullback-stable 𝓒 R.P
      f*       : ∀ {A B} → {f : Hom A B} → R.P f → Functor (Slice 𝓒 A) (Slice 𝓒 B)
      f⊣f*     : ∀ {A B} → {f : Hom A B} → (Rf : R.P f) → Base-change pullbacks f ⊣ f* Rf

CwR : ∀ {o ℓ} r → Type (lsuc o ⊔ lsuc ℓ ⊔ lsuc r)
CwR {o} {ℓ} r = Σ (Precategory o ℓ) (CwR-structure r) 
```

We can present the category $CwR(\mathbb{T}, \mathbb{S})$ of CwR morphisms from T to S
as a full subcategory of Lex[C,D]. 


```agda
module _ {o ℓ o' ℓ' r r'} (T : CwR {o} {ℓ} r) (S : CwR {o'} {ℓ'} r') where
  private
    C = T .fst
    D = S .fst
    module T = CwR-structure (T .snd)
    module S = CwR-structure (S .snd)

    module Lex[C,D] = Precategory Lex[ C , D ]

  is-CwR : (F : Lex[C,D].Ob) → Type (o ⊔ ℓ ⊔ r ⊔ r')
  is-CwR F = ∀ {x y} (f : T.Hom x y) → T.R.P f → S.R.P (F₁ f) where open Functor (F .object)

  CwR[_,_] : Precategory (o ⊔ ℓ ⊔ o' ⊔ ℓ' ⊔ r ⊔ r') (o ⊔ ℓ ⊔ ℓ')
  CwR[_,_] = Restrict {C = Lex[ C , D ]} is-CwR

```

```agda

module _ {o ℓ} (S : Precategory o ℓ) where
  module DF = Cat.Reasoning (Discrete-fibrations S)

  -- DFibsUnelem : ∀ {F} → (G : Displayed (∫  (F .fst)) o o) → (Gd : Discrete-fibration G) → DF.Hom F (F .fst D∘ G , discrete∘ (F .snd) Gd)
  -- DFibsUnelem a b = {!   !}

```

```agda
module _ {o ℓ} r {𝓒 : Precategory o ℓ} (C : CwR-structure r 𝓒) (S : Precategory o ℓ) where

  open CwR-structure C

  data IterDFib (X : Ob) : Type (lsuc o ⊔ ℓ)
  Unfold : ∀ {A} → (I : IterDFib A) → Displayed S o o
  
  
  data IterDFib X where
    base   : ∀ (C : Displayed S o o) → Discrete-fibration C → IterDFib X
    extend : ∀ {A} (f : Hom A X) → (idf : IterDFib A) → (C : Displayed (∫ (Unfold idf)) o o) → Discrete-fibration C → IterDFib X

  Unfold (base C x) = C
  Unfold (extend f x C x₁) = Unfold x D∘ C

  Unfold-discrete : ∀ {X} (I : IterDFib X) → Discrete-fibration (Unfold I)
  Unfold-discrete (base C x) = x
  Unfold-discrete (extend f x C Cd) = discrete∘ (Unfold-discrete x) Cd
 
  RIterDFib : Σ _ IterDFib → Type (o ⊔ ℓ)
  RIterDFib (_ , base D _) = Σ[ Extend ∈ Functor S (∫ D) ] (πᶠ D ⊣ Extend)
  RIterDFib (_ , extend f A' B' Bd) = Σ[ Extend ∈ Functor (∫ (Unfold A')) (∫ B') ] (πᶠ B' ⊣ Extend)


  -- record ItDFibs-Ob : Type (lsuc (o ⊔ ℓ)) where
  --   constructor IDF
  --   field 
  --     {a b} : Ob
  --     {f} : Hom a b
  --     dfib : IterDFib b
  --     resp-R : RIterDFib dfib

  -- ItDFibs : Displayed 𝓒 _ _
  -- Displayed.Ob[ ItDFibs ] x = IterDFib x
  -- Displayed.Hom[ ItDFibs ] f A B = Vertical-functor (Unfold A) (Unfold B)
  -- Displayed.Hom[ ItDFibs ]-set f A B = Vertical-functor-is-set S (Unfold-discrete B)
  -- ItDFibs .Displayed.id' = {!   !}
  -- ItDFibs .Displayed._∘'_ = {!   !}
  -- ItDFibs .Displayed.idr' = {!   !}
  -- ItDFibs .Displayed.idl' = {!   !}
  -- ItDFibs .Displayed.assoc' = {!   !}


     
```  