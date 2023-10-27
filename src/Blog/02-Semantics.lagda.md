<!--
```agda
{-# OPTIONS -vimpossible:10 #-}

open import Cat.Prelude 
import Cat.Morphism
import Cat.Instances.Product
open import Cat.Instances.Sets.Complete
open import Cat.CartesianClosed.Instances.PSh 
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Diagram.Exponential
open import Cat.Functor.Base
open import Cat.Functor.Bifunctor
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
import Cat.Reasoning
import Cat.Functor.Hom
import Cat.Functor.Hom.Representable
open import Cat.Strict
open Functor
 
open _=>_
```
-->


 
```agda
module Blog.02-Semantics where
``` 

# Normalisation for the simply typed lambda calculus with Products

The Model... 


```agda
record STLC {ℓ ℓ'} : Type (lsuc (ℓ ⊔ ℓ')) where
  field
    𝓒 : Precategory ℓ ℓ'

  open Precategory 𝓒 public renaming (Ob to Ctx ; Hom to Sub) using ()
  open Cat.Reasoning 𝓒 hiding (_≅_)
  open Cat.Functor.Hom 𝓒 
  open Binary-products (PSh ℓ' 𝓒) (PSh-products {κ = ℓ'} {C = 𝓒}) renaming (⟨_,_⟩ to ×⟨_,_⟩)
  open Cat.Functor.Hom.Representable {C = 𝓒} public
  open Representation
  
  module Ps = Cat.Reasoning (PSh ℓ' 𝓒)
  open Ps._≅_

  field
    𝓒-term :  Terminal 𝓒

  ε : Ctx
  ε = 𝓒-term .Terminal.top

  ⟨⟩ : ∀ Γ → Sub Γ ε
  ⟨⟩ Γ = 𝓒-term .Terminal.has⊤ Γ .is-contr.centre

  ⟨⟩! : ∀ {Γ} (γ : Sub Γ ε) → ⟨⟩ Γ ≡ γ
  ⟨⟩! {Γ} γ i = 𝓒-term .Terminal.has⊤ Γ .paths γ i  
```
Firstly, we have that a model of our stlc is a category that we will specify has
extra structure. As the naming suggests, we usually think of the objects of the
model as contexts and morphisms from $\Gamma \to \Delta$ as subtitutions from
$\Delta$ to $\Gamma$. We also wan't our category to have a Terminal object which
will denote the 'empty' context. The morphisms $⟨⟩ : \Gamma \to \top$ can be thought
of as the statement that a judgement that holds in the empty context must also
hold in some arbritary context $\Gamma$.

```agda
  field  
    Ty : Type ℓ

  field
    𝕋 : Ty → Ps.Ob

  Tm : Ty → Ctx → Type ℓ'
  Tm A Γ = ∣ 𝕋 A .F₀ Γ ∣

  _[_] : ∀ {A Γ Δ} → Tm A Δ → Sub Γ Δ → Tm A Γ
  _[_] {A} t γ = 𝕋 A .F₁ γ t

  _[Id] : ∀ {A Γ} → (t : Tm A Γ) → t [ id ] ≡ t
  t [Id] = λ i → 𝕋 _ .F-id i t
```

We also need a constant set of types that our terms can inhabit. Then we say that 
for each type $\tau$, we want a preasheaf that represents both terms of type $\tau$,
and the action of subtitutions on them. 

Finally, we wan't to model context extension, which is the property that given a context
$\Gamma$ and a type $\tau$, you can build a new context we are calling here $\Gamma ⊕ \tau$.
The natural isomorphism states that you can build a new substitution 
$⟨ \gamma , \tau⟩ : \Gamma \to \Delta ⨁ \tau$ from a substitution
$\gamma : \Gamma \to \Delta$ and a term $\Gamma \vdash t : \tau$. 
The natural iso also neatly packages up the other structure such as the two projections
and the eta rule.


```agda
  field
    extend : Ty → Functor 𝓒 𝓒

  _⊕_ : Ctx → Ty → Ctx
  Γ ⊕ A = extend A .F₀ Γ

  field  
    extension : (Γ : Ctx) (A : Ty) → (Hom[-, Γ ] ⊗₀ 𝕋 A) Ps.≅ Hom[-, Γ ⊕  A ]

  ⟨_,_⟩ : ∀ {Γ Δ A} → Sub Γ Δ → Tm A Γ → Sub Γ (Δ ⊕ A)
  ⟨_,_⟩ {Γ} {Δ} {A} γ a = extension Δ A .to .η Γ (γ , a)

  p : ∀ {Γ Δ A} → Sub Γ (Δ ⊕ A) → Sub Γ Δ
  p {Γ} {Δ} {A} γ = extension Δ A .from .η Γ γ .fst

  q : ∀ {Γ Δ A} → Sub Γ (Δ ⊕ A) → Tm A Γ
  q {Γ} {Δ} {A} γ = extension Δ A .from .η Γ γ .snd

  -- p⟨_,_⟩ : ∀ {Γ Δ A} → (γ : Sub Γ Δ) → (t : Tm A Γ) → p ⟨ γ , t ⟩ ≡ γ
  -- p⟨_,_⟩ {Γ} {Δ} {A} γ t = {!   !} -- extension Δ A .invr i .η Γ (γ , t) .fst

  -- pid : ∀ {Γ Δ A} → (γ : Sub Γ (Δ ⊕ A)) → (p id) ∘ γ ≡ p γ
  -- pid γ = {!   !}

  -- pqη : ∀ {Γ Δ A} → (γ : Sub Γ (Δ ⊕ A)) → ⟨ p γ , q γ ⟩ ≡ γ
  -- pqη {Γ} {Δ} {A} γ i = extension Δ A .invl i .η Γ γ

  -- ⟨_,_⟩∘_ : ∀ {Γ} {Δ} {Ψ} {A} → (γ : Sub Γ Δ) → (t : Tm A Γ) → (δ : Sub Ψ Γ ) → ⟨ γ , t ⟩ ∘ δ ≡ ⟨ γ ∘ δ , t [ δ ] ⟩
  -- ⟨_,_⟩∘_ {Γ} {Δ} {Ψ} {A} γ t δ i = extension Δ A .to .is-natural Γ Ψ δ (~ i) (γ , t) 

  Tm[-⊕_,_] : Ty → Ty → Ps.Ob
  Tm[-⊕ A , B ] = (𝕋 B) F∘ Functor.op (extend A)

``` 

We also would like to have at least function types which behave correctly in regards
to context extension. Again we can package this up rather neatly in terms of natural
isomorphisms of preasheafs.

```agda
record STLC-lam {ℓ ℓ'}  (stlc : STLC {ℓ} {ℓ'}) : Type (lsuc (ℓ ⊔ ℓ')) where
  open STLC stlc
  open Cat.Reasoning 𝓒 hiding (_≅_)

  open Ps._≅_

  field
    _⇒_ : Ty → Ty → Ty
    lamβη : ∀ {A B : Ty} → Tm[-⊕ A , B ] Ps.≅ 𝕋 (A ⇒ B)

  lam : ∀ {Γ} {A B} → Tm B (Γ ⊕ A) → Tm (A ⇒ B) Γ
  lam {Γ} = lamβη .to .η Γ 

  app : ∀ {Γ} {A B} → Tm (A ⇒ B) Γ → Tm B (Γ ⊕ A)
  app {Γ} = lamβη .from .η Γ 

```

```agda
record STLC-prod {ℓ ℓ'} (stlc : STLC {ℓ} {ℓ'}) : Type (lsuc (ℓ ⊔ ℓ')) where
    open STLC stlc
    open Cat.Morphism 𝓒

    open Ps._≅_ public

    open Binary-products (PSh ℓ' 𝓒) (PSh-products {κ = ℓ'} {C = 𝓒}) renaming (⟨_,_⟩ to ×⟨_,_⟩)

    field
      Prod : Ty → Ty → Ty
      prod : ∀ {A B : Ty} → 𝕋 (Prod A B) Ps.≅ (𝕋 A ⊗₀ 𝕋 B)

    _,,_ : ∀ {Γ} {A B} → Tm A Γ → Tm B Γ → Tm (Prod A B) Γ
    x ,, y = prod .from .η _ (x , y)

    proj₁ : ∀ {Γ} {A B} → Tm (Prod A B) Γ → Tm A Γ
    proj₁ p = prod .to .η _ p .fst
     
    proj₂ : ∀ {Γ} {A B} → Tm (Prod A B) Γ → Tm B Γ
    proj₂ p = prod .to .η _ p .snd
```
  

So what might be an example of a model then? The first example you might want to
consider is the so called standard model; also referred to as the meta-circular
interpretation.  

```agda
module StandardModel where
    open import 1Lab.Prelude using (_∘_)
    open Cat.Reasoning (Sets lzero) hiding (_∘_)
    open Cat.Functor.Hom (Sets lzero)
    open Binary-products (Sets lzero) (Sets-products) renaming (⟨_,_⟩ to ×⟨_,_⟩)

    StandardModel : STLC
    StandardModel .STLC.𝓒 = Sets lzero
    StandardModel .STLC.𝓒-term = Sets-terminal
    StandardModel .STLC.Ty = Set lzero
    StandardModel .STLC.𝕋 A = Hom[-, A ] 
    StandardModel .STLC.extend A = Right ×-functor A
    StandardModel .STLC.extension Γ A = to-natural-iso the-iso
        where
            open Binary-products (PSh lzero (Sets lzero)) (PSh-products {κ = lzero} {C = Sets lzero}) 
                    using () renaming (_⊗₀_ to _⊗₀ᴾ_ )
            the-iso : make-natural-iso (Hom[-, Γ ] ⊗₀ᴾ Hom[-, A ]) Hom[-, A ⊗₀ Γ ]
            the-iso .make-natural-iso.eta _ f x = (f .snd x , f .fst x)
            the-iso .make-natural-iso.inv _ f = (snd ∘ f , fst ∘ f)
            the-iso .make-natural-iso.eta∘inv B = funext (λ f →
                (λ x → (fst (f x) , snd (f x))) ≡⟨ ⟨⟩∘ {A} {Γ} {el! (Σ[ v ∈ ∣ A ∣ ] ∣ Γ ∣)} {B} {fst} {snd} f  ⟩
                (λ x →  fst x , snd x) ∘ f      ≡⟨ ap (_∘ f) (⟨⟩-η {A} {Γ}) ⟩
                f                               ∎ 
                )
            the-iso .make-natural-iso.inv∘eta B = funext (λ f → refl)
            the-iso .make-natural-iso.natural x y f = refl
```

```agda
    StandardModel-lam : STLC-lam StandardModel
    StandardModel-lam .STLC-lam._⇒_ A B = el! (Hom A B)
    StandardModel-lam .STLC-lam.lamβη {A} {B} = to-natural-iso the-iso where
      open STLC StandardModel
      open STLC-lam
      the-iso : make-natural-iso Tm[-⊕ A , B ] Hom[-, _ ]
      the-iso .make-natural-iso.eta _ f x a = f (a , x)
      the-iso .make-natural-iso.inv _ f (a , x) = f x a
      the-iso .make-natural-iso.eta∘inv _ = refl
      the-iso .make-natural-iso.inv∘eta _ = refl
      the-iso .make-natural-iso.natural _ _ _ = refl

```

```agda
    StandardModel-prod : STLC-prod StandardModel
    StandardModel-prod .STLC-prod.Prod A B = el! (∣ A ∣ × ∣ B ∣)
    StandardModel-prod .STLC-prod.prod = to-natural-iso the-iso where
       the-iso : make-natural-iso _ _
       the-iso .make-natural-iso.eta _ f = (fst ∘ f , snd ∘ f)
       the-iso .make-natural-iso.inv _ f x = fst f x , snd f x
       the-iso .make-natural-iso.eta∘inv _ = refl
       the-iso .make-natural-iso.inv∘eta _ = refl
       the-iso .make-natural-iso.natural _ _ _ = refl  
```  

So there isn't really any special properties about sets that we used aside from 
it's cartesian closure and so it's fairly trivial to extend this to a model for
any cartesian category. 

```agda
module CCC {ℓ} (𝓒 : Precategory ℓ ℓ) 
       (𝓒-term : Terminal 𝓒) (𝓒-prod : has-products 𝓒)
       (𝓒cc : Cartesian-closed 𝓒 𝓒-prod 𝓒-term) where

  open Cat.Reasoning 𝓒
  open Cat.Functor.Hom 𝓒
  open Binary-products 𝓒 𝓒-prod
  
  model : STLC
  model .STLC.𝓒 = 𝓒
  model .STLC.𝓒-term = 𝓒-term
  model .STLC.Ty = Ob
  model .STLC.𝕋 A = Hom[-, A ]
  model .STLC.extend = Right ×-functor
  model .STLC.extension Γ A = to-natural-iso the-iso  where 
    open Binary-products (PSh ℓ 𝓒) (PSh-products {κ = ℓ} {C = 𝓒}) 
            using () renaming (_⊗₀_ to _⊗₀ᴾ_ )
    open Product (𝓒-prod A Γ) using (π₂∘factor ; π₁∘factor)
    the-iso : make-natural-iso (Hom[-, Γ ] ⊗₀ᴾ Hom[-, A ]) Hom[-, A ⊗₀ Γ ]
    the-iso .make-natural-iso.eta _ (γ , t) = ⟨ t , γ ⟩
    the-iso .make-natural-iso.inv _ ΓA = (π₂ ∘ ΓA , π₁ ∘ ΓA)
    the-iso .make-natural-iso.eta∘inv _ = funext λ x → ⟨ π₁ ∘ x , π₂ ∘ x ⟩ ≡⟨ sym (⟨⟩∘ x) ⟩
                                                      ⟨ π₁ , π₂ ⟩ ∘ x    ≡⟨ ⟨⟩-η ⟩∘⟨refl ⟩
                                                      id ∘ x             ≡⟨ idl x ⟩
                                                      x ∎
    the-iso .make-natural-iso.inv∘eta _ = funext λ _ → ap₂ _,_ π₂∘factor π₁∘factor
    the-iso .make-natural-iso.natural _ _ ΓA = funext λ _ → ⟨⟩∘ ΓA
  
```

An important example of a CCC are preasheafs and this will become important later.

For now we want to define a category $\cW$ - standing for weakenings - that the
paper describes as 'generalising the notion of subsequence on contexts'. 

```agda
module Weakenings {ℓ} (𝓢 : STLC {ℓ} {ℓ}) where

  open STLC 𝓢
  open Cat.Reasoning 𝓒 hiding (_≅_)

  open Ps._≅_

  data Wk : Ctx → Ctx → Type ℓ where 
    wid : ∀ {Γ} → Wk Γ Γ
    _∘w_ : ∀ {Γ Δ Σ} → Wk Δ Σ → Wk Γ Δ → Wk Γ Σ

    widl : ∀ {Γ Δ} (f : Wk Γ Δ) → wid ∘w f ≡ f
    widr : ∀ {Γ Δ} (f : Wk Γ Δ) → f ∘w wid ≡ f
    wassoc : ∀ {Γ Δ Σ Ψ} (f : Wk Σ Ψ) (g : Wk Δ Σ) (h : Wk Γ Δ) → 
              f ∘w (g ∘w h) ≡ (f ∘w g) ∘w h

    drop : ∀ {Γ Δ} {A} → Wk Γ Δ → Wk (Γ ⊕ A) Δ
    keep : ∀ {Γ Δ} {A} → Wk Γ Δ → Wk (Γ ⊕ A) (Δ ⊕ A)

    drop∘ : ∀ {Γ Δ Σ} {A} (f : Wk Δ Σ) (g : Wk Γ Δ) → f ∘w  (drop g) ≡ drop {A = A} (f ∘w g)
    drop∘keep : ∀ {Γ Δ Σ} {A} (f : Wk Δ Σ) (g : Wk Γ Δ) → (drop f) ∘w (keep g) ≡ drop {A = A} (f ∘w g)
    keep∘keep : ∀ {Γ Δ Σ} {A} (f : Wk Δ Σ) (g : Wk Γ Δ)
                 → (keep f) ∘w (keep g) ≡ keep {A = A} (f ∘w g)

    has-is-set : ∀ Γ Δ → is-set (Wk Γ Δ)

```
  this forms a category trivially

```agda
  𝓦 : Precategory ℓ ℓ
  𝓦 .Precategory.Ob = Ctx
  𝓦 .Precategory.Hom = Wk
  𝓦 .Precategory.Hom-set = has-is-set
  𝓦 .Precategory.id = wid
  𝓦 .Precategory._∘_ = _∘w_
  𝓦 .Precategory.idr = widr
  𝓦 .Precategory.idl = widl
  𝓦 .Precategory.assoc = wassoc

  𝓦-term : Terminal 𝓦
  𝓦-term .Terminal.top = ε
  𝓦-term .Terminal.has⊤ x = contr {! drop  !} {!   !}

  module PsW = Precategory (PSh ℓ 𝓦)
  module W   = Cat.Reasoning 𝓦

```
We can also define a faithfull embedding back into $\cC$.
```agda
   
  e : ∀ {Γ Δ} → Wk Γ Δ → Sub Γ Δ
  e wid = id
  e (f ∘w g) = e f ∘ e g
  e (widl x i) = idl (e x) i
  e (widr x i) = idr (e x) i
  e (wassoc f g h i) = assoc (e f) (e g) (e h) i
  e (drop x) = extension _ _ .from .η _ (extend _ .F₁ (e x)) .fst
  e (keep x) = extend _ .F₁ (e x) 
  e {_} {Σ} (drop∘ {Γ} {Δ} x y i) = {! extension Γ _ .from .is-natural _ _ (extend _ .F₁ (e x)) i ?  !}
  e (drop∘keep x y i) = {!   !}
  e (keep∘keep x y i) = extend _ .F-∘ (e x) (e y) (~ i)
  e (has-is-set Γ Δ ρ σ P Q i j) = Hom-set Γ Δ (e ρ) (e σ)
                                   (λ i → e (P i)) (λ i → e (Q i)) i j

  E : Functor 𝓦 𝓒
  E .F₀ x = x
  E .F₁ = e
  E .F-id = refl
  E .F-∘ f g = refl  

  -- E-faithful : is-faithful E
  -- E-faithful {_} {_} {f} {g} P = {!   !}
  
```

We now define the normal and neutral terms inductively for an arbritary model and 
show that there is an embedding back into $\cC$.  

```agda
module Normals {ℓ} (S : STLC {ℓ} {ℓ})
               (sprod : STLC-prod S) (slam : STLC-lam S)
  where

  open STLC S
  open Cat.Reasoning 𝓒
  open STLC-lam slam
  open STLC-prod sprod

  variable
    Γ Δ : Ctx
    A B : Ty

  data Var : Ctx → Ty → Type ℓ where
    vz : Var (Γ ⊕ A) A
    vs : Var Γ A → Var (Γ ⊕ B) A

  data Nf : Ctx → Ty → Type ℓ
  data Ne : Ctx → Ty → Type ℓ

  data Nf where
    `ne : Ne Γ A → Nf Γ A
    `lam : Nf (Γ ⊕ A) B → Nf Γ (A ⇒ B)
    `pair : Nf Γ A → Nf Γ B → Nf Γ (Prod A B) 

  data Ne where
    `app : Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    `var : Var Γ A → Ne Γ A
    `fst : Ne Γ (Prod A B) → Ne Γ A
    `snd : Ne Γ (Prod A B) → Ne Γ B

  ⌜_⌝nf : Nf Γ A → Tm A Γ
  ⌜_⌝ne : Ne Γ A → Tm A Γ
  
  ⌜ `ne x ⌝nf = ⌜ x ⌝ne
  ⌜ `lam x ⌝nf = lam ⌜ x ⌝nf
  ⌜ `pair x y ⌝nf = ⌜ x ⌝nf ,, ⌜ y ⌝nf
  ⌜ `app f x ⌝ne = app ⌜ f ⌝ne [ ⟨ id , ⌜ x ⌝nf ⟩ ]
  ⌜ `var v ⌝ne = aux v where
      aux : Var Γ A → Tm A Γ
      aux vz = q id
      aux (vs v) = aux v [ p id ]
  ⌜ `fst x ⌝ne = proj₁ ⌜ x ⌝ne
  ⌜ `snd x ⌝ne = proj₂ ⌜ x ⌝ne
   
  open Weakenings S

  _[_]wV : Var Γ A → W.Hom Δ Γ → Var Δ A
  v [ Weakenings.wid ]wV = v
  v [ γ Weakenings.∘w δ ]wV = (v [ γ ]wV) [ δ ]wV
  v [ Weakenings.widl γ i ]wV = v [ γ ]wV
  v [ Weakenings.widr γ i ]wV = v [ γ ]wV
  v [ Weakenings.wassoc γ γ₁ γ₂ i ]wV = ((v [ γ ]wV) [ γ₁ ]wV) [ γ₂ ]wV
  v [ Weakenings.drop γ ]wV = {!   !}
  v [ Weakenings.keep γ ]wV = {! v  !}
  v [ Weakenings.drop∘ γ γ₁ i ]wV = {!   !}
  v [ Weakenings.drop∘keep γ γ₁ i ]wV = {!   !}
  v [ Weakenings.keep∘keep γ γ₁ i ]wV = {!   !}
  v [ Weakenings.has-is-set Γ Δ γ γ₁ x y i i₁ ]wV = {!   !}

  _[_]wNe : Ne Γ A → W.Hom Δ Γ → Ne Δ A
  _[_]wNf : Nf Γ A → W.Hom Δ Γ → Nf Δ A
  `app f x [ ρ ]wNe = `app (f [ ρ ]wNe) (x [ ρ ]wNf)
  `var v [ ρ ]wNe = `var (v [ ρ ]wV)
  `fst x [ ρ ]wNe = `fst (x [ ρ ]wNe)
  `snd x [ ρ ]wNe = `snd (x [ ρ ]wNe)
  `ne x [ ρ ]wNf = `ne (x [ ρ ]wNe)
  `lam x [ ρ ]wNf = `lam (x [ keep ρ ]wNf)
  `pair x y [ ρ ]wNf = `pair (x [ ρ ]wNf) (y [ ρ ]wNf)


  NE : Ty → PsW.Ob
  NE A .F₀ Γ = el (Ne Γ A) {!   !}
  NE A .F₁ = {!   !}
  NE A .F-id = {!   !}
  NE A .F-∘ = {!   !}
  
  NF : Ty → PsW.Ob
  NF A = {!   !}

```


Now for the bulk of this formalization we will assume that there exists
an initial object in the category of models

```agda
module withInitial {ℓ} (Tm : STLC {ℓ} {ℓ}) 
  (⟦-⟧ : ∀ s → s .STLC.Ctx → Functor (Tm .STLC.𝓒) (s .STLC.𝓒)) where 
```
 
We now introduce a functor 

```agda
module Syntax {ℓ} (𝓑 : Precategory ℓ ℓ) where
```  
 
Now we consider the free model generated by an underlying category 
$\c{B}$ of base types and constants. We can show that this is initial
in the category of models. The free model also happens to be the syntax
of the simply typed lambda calculus!!  