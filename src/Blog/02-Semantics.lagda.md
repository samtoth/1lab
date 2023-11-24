<!--
```agda
{-# OPTIONS -vimpossible:10 #-}

open import Cat.Prelude 
import Cat.Morphism
import Cat.Instances.Product
open import Cat.Instances.Sets.Complete
open import Cat.Instances.Functor
open import Cat.Instances.Lift
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

  p⟨_,_⟩ : ∀ {Γ Δ A} → (γ : Sub Γ Δ) → (t : Tm A Γ) → p ⟨ γ , t ⟩ ≡ γ
  p⟨_,_⟩ {Γ} {Δ} {A} γ t = {! happly (extension Δ A .invr) !} -- extension Δ A .invr i .η Γ (γ , t) .fst

  q⟨_,_⟩ : ∀ {Γ Δ A} → (γ : Sub Γ Δ) → (t : Tm A Γ) → q ⟨ γ , t ⟩ ≡ t
  q⟨_,_⟩ γ t = {! extension _ _ .invl  !}

  pid : ∀ {Γ Δ A} → (γ : Sub Γ (Δ ⊕ A)) → (p id) ∘ γ ≡ p γ
  pid γ = sym (ap fst (happly (extension _ _ .from .is-natural _ _ γ) id)) 
        ∙ ap (λ x → fst (extension _ _ .from .η _ x)) (idl _)

  qid : ∀ {Γ Δ A} → (γ : Sub Γ (Δ ⊕ A)) → (q id) [ γ ] ≡ q γ
  qid γ = sym (ap snd (happly (extension _ _ .from .is-natural _ _ γ) id)) 
           ∙ ap (λ x → snd (extension _ _ .from .η _ x)) (idl _)

  pqη : ∀ {Γ Δ A} → (γ : Sub Γ (Δ ⊕ A)) → ⟨ p γ , q γ ⟩ ≡ γ
  pqη {Γ} {Δ} {A} γ = {! ap η (extension Δ A .invl)  !} -- extension Δ A .invl i .η Γ γ

  ⟨_,_⟩∘_ : ∀ {Γ} {Δ} {Ψ} {A} → (γ : Sub Γ Δ) → (t : Tm A Γ) → (δ : Sub Ψ Γ ) → ⟨ γ , t ⟩ ∘ δ ≡ ⟨ γ ∘ δ , t [ δ ] ⟩
  ⟨_,_⟩∘_ {Γ} {Δ} {Ψ} {A} γ t δ i = extension Δ A .to .is-natural Γ Ψ δ (~ i) (γ , t) 

  weaken : ∀ {Γ Δ A} → Sub Γ Δ → Sub (Γ ⊕ A) Δ
  weaken x = p (extend _ .F₁ x)

  weakenId : ∀ {Γ A} → weaken {Γ} {Γ} {A} id ≡ p id
  weakenId = ap (λ x → fst (extension _ _ .Cat.Morphism.from .η _ x)) (extend _ .F-id)

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

(for convinience I am going to package the data for a CCC up.)

```agda
record CCC o ℓ : Type (lsuc (o ⊔ ℓ)) where
    constructor ccc
    field 𝓒 : Precategory o ℓ
    field term : Terminal 𝓒
    field prod : has-products 𝓒
    field closed : Cartesian-closed 𝓒 prod term

    open Binary-products 𝓒 prod public hiding (unique₂)
    open Terminal term public
    open Cartesian-closed closed public
```


```agda
CCC→STLC : ∀ {o ℓ} → CCC o ℓ → Σ STLC STLC-lam
CCC→STLC {o} {ℓ} C = model , {!   !} where
  open CCC C using (𝓒;term;prod)
  open Cat.Reasoning (Lift-cat o (o ⊔ ℓ) 𝓒)
  open Cat.Functor.Hom (Lift-cat o (o ⊔ ℓ) 𝓒)  

  lift-term : Terminal (Lift-cat o (o ⊔ ℓ) 𝓒)
  lift-term .Terminal.top = lift (term .Terminal.top)
  lift-term .Terminal.has⊤ (lift x) =  contr (lift (Terminal.! term)) 
                                         λ where (lift f) → ap lift (Terminal.!-unique term f)

  lift-prod : has-products (Lift-cat o (o ⊔ ℓ) 𝓒)
  lift-prod (lift a) (lift b) = p where
    module Pr = Product (prod a b)
    p : Product _ _ _
    p .Product.apex = lift Pr.apex
    p .Product.π₁ = lift Pr.π₁
    p .Product.π₂ = lift Pr.π₂
    p .Product.has-is-product .is-product.⟨_,_⟩ (lift f) (lift g) = lift Pr.⟨ f , g ⟩
    p .Product.has-is-product .is-product.π₁∘factor {Q = lift Q} {p1 = lift p1} {lift p2}
         = ap lift (Pr.π₁∘factor {p1 = p1} {p2})
    p .Product.has-is-product .is-product.π₂∘factor {Q = lift Q} {p1 = lift p1} {lift p2}
         = ap lift (Pr.π₂∘factor {p1 = p1} {p2})
    p .Product.has-is-product .is-product.unique {p1 = lift p1} {lift p2} (lift f) P Q
         = ap lift (Pr.unique f {!   !} {!   !})

  open Binary-products (Lift-cat o (o ⊔ ℓ) 𝓒)  lift-prod hiding (unique₂)
  open Terminal lift-term

  model : STLC
  model .STLC.𝓒 = Lift-cat o (o ⊔ ℓ) 𝓒
  model .STLC.𝓒-term = lift-term
  model .STLC.Ty = Ob
  model .STLC.𝕋 A = Hom[-, A ]
  model .STLC.extend = Right ×-functor
  model .STLC.extension Γ A = to-natural-iso the-iso  where 
    open Binary-products (PSh (o ⊔ ℓ) (Lift-cat o (o ⊔ ℓ) 𝓒))
             (PSh-products {κ = o ⊔ ℓ} {C = Lift-cat o (o ⊔ ℓ) 𝓒}) 
            using () renaming (_⊗₀_ to _⊗₀ᴾ_ )
    open Product (lift-prod A Γ) using (π₂∘factor ; π₁∘factor)
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

We can go the other way - from our STLC model to a CCC. 

```agda
module Democratic {o ℓ} (S : STLC {o} {o ⊔ ℓ}) where

  open STLC S hiding (Ctx ; Sub)
  open Cat.Reasoning 𝓒
  open Terminal 𝓒-term

  data Ctx : Type o where
    ∅ : Ctx
    Cons : Ctx → Ty → Ctx

  mapCtx : (A : Ty → Ty) → Ctx → Ctx
  mapCtx A ∅ = ∅ 
  mapCtx A (Cons Γ t) = Cons (mapCtx A Γ) (A t) 

  embedCtx : Ctx → Ob
  embedCtx ∅ = ε
  embedCtx (Cons x a) = embedCtx x ⊕ a 

  data Subst (Γ : Ctx) : Ctx → Type (o ⊔ ℓ) where
    nill : Subst Γ ∅
    extendS : ∀ {Δ} {A} → Subst Γ Δ → Tm A (embedCtx Γ) → Subst Γ (Cons Δ A)


  embedSubst : ∀ {Γ Δ} → Subst Γ Δ → Hom (embedCtx Γ) (embedCtx Δ)
  embedSubst nill = ⟨⟩ _
  embedSubst (extendS s f) = ⟨ embedSubst s , f ⟩

  w1 : ∀ {Γ Δ} {A} → Subst Γ Δ → Subst (Cons Γ A) Δ
  w1 nill = nill
  w1 (extendS γ x) = extendS (w1 γ) (x [ p id ])

  w2 : ∀ {Γ Δ A} → Subst Γ Δ → Subst (Cons Γ A) (Cons Δ A)
  w2 γ = extendS (w1 γ) (q id)

  Sid : ∀ {Γ} → Subst Γ Γ
  Sid {∅} = nill
  Sid {Cons Γ x} = w2 Sid

  _∘s_ : ∀ {Γ Δ Σ} → Subst Δ Σ → Subst Γ Δ → Subst Γ Σ
  nill ∘s δ = nill
  extendS γ f ∘s δ = extendS (γ ∘s δ) (f [ embedSubst δ ])

  embedP1 : ∀ {Γ Δ A} (f : Subst Γ Δ) → embedSubst (w1 {A = A} f) ≡ weaken (embedSubst f) 
  embedP1 nill = has⊤ _ .paths _
  embedP1 (extendS f x) = ap ⟨_, _ ⟩ (embedP1 f) ∙ {!   !}

  embedId : ∀ {Γ} → embedSubst (Sid {Γ}) ≡ id
  embedId {∅} = has⊤ top .paths id
  embedId {Cons Γ A} = ap ⟨_, q id ⟩ (embedP1 {Γ} Sid ∙ ap weaken (embedId {Γ}) ∙ weakenId) ∙ pqη id

  Sidr : ∀ {Γ Δ} → (f : Subst Γ Δ) → (f ∘s Sid) ≡ f
  Sidr nill = refl
  Sidr {Γ} (extendS f x) = ap₂ extendS (Sidr f) (ap (x [_]) (embedId {Γ}) ∙ (happly (𝕋 _ .F-id) x))

  wk1Extend : ∀ {Γ Δ Σ A} {x} (f : Subst Δ Σ) {g : Subst Γ Δ}
              → w1 {A = A} f ∘s extendS g x ≡ f ∘s g
  wk1Extend nill = refl
  wk1Extend (extendS f x) = ap₂ extendS (wk1Extend f)
             (sym (happly (𝕋 _ .F-∘ _ _) _) ∙ ap (x [_]) (pid _ ∙ p⟨ _ , _ ⟩))
 
  Sidl : ∀ {Γ Δ} → (f : Subst Γ Δ) → Sid {Δ} ∘s f ≡ f
  Sidl nill = refl
  Sidl {Γ} {Cons Δ A} (extendS f x) = ap₂ extendS (wk1Extend Sid ∙ Sidl f) (qid _ ∙ q⟨ _ , _ ⟩)

  embed∘ : ∀ {Γ Δ Σ} (f : Subst Δ Σ) (g : Subst Γ Δ)
            → embedSubst (f ∘s g) ≡ embedSubst f ∘ embedSubst g
  embed∘ nill g = has⊤ _ .paths _
  embed∘ (extendS f x) g = (ap ⟨_, _ ⟩) (embed∘ f g) ∙ sym (⟨ _ , _ ⟩∘ _)

  Sassoc : ∀ {Γ Δ Σ Ψ} (f : Subst Σ Ψ) (g : Subst Δ Σ) (h : Subst Γ Δ) 
            → f ∘s (g ∘s h) ≡ (f ∘s g) ∘s h
  Sassoc nill g h = refl
  Sassoc (extendS f x) g h = ap₂ extendS (Sassoc f g h) (ap (x [_]) (embed∘ g h) ∙ happly (𝕋 _ .F-∘ _ _) x)

  𝓒d : Precategory o (o ⊔ ℓ)
  𝓒d .Precategory.Ob = Ctx
  𝓒d .Precategory.Hom = Subst
  𝓒d .Precategory.Hom-set = {!   !}
  𝓒d .Precategory.id = Sid
  𝓒d .Precategory._∘_ = _∘s_
  𝓒d .Precategory.idr = Sidr
  𝓒d .Precategory.idl = Sidl
  𝓒d .Precategory.assoc = Sassoc
    
  open Cat.Functor.Hom 𝓒  
  
  -- this functor is faithful too
  embedF : Functor 𝓒d 𝓒
  embedF .F₀ = embedCtx
  embedF .F₁ = embedSubst
  embedF .F-id {Γ} = embedId {Γ}
  embedF .F-∘ = embed∘

  dTerm : Terminal 𝓒d
  dTerm .Terminal.top = ∅
  dTerm .Terminal.has⊤ f = contr nill (λ where nill → refl)

  w1∘w2 : ∀ {Γ Δ Σ A} (f : Subst Δ Σ) (g : Subst Γ Δ)
        → w1 {A = A} (f ∘s g) ≡ w1 f ∘s w2 g
  w1∘w2 nill g = refl
  w1∘w2 (extendS f x) g = ap₂ extendS (w1∘w2 f g) {!   !}
      -- (sym ( sym (assoc x _ _) ∙ (refl⟩∘⟨ π₁∘⟨⟩ ∙ embedP1 g) ∙ assoc _ _ _))

  w2∘ : ∀ {Γ Δ Σ A} (f : Subst Δ Σ) (g : Subst Γ Δ)
        → w2 {A = A} (f ∘s g) ≡ extendS (w1 f ∘s w2 g) (q id)
  w2∘ f g = ap₂ extendS (w1∘w2 f g) refl
  
  dExtend : Ty → Functor 𝓒d 𝓒d
  dExtend A .F₀ Γ = Cons Γ A
  dExtend A .F₁ f = w2 f
  dExtend A .F-id = refl
  dExtend A .F-∘ f g = w2∘ f g ∙ ap (extendS _) (sym (qid _ ∙ q⟨ _ , _ ⟩))

  dModel : STLC
  dModel .STLC.𝓒 = 𝓒d
  dModel .STLC.𝓒-term = dTerm
  dModel .STLC.Ty = Ty
  dModel .STLC.𝕋 A = 𝕋 A F∘ Functor.op embedF
  dModel .STLC.extend = dExtend
  dModel .STLC.extension Γ A = to-natural-iso the-iso where
    the-iso : make-natural-iso _ _
    the-iso .make-natural-iso.eta Δ (f , g)  = extendS f g
    the-iso .make-natural-iso.inv Δ (extendS f x) = f , x
    the-iso .make-natural-iso.eta∘inv Δ i (extendS f x) = extendS f x
    the-iso .make-natural-iso.inv∘eta Δ i (f , x) = f , x 
    the-iso .make-natural-iso.natural _ _ f i (g , x) = extendS (g ∘s f) (𝕋 A .F₁ (embedSubst f) x)
  

  -- dLam : STLC-lam dModel
  -- dLam .STLC-lam._⇒_ = Exp.B^A
  -- dLam .STLC-lam.lamβη = to-natural-iso the-iso where
  --   the-iso : make-natural-iso _ _
  --   the-iso .make-natural-iso.eta Γ = ƛ
  --   the-iso .make-natural-iso.inv Γ = unlambda
  --   the-iso .make-natural-iso.eta∘inv Γ = funext (equiv→counit lambda-is-equiv)
  --   the-iso .make-natural-iso.inv∘eta Γ = funext (equiv→unit lambda-is-equiv)
  --   the-iso .make-natural-iso.natural Γ Δ f = funext λ where x → unique (ƛ x ∘ embedSubst f) {! commutes _   !}

  -- dProd : STLC-prod dModel
  -- dProd .STLC-prod.Prod = {!   !}
  -- dProd .STLC-prod.prod = {!   !}

```

For now we want to define a category $\cW$ - standing for weakenings - that the
paper describes as 'generalising the notion of subsequence on contexts'. 

```agda
module Weakenings {o ℓ} (S : STLC {o} {o ⊔ ℓ}) where

  open Democratic {o} {ℓ} S hiding (Ctx; Subst)
  open STLC dModel
  open Cat.Reasoning 𝓒 hiding (_≅_)

  -- open Ps._≅_

  data Wk : Ctx → Ctx → Type (o ⊔ ℓ) where 
    stop : ∀ {Γ} → Wk Γ Γ
    drop : ∀ {Γ Δ} {A} → Wk Γ Δ → Wk (Γ ⊕ A) Δ
    keep : ∀ {Γ Δ} {A} → Wk Γ Δ → Wk (Γ ⊕ A) (Δ ⊕ A)

  _∘w_ : ∀ {Γ Δ Σ} → Wk Δ Σ → Wk Γ Δ → Wk Γ Σ
  ρ ∘w stop = ρ
  ρ ∘w drop σ = drop (ρ ∘w σ)
  stop ∘w keep {Γ} {Δ} {A} σ = keep σ
  drop ρ ∘w keep {Γ} {Δ} {A} σ = drop (ρ ∘w σ)
  keep ρ ∘w keep {Γ} {Δ} {A} σ = keep (ρ ∘w σ)

  widl : ∀ {Γ Δ} → (f : Wk Γ Δ) → stop ∘w f ≡ f
  widl stop = refl
  widl (drop f) = ap drop (widl f)
  widl (keep f) = refl

  wassoc : ∀ {Γ Δ Σ Ψ} (f : Wk Σ Ψ) (g : Wk Δ Σ) (h : Wk Γ Δ)
           → f ∘w (g ∘w h) ≡ (f ∘w g) ∘w h
  wassoc f g stop = refl
  wassoc f g (drop h) = ap drop (wassoc f g h)
  wassoc f stop (keep h) = refl
  wassoc f (drop g) (keep h) = ap drop (wassoc f g h)
  wassoc stop (keep g) (keep h) = refl
  wassoc (drop f) (keep g) (keep h) = ap drop (wassoc f g h)
  wassoc (keep f) (keep g) (keep h) = ap keep (wassoc f g h)
  
  Wk-is-set : ∀ Γ Δ → is-set (Wk Γ Δ)
  Wk-is-set = {!   !}
```
  this forms a category trivially

```agda
  𝓦 : Precategory o (o ⊔ ℓ)
  𝓦 .Precategory.Ob = Ctx
  𝓦 .Precategory.Hom = Wk
  𝓦 .Precategory.Hom-set = Wk-is-set
  𝓦 .Precategory.id = stop
  𝓦 .Precategory._∘_ = _∘w_
  𝓦 .Precategory.idr _ = refl
  𝓦 .Precategory.idl = widl
  𝓦 .Precategory.assoc = wassoc

  term : ∀ {Γ} → Wk Γ ε
  term {∅} = stop
  term {Cons Γ x} = drop term

  term! : ∀ {Γ} (f : Wk Γ ∅) → term ≡ f
  term! stop = refl
  term! (drop f) = ap drop (term! f) 

  𝓦-term : Terminal 𝓦
  𝓦-term .Terminal.top = ε
  𝓦-term .Terminal.has⊤ x = contr term term!

  module PsW = Precategory (PSh (o ⊔ ℓ) 𝓦)
  module W   = Cat.Reasoning 𝓦

```
We can also define a faithfull embedding back into $\cC$.
```agda
   
  e : ∀ {Γ Δ} → Wk Γ Δ → Hom Γ Δ
  e stop = id
  e (drop f) = e f ∘ w1 id
  e (keep f) = w2 (e f)

  extendw1 : ∀ {Γ Δ A} (f : Wk Γ Δ) → w1 {A = A} (e f) ≡ e f ∘ w1 Sid
  extendw1 stop = sym (idl _)
  extendw1 (drop f) = w1∘w2 _ _ ∙ (extendw1 f ⟩∘⟨refl) ∙ sym (Sassoc _ _ _) ∙ (refl⟩∘⟨ sym (w1∘w2 _ _) ∙ (ap w1 (Sidl _))) ∙ {!   !}
  extendw1 (keep f) = {!   !}

  e∘ : ∀ {Γ Δ Σ} (f : Wk Δ Σ) (g : Wk Γ Δ)
       → e (f ∘w g) ≡ e f ∘ e g
  e∘ f stop = sym (idr (e f))
  e∘ f (drop g) = (e∘ f g ⟩∘⟨refl) ∙ sym (assoc _ _ _)
  e∘ stop (keep g) = ap w2 (sym (idl _)) ∙ w2∘ id (e g) ∙ ap₂ extendS refl (sym (qid _ ∙ q⟨ _ , _ ⟩))
  e∘ (drop f) (keep g) = (e∘ f g ⟩∘⟨refl) ∙ sym (sym (assoc _ _ _)
                       ∙ (refl⟩∘⟨ (sym (w1∘w2 _ _) ∙ ap w1 (idl _) ∙ extendw1 g)) ∙ assoc _ _ _)
  e∘ (keep f) (keep g) = ap  w2 (e∘ f g) ∙ w2∘ (e f) (e g) ∙ ap₂ extendS refl (sym (qid _ ∙ q⟨ _ , _ ⟩))

  E : Functor 𝓦 𝓒
  E .F₀ x = x
  E .F₁ = e
  E .F-id = refl
  E .F-∘ = e∘

  -- E-faithful : is-faithful E
  -- E-faithful {_} {_} {f} {g} P = {!   !}
  

  Yw : Ob → PsW.Ob
  Yw o = C.Hom[-, o ] F∘ Functor.op E 
    where module C = Cat.Functor.Hom 𝓒
          
  𝕋W : Ty → PsW.Ob
  𝕋W t = 𝕋 t F∘ Functor.op E


```

We now define the normal and neutral terms inductively for an arbritary model and 
show that there is an embedding back into $\cC$.  

```agda
module Normals {o ℓ} (S : STLC {o} {o ⊔ ℓ}) (slam : STLC-lam S) (sprod : STLC-prod S) where
  open STLC S hiding (𝓒;Ctx)
  module SC = Precategory (S .STLC.𝓒)
  open Democratic {o} {ℓ} S renaming (𝓒d to 𝓒)
  open Cat.Reasoning 𝓒
  open STLC-lam slam
  open STLC-prod sprod

  variable
    Γ Δ : Ctx
    A B : Ty

  data Var : Ctx → Ty → Type o where
    vz : Var (Cons Γ A) A
    vs : Var Γ A → Var (Cons Γ B) A

  data Nf : Ctx → Ty → Type (o ⊔ ℓ)
  data Ne : Ctx → Ty → Type (o ⊔ ℓ)

  data Nf where
    `ne : Ne Γ A → Nf Γ A
    `lam : Nf (Cons Γ A) B → Nf Γ (A ⇒ B)
    `pair : Nf Γ A → Nf Γ B → Nf Γ (Prod A B) 

  data Ne where
    `app : Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    `var : Var Γ A → Ne Γ A
    `fst : Ne Γ (Prod A B) → Ne Γ A
    `snd : Ne Γ (Prod A B) → Ne Γ B

  ⌜_⌝nf : Nf Γ A → Tm A (embedCtx Γ)
  ⌜_⌝ne : Ne Γ A → Tm A (embedCtx Γ)
  
  ⌜_⌝nf {Γ} (`ne x) = ⌜ x ⌝ne
  ⌜_⌝nf {Γ} (`lam x) = lam   ⌜ x ⌝nf
  ⌜_⌝nf {Γ} (`pair x y) = _,,_  ⌜ x ⌝nf ⌜ y ⌝nf
  ⌜_⌝ne {Γ} (`app f x) = _[_] {_}  {_} (app {_} {_} {_} ⌜ f ⌝ne) ⟨ SC.id , ⌜ x ⌝nf ⟩
  ⌜_⌝ne {Γ} (`fst {_} {A} {B} x) = proj₁ {_} {A} {B} ⌜ x ⌝ne
  ⌜_⌝ne {Γ} (`snd {_} {A} {B} x) = proj₂ {_} {A} {B} ⌜ x ⌝ne
  ⌜ `var v ⌝ne = aux v where
      aux : Var Γ A → Tm A (embedCtx Γ)
      aux {Γ = Γ} vz = q {_} SC.id
      aux {Γ = Γ} (vs v) = _[_] {_} {_} (aux v) (p {_} SC.id)
   
  open Weakenings {o} {ℓ} S

  _[_]wV : Var Γ A → W.Hom Δ Γ → Var Δ A
  v [ Weakenings.stop ]wV = v
  v [ Weakenings.drop γ ]wV = vs (v [ γ ]wV)
  vz [ Weakenings.keep γ ]wV = vz
  vs v [ Weakenings.keep γ ]wV = vs (v [ γ ]wV)

  _[_]wNe : Ne Γ A → W.Hom Δ Γ → Ne Δ A
  _[_]wNf : Nf Γ A → W.Hom Δ Γ → Nf Δ A
  `app f x [ ρ ]wNe = `app (f [ ρ ]wNe) (x [ ρ ]wNf)
  `var v [ ρ ]wNe = `var (v [ ρ ]wV)
  `fst {B = B} x [ ρ ]wNe = `fst {B = B} (x [ ρ ]wNe)
  `snd {A = A} x [ ρ ]wNe = `snd {A = A} (x [ ρ ]wNe)
  `ne x [ ρ ]wNf = `ne (x [ ρ ]wNe)
  `lam x [ ρ ]wNf = `lam (x [ keep ρ ]wNf)
  `pair x y [ ρ ]wNf = `pair (x [ ρ ]wNf) (y [ ρ ]wNf)

  _[keepstop]nfId : ∀ {Γ A B} (f : Nf (Cons Γ A) B)
                      → (f [ keep stop ]wNf) ≡ f
  _[keepstop]nfId {Γ} f = {!      !}

  _[Id]wNe : ∀ {Γ A} (f : Ne Γ A) → f [ stop ]wNe ≡ f
  _[Id]wNf : ∀ {Γ A} (f : Nf Γ A) → f [ stop ]wNf ≡ f
  `app f x [Id]wNe = ap₂ `app (f [Id]wNe) (x [Id]wNf)
  `var x [Id]wNe = refl
  `fst f [Id]wNe = ap `fst (f [Id]wNe)
  `snd f [Id]wNe = ap `snd (f [Id]wNe)
  `ne x [Id]wNf = ap `ne (x [Id]wNe)
  `lam f [Id]wNf = ap `lam (f [keepstop]nfId)
  `pair a b [Id]wNf = ap₂ `pair (a [Id]wNf) (b [Id]wNf)

  NE : Ty → PsW.Ob
  NE A .F₀ Γ = el (Ne Γ A) {!   !}
  NE A .F₁ f n = n [ f ]wNe
  NE A .F-id = funext _[Id]wNe
  NE A .F-∘ = {!   !}
  
  NF : Ty → PsW.Ob
  NF A .F₀ Γ = el (Nf Γ A) {!   !}
  NF A .F₁ f n = n [ f ]wNf
  NF A .F-id = funext _[Id]wNf
  NF A .F-∘ = {!   !}


```


Now for the bulk of this formalization we will assume that there exists
an initial object in the category of models

```agda
module withInitial {ℓ} (Tm : STLC {ℓ} {ℓ}) 
  (⟦-⟧ : ∀ s → s .STLC.Ctx → Functor (Tm .STLC.𝓒) (s .STLC.𝓒)) where 
```

now would be a good time to introduce a notion of free STLC
```agda
module Free where


  
```
 

```agda
module TwGl {o} (S : STLC {o} {o}) (slam : STLC-lam S) (sprod : STLC-prod S) where
  module SC = Precategory (S .STLC.𝓒)
  open Democratic {o} {o} S
  open STLC dModel renaming (Ctx to Ob)
  open Weakenings {o} {o} S
  open Normals {o} {o} S slam sprod
  open Cat.Reasoning 𝓒
  open STLC-lam slam
  open STLC-prod sprod
  open Lift

  module P = Democratic {lsuc o} {lsuc o} (fst (CCC→STLC (
    ccc (PSh o 𝓦)
                (PSh-terminal {κ = o} {𝓦})
                (PSh-products {κ = o} {𝓦})
                (PSh-closed {o} {𝓦}))))
  module Pm = STLC P.dModel

  record TwGl-Ty : Type (lsuc o) where
    field τ   : Ty
    field ⦅τ⦆  : Pm.Ty
    field unq : PsW.Hom (NE τ)  (⦅τ⦆ .lower)
    field quo : PsW.Hom (⦅τ⦆ .lower) (NF τ)

    field commutes : ∀ (M : Ne Γ τ) → ⌜ quo .η Γ (unq .η Γ M) ⌝nf ≡ ⌜ M ⌝ne


  data TwGl-Ctx : Type (lsuc o) where
    ∅ : TwGl-Ctx
    Cons : TwGl-Ctx → TwGl-Ty → TwGl-Ctx  

  ⦅_⦆ctx : TwGl-Ctx → Pm.Ctx
  ⦅ ∅ ⦆ctx = Pm.ε
  ⦅ Cons x a ⦆ctx = ⦅ x ⦆ctx Pm.⊕ ⦅τ⦆ where open TwGl-Ty a

  
  ιNF : ∀ τ → PsW.Hom (NF τ) (𝕋W τ)
  ιNF = {!   !}

  NEs : Ctx → Pm.Ctx
  NEs Democratic.∅ = Pm.ε
  NEs (Democratic.Cons Γ t) = NEs Γ Pm.⊕ lift (NE t)

  getCtx : TwGl-Ctx → Ctx
  getCtx ∅ = ε
  getCtx (Cons x a) = getCtx x ⊕ τ where open TwGl-Ty a



  record TwGl-Tm (Γ : TwGl-Ctx) (A : TwGl-Ty) : Type (lsuc o) where
    
    module A = TwGl-Ty A
    field ⦅α⦆ : Pm.Tm A.⦅τ⦆ ⦅ Γ ⦆ctx
    field α  : Tm A.τ (getCtx Γ)

    -- field comm : ⦅α⦆ Pm.[ {!    !} ] ≡ {!   !}
          
    
```


-- We now introduce a functor 

-- ```agda 
-- module Syntax {ℓ} (𝓑 : Precategory ℓ ℓ) where
-- ```  
   
-- Now we consider the free model generated by an underlying category 
-- $\c{B}$ of base types and constants. We can show that this is initial
-- in the category of models. The free model also happens to be the syntax
-- of the simply typed lambda calculus!!                                