<!--
```agda
open import Cat.Prelude
open import Data.Dec.Base
open import Data.Nat.Base

open import Meta.Idiom
```
-->

```agda
module Logic.SimpleContext where
```

# Simple Contexts {defines="simply-typed-contexts"}

```agda
```

```agda
private variable 
  o : Level
  Ty : Type o

data Ctx {o} (Ty : Type o) : Type o where
  []  : Ctx Ty
  _⨾_ : Ctx Ty → Ty → Ctx Ty

_++_ : Ctx Ty → Ctx Ty → Ctx Ty
Γ ++ [] = Γ
Γ ++ (θ ⨾ P) = (Γ ++ θ) ⨾ P

instance
  Ctx-app : Append (Ctx Ty)
  Ctx-app .Append.mempty = []
  Ctx-app .Append._<>_ = _++_

map-ctx : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → Ctx A → Ctx B
map-ctx f []       = []
map-ctx f (xs ⨾ x) = map-ctx f xs ⨾ f x

Map-Ctx-id : ∀ {Ty : Type o} (Γ : Ctx Ty) → map-ctx (λ x → x) Γ ≡ Γ
Map-Ctx-id [] = refl
Map-Ctx-id (Γ ⨾ x) = ap (_⨾ x) (Map-Ctx-id Γ)

instance
  Map-Ctx : Map (eff Ctx)
  Map-Ctx = record { map = map-ctx }

private variable
  Γ Δ Θ : Ctx Ty
  A B : Ty
```


The following type represents an index into a context,
often called a variable.

```agda
data _∈ᶜ_ {o} {Ty : Type o} (P : Ty) : Ctx Ty → Type o where
  here  : ∀ {Γ} → P ∈ᶜ (Γ ⨾ P)
  there : ∀ {Γ Q} → P ∈ᶜ Γ → P ∈ᶜ (Γ ⨾ Q)

instance
  Membership-Ctx : Membership Ty (Ctx Ty) (level-of Ty)
  Membership-Ctx = record { _∈_ = _∈ᶜ_ }  



```

<!--
```agda
⨾≠[] : ∀ {x : Ty} {xs} → ¬ (xs ⨾ x) ≡ []
⨾≠[] p = subst distinguish p tt where
  distinguish : Ctx Ty → Type
  distinguish []     = ⊥
  distinguish (_ ⨾ _) = ⊤

π₁-cx : Ctx Ty → Ctx Ty
π₁-cx [] = []
π₁-cx (Γ ⨾ x) = Γ

π₂-cx : Ty → Ctx Ty → Ty
π₂-cx A [] = A
π₂-cx _ (Γ ⨾ A) = A

module CtxPath {Ty : Type o} where
  Code : Ctx Ty → Ctx Ty → Type (level-of Ty)
  Code [] []             = Lift _ ⊤
  Code [] (_ ⨾ _)         = Lift _ ⊥
  Code (t ⨾ h) []         = Lift _ ⊥
  Code (t ⨾ h) (t' ⨾ h')  = Code t t' × (h ≡ h')

  encode : {xs ys : Ctx Ty} → xs ≡ ys → Code xs ys
  encode {[]} {ys = []} path = lift tt
  encode {[]} {ys = ys ⨾ y} path = lift (⨾≠[] (sym path))
  encode {xs ⨾ x} {ys = []} path = lift (⨾≠[] path)
  encode {xs ⨾ x} {ys = ys ⨾ y} path =
      encode {xs} {ys} (ap π₁-cx path) , ap (π₂-cx y) path

  decode : {xs ys : Ctx Ty} → Code xs ys → xs ≡ ys
  decode {xs = []} {[]} code = refl
  decode {xs = xs ⨾ x} {ys ⨾ y} (p , q) i = decode p i ⨾ q i

  encode-decode : {xs ys : Ctx Ty} (p : Code xs ys) → encode (decode p) ≡ p
  encode-decode {xs = []} {[]} (lift tt) = refl
  encode-decode {xs = xs ⨾ x} {ys ⨾ y} (p , q) i = encode-decode p i , q

  decode-encode : {xs ys : Ctx Ty} (p : xs ≡ ys) → decode (encode p) ≡ p
  decode-encode = J (λ y p → decode (encode p) ≡ p) de-refl where
    de-refl : {xs : Ctx Ty} → decode (encode (λ i → xs)) ≡ (λ i → xs)
    de-refl {xs = []}         = refl
    de-refl {xs = xs ⨾ x} i j = de-refl {xs = xs} i j ⨾ x

  Code≃Path : {xs ys : Ctx Ty} → (xs ≡ ys) ≃ Code xs ys
  Code≃Path = Iso→Equiv (encode , iso decode encode-decode decode-encode)

  Ctx-is-hlevel : (n : Nat) → is-hlevel Ty (2 + n) → is-hlevel (Ctx Ty) (2 + n)
  Ctx-is-hlevel n ahl x y = Equiv→is-hlevel (suc n) Code≃Path Code-is-hlevel where
    Code-is-hlevel : {x y : Ctx Ty} → is-hlevel (Code x y) (suc n)
    Code-is-hlevel {[]} {[]}         = is-prop→is-hlevel-suc λ x y → refl
    Code-is-hlevel {[]} {y ⨾ x}      = is-prop→is-hlevel-suc λ x → absurd (lower x)
    Code-is-hlevel {_ ⨾ x} {[]}     = is-prop→is-hlevel-suc λ x → absurd (lower x)
    Code-is-hlevel {_ ⨾ x} {y ⨾ _} = ×-is-hlevel (suc n) Code-is-hlevel (ahl _ _) 

  instance
    H-Level-Ctx : ∀ {n} ⦃ p : 2 ≤ n ⦄ ⦃ _ : H-Level Ty n ⦄ → H-Level (Ctx Ty) n
    H-Level-Ctx {n = suc (suc n)} ⦃ s≤s (s≤s p) ⦄ ⦃ x ⦄ =
      record { has-hlevel = Ctx-is-hlevel n (H-Level.has-hlevel x) }

  is-set→Ctx-is-set : is-set Ty → is-set (Ctx Ty)
  is-set→Ctx-is-set = Ctx-is-hlevel zero

_∈?_ : ⦃ _ : Discrete Ty ⦄ (x : Ty) (xs : Ctx Ty) → Dec (x ∈ xs)
x ∈? [] = no λ ()
x ∈? (xs ⨾ y) with x ≡ᵢ? y
... | yes reflᵢ = yes here
... | no ¬p with x ∈? xs
... | yes p = yes (there p)
... | no ¬q = no λ { here → ¬p reflᵢ ; (there q) → ¬q q }

  
instance
  Dec-∈ : ⦃ _ : Discrete Ty ⦄ {x : Ty} {xs : Ctx Ty}
        → Dec (x ∈ xs)
  Dec-∈ {x = x} {xs} = x ∈? xs

```
-->
 
Sometimes we need to duplicate, remove, or reorder
a List, Renamings can be used for this. However,
we would like to provide a more general type.

For any family `Ctx → Ty → Type`, which we will call
generalised terms, we can provide a type of simultaneous
substitutions. Given a domain context $\Gamma$ and a
source context $\Delta$, we describe a substitution
$\Gamma → \Delta$ as a list of terms of type $\Delta_i$
in the context $\Gamma$.

```agda
data Sub {o ℓ} {Ty : Type o} (Tm : Ctx Ty → Ty → Type ℓ) (Γ : Ctx Ty)
      : Ctx Ty → Type (o ⊔ ℓ) where
  ε   : Sub Tm Γ []
  _⦊_ : ∀ {Δ A} → Sub Tm Γ Δ → Tm Γ A → Sub Tm Γ (Δ ⨾ A)
  
infixr 20 _⦊_
```

If a Term-Sub acts on a Term, then we can in general derive
a composition operation.

```agda
record Subst {ℓ ℓ' o} {Ty : Type o} (Tm : Ctx Ty → Ty → Type ℓ) (Ac : Ctx Ty → Ty → Type ℓ') : Type (o ⊔ ℓ ⊔ ℓ')
  where
  field _[_] : Tm Γ A → Sub Ac Δ Γ → Tm Δ A

  _[_]ᶜ : Sub Tm Γ Θ → Sub Ac Δ Γ → Sub Tm Δ Θ
  ε [ ρ ]ᶜ = ε
  (σ ⦊ x) [ ρ ]ᶜ = (σ [ ρ ]ᶜ) ⦊ (x [ ρ ])

open Subst {{...}}

_∘sub_ : ∀ {ℓ} {Tm : (Ctx Ty) → Ty → Type ℓ} ⦃ _ : Subst Tm Tm ⦄ {Γ Δ Θ}
          → Sub Tm Δ Θ → Sub Tm Γ Δ → Sub Tm Γ Θ
ε ∘sub s = ε
(r ⦊ x) ∘sub s = (r ∘sub s) ⦊ (x [ s ])

```

Alone this type isn't so useful, we can't even define
an identity substitution in general. So instead we
first focus on a concrete case: substitution of variables,
which we call renamings.

```agda

_ᶜ∋_ : (Ctx Ty) → Ty → Type (level-of Ty)
_ᶜ∋_ = flip _∈ᶜ_

Ren : Ctx Ty → Ctx Ty → Type (level-of Ty)
Ren = Sub _ᶜ∋_
  
  -- {-# DISPLAY _ᶜ∋_ _ Γ A = Γ ∈ A #-}
  -- {-# DISPLAY Sub Γ Δ = Ren Γ Δ #-}
  
drop-rn : Ren Γ Δ → Ren (Γ ⨾ A) Δ
drop-rn ε = ε
drop-rn (rn ⦊ x) = (drop-rn rn) ⦊ there x

keep-rn : Ren Γ Δ → Ren (Γ ⨾ A) (Δ ⨾ A)
keep-rn r = (drop-rn r) ⦊ here

id-rn : Ren Γ Γ
id-rn {Γ = []} = ε
id-rn {Γ = Γ ⨾ x} = drop-rn id-rn ⦊ here

π₁-rn : Ren (Γ ++ Δ) Γ
π₁-rn {Γ = Γ} {[]} = id-rn
π₁-rn {Γ = Γ} {Δ ⨾ x} = drop-rn π₁-rn

π₂-rn : Ren (Γ ++ Δ) Δ
π₂-rn {Γ = Γ} {[]} = ε
π₂-rn {Γ = Γ} {Δ ⨾ x} = drop-rn π₂-rn ⦊ here

⟨⟩-rn : Ren Γ Δ → Ren Γ Θ → Ren Γ (Δ ++ Θ)
⟨⟩-rn {Θ = []} f g = f
⟨⟩-rn {Θ = Θ ⨾ x} f (g ⦊ y) = (⟨⟩-rn f g) ⦊ y
```

We can easily show that renamings act on variables,
and so we get a composition operation for free.

```agda
_[_]v : A ∈ Γ → Ren Δ Γ → A ∈ᶜ Δ
here [ _ ⦊ x ]v = x
there v [ r ⦊ _ ]v = v [ r ]v

instance
  Sub-var : ∀ {o} {Ty : Type o} → Subst {Ty = Ty} _ᶜ∋_ _ᶜ∋_
  Sub-var = record { _[_] = _[_]v }
  
```

Now lets show that the composition really does form a category.

```agda
module _ {o} {Ty : Type o} where
  rn-comp-lem : (x : A ∈ Θ) → {σ : Ren Δ Θ} → {τ : Ren Γ Δ}
              → ((x [ σ ]v) [ τ ]v) ≡ (x [ σ ∘sub τ ]v)
  rn-comp-lem here {σ = σ ⦊ y} = refl
  rn-comp-lem (there x) {σ = σ ⦊ _} = rn-comp-lem x

  rn-comp-assoc : ∀ {B Γ Δ Θ} {ρ : Ren {Ty = Ty} Δ Θ} {σ : Ren Γ Δ} {τ : Ren B Γ}
                →  (ρ ∘sub σ) ∘sub τ ≡ ρ ∘sub (σ ∘sub τ)
  rn-comp-assoc {ρ = ε} {σ} {τ} = refl
  rn-comp-assoc {ρ = ρ ⦊ x} {σ} {τ} = ap₂ _⦊_ rn-comp-assoc (rn-comp-lem x)

  rn-idl-lem : {ρ : Ren Γ Δ} {σ : Ren Δ Θ} {x : A ∈ᶜ Γ}
            → drop-rn σ ∘sub (ρ ⦊ x) ≡ σ ∘sub ρ
  rn-idl-lem {ρ = ρ} {ε} = refl
  rn-idl-lem {ρ = ρ} {σ ⦊ x} = ap₂ _⦊_ rn-idl-lem refl

  rn-comp-idl : {ρ : Ren Γ Δ} → id-rn ∘sub ρ ≡ ρ
  rn-comp-idl {ρ = ε} = refl
  rn-comp-idl {ρ = ρ ⦊ x} = ap₂ _⦊_ (rn-idl-lem ∙ rn-comp-idl) refl

  rn-idr-lem : (x : B ∈ᶜ Γ) (σ : Ren {Ty = Ty} Δ Γ)
            → x [ drop-rn {A = A} σ ] ≡ there (x [ σ ])
  rn-idr-lem here (σ ⦊ x) = refl
  rn-idr-lem (there x) (σ ⦊ v) = rn-idr-lem x σ

  rn-idr-lem2 : (x' : B ∈ᶜ Γ) → x' [ id-rn ] ≡ x'
  rn-idr-lem2 here = refl
  rn-idr-lem2 (there x')
    = rn-idr-lem x' id-rn ∙ ap there (rn-idr-lem2 x')

  rn-comp-idr : {ρ : Ren {Ty = Ty} Γ Δ} → ρ ∘sub id-rn ≡ ρ
  rn-comp-idr {ρ = ε} = refl
  rn-comp-idr {ρ = ρ ⦊ x} = ap₂ _⦊_ rn-comp-idr (rn-idr-lem2 x)


  -- Renamings : ⦃ _ : H-Level Ty 2 ⦄ → Precategory o o
  -- Renamings .Precategory.Ob = Ctx
  -- Renamings .Precategory.Hom = Ren
  -- Renamings .Precategory.Hom-set = {!  !}
  -- Renamings .Precategory.id = id-rn
  -- Renamings .Precategory._∘_ = _∘sub_
  -- Renamings .Precategory.idr _ = rn-comp-idr
  -- Renamings .Precategory.idl _ = rn-comp-idl
  -- Renamings .Precategory.assoc _ _ _ = sym rn-comp-assoc

  -- Var-psh : ⦃ _ : H-Level Ty 2 ⦄ → Ty → Functor (Renamings ^op) (Sets o)
  -- Var-psh A .Functor.F₀ Γ = el (A ∈ Γ) {!   !}
  -- Var-psh A .Functor.F₁ σ v = v [ σ ]
  -- Var-psh A .Functor.F-id = ext rn-idr-lem2
  -- Var-psh A .Functor.F-∘ f g = ext (λ x → sym (rn-comp-lem x))
```


A var term is a term that has an embedding of variables.



```agda

extend-subs : ∀ {ℓ ℓ'} → {Tm : Ctx Ty → Ty → Type ℓ}
            → {Tm' : Ctx Ty → Ty → Type ℓ'}
            → (∀ {Γ A} → Tm Γ A → Tm' Γ A)
            → Sub Tm Γ Δ → Sub Tm' Γ Δ
extend-subs f ε = ε
extend-subs f (r ⦊ x) = (extend-subs f r) ⦊ (f x)

record Var-term {ℓ} (Tm : Ctx Ty → Ty → Type ℓ) : Type (level-of Ty ⊔ ℓ) where
  field ι : A ∈ Γ → Tm Γ A

  vzero : Tm (Γ ⨾ A) A
  vzero = ι here
  
  ι₁ : Ren Γ Δ → Sub Tm Γ Δ
  ι₁ = extend-subs ι

open Var-term ⦃ ... ⦄ public

instance
  varSub : ∀ {ℓ} {Tm : Ctx Ty → Ty → Type ℓ}
          → ⦃ _ : Subst Tm Tm ⦄ → ⦃ _ : Var-term {o} {Ty} {ℓ} Tm ⦄ 
          → Subst Tm _ᶜ∋_
  (varSub Subst.[ t ]) σ = t [ ι₁ σ ]
  {-# OVERLAPPABLE varSub #-}

module _ {ℓ'} {Tm : Ctx Ty → Ty → Type ℓ'} ⦃ _ : Subst Tm _ᶜ∋_ ⦄
      ⦃ _ : Var-term Tm ⦄ where

  wk1 : Tm Γ A → Tm (Γ ⨾ B) A
  wk1 x = x [ π₁-rn ]
  
  drop-sub : Sub Tm Γ Δ → Sub Tm (Γ ⨾ A) Δ
  drop-sub ε = ε
  drop-sub (r ⦊ x) = (drop-sub r) ⦊ (wk1 x)

  keep-sub : Sub Tm Γ Δ → Sub Tm (Γ ⨾ A) (Δ ⨾ A)
  keep-sub r = (drop-sub r) ⦊ vzero

  id-sub : Sub Tm Γ Γ
  id-sub {[]} = ε
  id-sub {Γ ⨾ x} = (drop-sub id-sub) ⦊ vzero

  π₁-sub : Sub Tm (Γ ++ Δ) Γ
  π₁-sub {Δ = []} = id-sub
  π₁-sub {Δ = Δ ⨾ x} = drop-sub π₁-sub

  π₂-sub : Sub Tm (Γ ++ Δ) Δ
  π₂-sub {Δ = []} = ε
  π₂-sub {Δ = Δ ⨾ x} = keep-sub π₂-sub

  ⟨⟩-sub : Sub Tm Γ Δ → Sub Tm Γ Θ → Sub Tm Γ (Δ ++ Θ)
  ⟨⟩-sub f ε = f
  ⟨⟩-sub f (g ⦊ x) = (⟨⟩-sub f g) ⦊ x
```

As you can see we can turn any type that has a `Subst Tm Tm`
instance into a category, just as long it satisfies the lemmas

```agda
  -- record is-Subst-cat {ℓ} (Tm : Ctx → Ty → Type ℓ) 
  --         ⦃ _ : ∀ {Γ A} → H-Level (Tm Γ A) 2 ⦄
  --         ⦃ _ : Var-term Tm ⦄ ⦃ _ : Subst Tm Tm ⦄ : Type (ℓ ⊔ o) where
  --   field
  --     subst-assoc : {σ : Sub Tm Δ Θ} → {τ : Sub Tm Γ Δ}
  --                 → (x : Tm Θ A)
  --                 → (x [ σ ]) [ τ ] ≡ x [ σ ∘sub τ ]

  --     subst-idr : {ρ : Sub Tm Γ Δ} {σ : Sub Tm Δ Θ} 
  --               → (x : Tm Γ A)
  --               → drop-sub σ ∘sub (ρ ⦊ x) ≡ σ ∘sub ρ

  --     subst-idl : (x : Tm Γ B)
  --               → x [ id-sub ] ≡ x

  --     subst-varz : ∀ {σ : Sub Tm Γ Δ} (x : Tm Γ A)
  --                → vzero [ σ ⦊ x ] ≡ x

  --   subst-idl' : ∀ (σ : Sub Tm Γ Δ) → id-sub ∘sub σ ≡ σ
  --   subst-idl' ε = refl
  --   subst-idl' (f ⦊ x) = ap₂ _⦊_ (subst-idr x ∙ subst-idl' f) (subst-varz x)

  --   subst-idr' : ∀ (σ : Sub Tm Γ Δ) → σ ∘sub id-sub ≡ σ
  --   subst-idr' ε = refl
  --   subst-idr' (σ ⦊ x) = ap₂ _⦊_ (subst-idr' σ) (subst-idl x)

  --   subst-assoc' : ∀ {B Γ Δ Θ} (ρ : Sub Tm Δ Θ) (σ : Sub Tm Γ Δ)
  --                  (τ : Sub Tm B Γ)
  --                 →  (ρ ∘sub σ) ∘sub τ ≡ ρ ∘sub (σ ∘sub τ)
  --   subst-assoc' ε g h = refl
  --   subst-assoc' (f ⦊ x) g h = ap₂ _⦊_ (subst-assoc' f g h) (subst-assoc x)

    -- Subs : Precategory o (o ⊔ ℓ)
    -- Subs .Precategory.Ob = Ctx
    -- Subs .Precategory.Hom = Sub Tm
    -- Subs .Precategory.Hom-set = {! hlevel 2  !}
    -- Subs .Precategory.id = id-sub
    -- Subs .Precategory._∘_ = _∘sub_
    -- Subs .Precategory.idr = subst-idr'
    -- Subs .Precategory.idl = subst-idl'
    -- Subs .Precategory.assoc f g h = sym (subst-assoc' f g h)

    -- Tm-psh : Ty → Functor (Subs ^op) (Sets ℓ)
    -- Tm-psh A .Functor.F₀ Γ = el (Tm Γ A) (hlevel 2)
    -- Tm-psh A .Functor.F₁ σ t = t [ σ ]
    -- Tm-psh A .Functor.F-id = ext subst-idl
    -- Tm-psh A .Functor.F-∘ f g = ext (λ x  → sym $ subst-assoc x)
 
```
     
     