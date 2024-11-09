

```agda
open import Cat.Prelude
open import Order.Semilattice.Meet
open import Order.Base
open import Order.Cat
open import Order.Instances.Props
open import Cat.Instances.Product
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Instances.Family
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Total
open import Cat.Instances.StrictCat
open import Cat.Functor.Naturality
open import Data.Sum.Base

open import Data.Nat

open import Logic.SimpleContext

open import Meta.Idiom

import Cat.Morphism

module Logic.Propositional.Intuitionistic where

private variable
  ℓ : Level
  A : Type ℓ
```



```agda
data ℙrop (A : Type ℓ) : Type ℓ where
  ↑_      : A → ℙrop A
  _′∧_   : ℙrop A → ℙrop A → ℙrop A
  _′∨_   : ℙrop A → ℙrop A → ℙrop A
  _′⇒_  : ℙrop A → ℙrop A → ℙrop A
  true false : ℙrop A


  
map-ℙrop : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → ℙrop A → ℙrop B
map-ℙrop f (↑ x) = ↑ f x
map-ℙrop f (x ′∧ x₁) = map-ℙrop f x ′∧ map-ℙrop f x₁
map-ℙrop f (x ′∨ x₁) = map-ℙrop f x ′∨ map-ℙrop f x₁
map-ℙrop f (x ′⇒ x₁) = map-ℙrop f x ′⇒ map-ℙrop f x₁
map-ℙrop f true = true
map-ℙrop f false = false

map-ℙ-id : ∀ {A : Type ℓ} (p : ℙrop A) → map-ℙrop (λ x → x) p ≡ p
map-ℙ-id (↑ x) = refl
map-ℙ-id (p ′∧ q) i = map-ℙ-id p i ′∧ map-ℙ-id q i
map-ℙ-id (p ′∨ q) i = map-ℙ-id p i ′∨ map-ℙ-id q i
map-ℙ-id (p ′⇒ q) i = map-ℙ-id p i ′⇒ map-ℙ-id q i
map-ℙ-id (true) = refl
map-ℙ-id (false) = refl

map-ℙ-∘ : ∀ {A B C : Type ℓ} (f : A → B) (g : B → C) (p : ℙrop A)
        → map-ℙrop (g ⊙ f) p ≡ map-ℙrop g (map-ℙrop f p)
map-ℙ-∘ _ _ (↑ x) = refl
map-ℙ-∘ f g (p ′∧ q) i = map-ℙ-∘ f g p i ′∧ map-ℙ-∘ f g q i
map-ℙ-∘ f g (p ′∨ q) i = map-ℙ-∘ f g p i ′∨ map-ℙ-∘ f g q i
map-ℙ-∘ f g (p ′⇒ q) i = map-ℙ-∘ f g p i ′⇒ map-ℙ-∘ f g q i
map-ℙ-∘ _ _ true = refl
map-ℙ-∘ _ _ false = refl

instance
  Map-ℙrop : Map (eff ℙrop)
  Map-ℙrop = record { map = map-ℙrop }

module ℙrop-path {ℓ} {A : Type ℓ} where
  Code : ℙrop A → ℙrop A → Type ℓ
  Code (↑ x) (↑ x') = x ≡ x'
  Code (p ′∧ p') (q ′∧ q') = Code p q × Code p' q'
  Code (p ′∨ p') (q ′∨ q') = Code p q × Code p' q'
  Code (p ′⇒ p') (q ′⇒ q') = Code p q × Code p' q'
  Code true true = Lift _ ⊤
  Code false false = Lift _ ⊤
  Code _ _ = Lift _ ⊥

  isHead : ℙrop A → Type ℓ
  isHead (↑ x) = Lift _ ⊤
  isHead _ = Lift _ ⊥

  isAnd : ℙrop A → Type ℓ
  isAnd (_ ′∧ _) = Lift _ ⊤
  isAnd _ = Lift _ ⊥

  isOr : ℙrop A → Type ℓ
  isOr (_ ′∨ _) = Lift _ ⊤
  isOr _ = Lift _ ⊥

  isImp : ℙrop A → Type ℓ
  isImp (_ ′⇒ _) = Lift _ ⊤
  isImp _ = Lift _ ⊥

  isTrue : ℙrop A → Type ℓ
  isTrue true = Lift _ ⊤
  isTrue _ = Lift _ ⊥

  isFalse : ℙrop A → Type ℓ
  isFalse false = Lift _ ⊤
  isFalse _ = Lift _ ⊥

  encode : ∀ {p q} → p ≡ q → Code p q 
  encode {↑ x} {↑ x₁} P = ap (f x) P where
    f : A  → ℙrop A → A
    f _ (↑ x) = x
    f x _ = x
  encode {↑ x} {q ′∧ q₁} P = subst isHead P _
  encode {↑ x} {q ′∨ q₁} P = subst isHead P _
  encode {↑ x} {q ′⇒ q₁} P = subst isHead P _
  encode {↑ x} {true} P = subst isHead P _
  encode {↑ x} {false} P = subst isHead P _
  
  encode {p ′∧ p₁} {q ′∧ q₁} P 
    = encode {p} (ap (f p) P) , encode {p₁} {q₁} (ap (g q) P) where
    f : ℙrop A → ℙrop A → ℙrop A
    f x' (x ′∧ x₁) = x
    f x' _ = x'

    g : ℙrop A → ℙrop A → ℙrop A
    g x' (x ′∧ x₁) = x₁
    g x' _ = x'
  encode {p ′∧ p₁} {↑ x} P = subst isAnd P _
  encode {p ′∧ p₁} {q ′∨ q₁} P = subst isAnd P _
  encode {p ′∧ p₁} {q ′⇒ q₁} P = subst isAnd P _
  encode {p ′∧ p₁} {true} P = subst isAnd P _
  encode {p ′∧ p₁} {false} P = subst isAnd P _

  encode {p ′∨ p₁} {q ′∨ q₁} P 
    = (encode {p} (ap (f p) P)) , (encode {p₁} (ap (g p) P)) where
    f : ℙrop A → ℙrop A → ℙrop A
    f x' (x ′∨ x₁) = x
    f x' _ = x'

    g : ℙrop A → ℙrop A → ℙrop A
    g x' (x ′∨ x₁) = x₁
    g x' _ = x'
  encode {p ′∨ p₁} {↑ x} P = subst isOr P _
  encode {p ′∨ p₁} {q ′∧ q₁} P = subst isOr P _
  encode {p ′∨ p₁} {q ′⇒ q₁} P = subst isOr P _
  encode {p ′∨ p₁} {true} P = subst isOr P _
  encode {p ′∨ p₁} {false} P = subst isOr P _

  encode {p ′⇒ p₁} {q ′⇒ q₁} P
    = (encode {p} (ap (f p) P)) , (encode {p₁} (ap (g p) P)) where
    f : ℙrop A → ℙrop A → ℙrop A
    f x' (x ′⇒ x₁) = x
    f x' _ = x'

    g : ℙrop A → ℙrop A → ℙrop A
    g x' (x ′⇒ x₁) = x₁
    g x' _ = x'
  encode {p ′⇒ p₁} {↑ x} P = subst isImp P _
  encode {p ′⇒ p₁} {q ′∧ q₁} P = subst isImp P _
  encode {p ′⇒ p₁} {q ′∨ q₁} P = subst isImp P _
  encode {p ′⇒ p₁} {true} P = subst isImp P _
  encode {p ′⇒ p₁} {false} P = subst isImp P _

  encode {true} {true} P = _
  encode {true} {↑ x} P = subst isTrue P _
  encode {true} {q ′∧ q₁} P = subst isTrue P _
  encode {true} {q ′∨ q₁} P = subst isTrue P _
  encode {true} {q ′⇒ q₁} P = subst isTrue P _
  encode {true} {false} P = subst isTrue P _
  
  encode {false} {false} P = _
  encode {false} {↑ x} P = subst isFalse P _
  encode {false} {q ′∧ q₁} P = subst isFalse P _
  encode {false} {q ′∨ q₁} P = subst isFalse P _
  encode {false} {q ′⇒ q₁} P = subst isFalse P _
  encode {false} {true} P = subst isFalse P _

  decode : ∀ {p q} → Code p q → p ≡ q
  decode {↑ x} {↑ x₁} P = ap (↑_) P
  decode {p ′∧ p₁} {q ′∧ q₁} (P , Q) = ap₂ _′∧_ (decode P) (decode Q)
  decode {p ′∨ p₁} {q ′∨ q₁} (P , Q) = ap₂ _′∨_ (decode P) (decode Q)
  decode {p ′⇒ p₁} {q ′⇒ q₁} (P , Q) = ap₂ _′⇒_ (decode P) (decode Q)
  decode {true} {true} P = refl
  decode {false} {false} P = refl

  encode-decode : ∀ {p q} (P : Code p q) → encode (decode P) ≡ P
  encode-decode {↑ x} {↑ x₁} P = refl
  encode-decode {p ′∧ p₁} {q ′∧ q₁} (P , Q) = encode-decode P ,ₚ encode-decode Q
  encode-decode {p ′∨ p₁} {q ′∨ q₁} (P , Q) = (encode-decode P ,ₚ encode-decode Q)
  encode-decode {p ′⇒ p₁} {q ′⇒ q₁} (P , Q) = (encode-decode P ,ₚ encode-decode Q)
  encode-decode {true} {true} P = refl
  encode-decode {false} {false} P = refl

  decode-encode : ∀ {p q} (P : p ≡ q) → decode (encode P) ≡ P
  decode-encode P = J (λ y p → decode (encode p) ≡ p) de-refl P where
    de-refl : ∀ {p} → decode (encode {p} refl) ≡ (refl)
    de-refl {↑ x} = refl
    de-refl {p ′∧ q} i j = de-refl {p} i j ′∧ de-refl {q} i j
    de-refl {p ′∨ q} i j = de-refl {p} i j ′∨ de-refl {q} i j
    de-refl {p ′⇒ q} i j = de-refl {p} i j ′⇒ de-refl {q} i j
    de-refl {true} = refl
    de-refl {false} = refl

  
  Code≃Path : ∀ {p q} → (p ≡ q) ≃ Code p q
  Code≃Path = Iso→Equiv (encode , iso decode encode-decode decode-encode)

  ℙrop-is-hlevel : (n : Nat) → is-hlevel A (2 + n) → is-hlevel (ℙrop A) (2 + n)
  ℙrop-is-hlevel n ahl x y = Equiv→is-hlevel (suc n) Code≃Path Code-is-hlevel where
    Code-is-hlevel : ∀ {x y} → is-hlevel (Code x y) (suc n)
    Code-is-hlevel {↑ x} {↑ x₁} = ahl _ _
    Code-is-hlevel {↑ x} {y ′∧ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {↑ x} {y ′∨ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {↑ x} {y ′⇒ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {↑ x} {true} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {↑ x} {false} = is-prop→is-hlevel-suc (hlevel 1)
    
    Code-is-hlevel {x ′∧ x₁} {y ′∧ y₁} = ×-is-hlevel (suc n) Code-is-hlevel Code-is-hlevel
    Code-is-hlevel {x ′∧ x₁} {↑ x₂} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {x ′∧ x₁} {y ′∨ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {x ′∧ x₁} {y ′⇒ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {x ′∧ x₁} {true} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {x ′∧ x₁} {false} = is-prop→is-hlevel-suc (hlevel 1)

    Code-is-hlevel {x ′∨ x₁} {y ′∨ y₁} = ×-is-hlevel (suc n) Code-is-hlevel Code-is-hlevel
    Code-is-hlevel {x ′∨ x₁} {↑ x₂} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {x ′∨ x₁} {y ′∧ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {x ′∨ x₁} {y ′⇒ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {x ′∨ x₁} {true} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {x ′∨ x₁} {false} = is-prop→is-hlevel-suc (hlevel 1)

    Code-is-hlevel {x ′⇒ x₁} {y ′⇒ y₁} = ×-is-hlevel (suc n) Code-is-hlevel Code-is-hlevel
    Code-is-hlevel {x ′⇒ x₁} {↑ x₂} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {x ′⇒ x₁} {y ′∧ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {x ′⇒ x₁} {y ′∨ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {x ′⇒ x₁} {true} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {x ′⇒ x₁} {false} = is-prop→is-hlevel-suc (hlevel 1)

    Code-is-hlevel {true} {true} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {true} {↑ x} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {true} {y ′∧ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {true} {y ′∨ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {true} {y ′⇒ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {true} {false} = is-prop→is-hlevel-suc (hlevel 1)
    
    Code-is-hlevel {false} {false} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {false} {↑ x} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {false} {y ′∧ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {false} {y ′∨ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {false} {y ′⇒ y₁} = is-prop→is-hlevel-suc (hlevel 1)
    Code-is-hlevel {false} {true} = is-prop→is-hlevel-suc (hlevel 1)

  instance
    H-Level-ℙrop : ∀ {n} ⦃ p : 2 ≤ n ⦄ ⦃ _ : H-Level A n ⦄ → H-Level (ℙrop A) n
    H-Level-ℙrop {n = suc (suc n)} ⦃ s≤s (s≤s p) ⦄ ⦃ x ⦄ =
      record { has-hlevel = ℙrop-is-hlevel n (H-Level.has-hlevel x) }

  is-set→ℙrop-is-set : is-set A → is-set (ℙrop A)
  is-set→ℙrop-is-set = ℙrop-is-hlevel zero

```

## Propositional theories

We want to parameterise our theory by some set of atoms
and operations.

We follow Jacobs [cite], and directly define theories
as a displayed category - which is a nicer type theoretic
version of a fibration. The particular fibration we are
interested in is a pullback of the family fibration
by X ↦ List (ℙrop X) × ℙrop X.

```agda
Ctx-F : Functor (Sets ℓ) (Sets ℓ)
Ctx-F .Functor.F₀ X = el (Ctx (ℙrop ∣ X ∣) × (ℙrop ∣ X ∣)) (hlevel 2)
Ctx-F .Functor.F₁ f (a , b) = map (map f) a , map f b
Ctx-F .Functor.F-id = ext (λ xs y → p1 _ , map-ℙ-id _) where
  p1 : ∀ (a : Ctx (ℙrop A)) → map (map (λ x → x)) a ≡ a 
  p1 [] = refl
  p1 (a ⨾ x) i = p1 a i ⨾ map-ℙ-id x i
Ctx-F .Functor.F-∘ f g = ext (λ xs y → p1 g f xs , map-ℙ-∘ g f y) where
  p1 : ∀ {A B C : Type ℓ} (f : A → B) (g : B → C) (p : Ctx (ℙrop A))
        → map (map (g ⊙ f)) p ≡ map (map g) (map (map f) p)
  p1 f g [] = refl
  p1 f g (p ⨾ x) i = p1 f g p i ⨾ map-ℙ-∘ f g x i

Theories : Displayed (Sets ℓ) ℓ ℓ
Theories = Change-of-base Ctx-F (Family (poset→category Props))


Th : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Th _ = ∫ Theories

module Th {ℓ} = Precategory (Th ℓ)
  
Theory : ∀ ℓ → Type (lsuc ℓ)
Theory ℓ = Th ℓ .Precategory.Ob 

```


```agda

module Theory (T : Theory ℓ) where
  Atom : Type ℓ
  Atom = ∣  T .fst ∣

  Axiom : Ctx (ℙrop Atom) → ℙrop Atom → Ω
  Axiom Γ A = T .snd (Γ , A)

record Theory-hom {o o'} (S : Theory o) (T : Theory o')
  : Type (o ⊔ o') where
  
  constructor T-hom

  module T = Theory T
  module S = Theory S


  field
    F-atom  : S.Atom → T.Atom
    F-axiom : ∀ {Γ A} → ∣ S.Axiom Γ A ∣ 
               → ∣ T.Axiom (map (map F-atom) Γ) (map F-atom A) ∣

make-theory-hom : ∀ {o} {S T : Theory o} 
    → Theory-hom S T → Th o .Precategory.Hom S T
make-theory-hom tm 
  = total-hom F-atom λ _ → F-axiom where
  open Theory-hom tm

unmake-theory-hom : ∀ {o} {S T : Theory o}
      → Th o .Precategory.Hom S T → Theory-hom S T
unmake-theory-hom (total-hom hom pres) = T-hom hom (λ {Γ} {A} → pres (Γ , A) )


```
 

## Models of propositional logic

Here we now define what a model is,
given a particular theory.


```agda
Props' = poset→category Props

record _↔_ {o ℓ} {C : Precategory o ℓ}
  (x y : C .Precategory.Ob) : Type (o ⊔ ℓ) where
  constructor Iff
  open Precategory C
  field
    to : Hom x y
    from : Hom y x


record SPwF o ℓ : Type (lsuc (o ⊔ ℓ))  where

  field 
    Con  : Precategory o ℓ

  field
    Con-thin : is-thin Con
  
  field
    Con-ter : Terminal Con
    Con-prod : ∀ Γ Δ → Product Con Γ Δ

  open Precategory Con using () renaming (Ob to Cx; Hom to Con[_,_]) public
  open Cat.Morphism Con public
  open Terminal Con-ter using (top;!) public
  open Binary-products Con Con-prod public
  open Functor

  field
    Con-str  : is-set Cx
    Ty   : Set o

    Tm   : ∀ (A : ∣ Ty ∣) → Functor (Con ^op) Props'

  _⊨_ : Cx → ∣ Ty ∣ → Type
  Γ ⊨ A = ∣ Tm A .F₀ Γ ∣

  field
    extend   : ∀ (A : ∣ Ty ∣) → Functor Con Con

  _⊕_ : Cx → ∣ Ty ∣ → Cx
  Γ ⊕ A = extend A .F₀ Γ

  _⊕₁_ : ∀ {Γ Δ} → Con[ Γ , Δ ] → (A : ∣ Ty ∣) → Con[ Γ ⊕ A , Δ ⊕ A ]
  γ ⊕₁ A = extend A .F₁ γ

  field
    extend-rep : ∀ {Γ Δ} → (A : ∣ Ty ∣)
                 → (Con[ Γ , Δ ] × Γ ⊨ A) ≡ Con[ Γ , (Δ ⊕ A) ]

  field
    model-⊤ : ∣ Ty ∣
    ⊤-rep : ∀ {Γ} → Γ ⊨ model-⊤ -- Γ ⊨ ⊤ is contr

  field
    model-⊥ : ∣ Ty ∣
    ⊥-rep   : ∀ {Γ A} → (Γ ⊕ model-⊥) ⊨ A -- ⊥ ⊨ A is contr

  field
    _model-∧_ : ∣ Ty ∣ → ∣ Ty ∣ → ∣ Ty ∣
    ∧-rep : ∀ {Γ A B} → Γ ⊨ (A model-∧ B) ≡ (Γ ⊨ A × Γ ⊨ B)

  field
    _model-∨_ : ∣ Ty ∣  → ∣ Ty ∣ → ∣ Ty ∣
    ∨-rep : ∀ {Γ A B Δ}
            → Con[ Γ ⊕ (A model-∨ B) , Δ ] 
                ≡
              (Con[ Γ ⊕ A , Δ ] × Con[ Γ ⊕ B , Δ ])
    
  field
    _model-⇒_ : ∣ Ty ∣ → ∣ Ty ∣ → ∣ Ty ∣
    ⇒-rep : ∀ {Γ A B} → (Γ ⊕ A) ⊨ B ≡ Γ ⊨ (A model-⇒ B)

  instance
    con-hlevel : ∀ {Γ Δ} → H-Level Con[ Γ , Δ ] 1
    con-hlevel = basic-instance 1 (Con-thin _ _)

    prop'-hlevel : ∀ {X Y} → H-Level (Props' .Precategory.Hom X Y) 1
    prop'-hlevel = hlevel-instance (λ f g → ext λ x → prop!)

  sub-tm : ∀ {Γ Δ A} → Con[ Γ , Δ ] → Δ ⊨ A → Γ ⊨ A
  sub-tm = Tm _ .F₁

  extπ₁ : ∀ {Γ Δ A} → Con[ Γ , Δ ⊕ A ] → Con[ Γ , Δ ]
  extπ₁ {_} {_} {A} x = transport (sym $ extend-rep A) x .fst


  ext→term : ∀ {Γ A} → Con[ Γ , Γ ⊕ A ] → Γ ⊨ A
  ext→term {_} {A} x = transport (sym $ extend-rep A) x .snd

  extend-sub : ∀ {Γ Δ A} → Con[ Γ , Δ ] → Γ ⊨ A → Con[ Γ , Δ ⊕ A ]
  extend-sub γ t = transport (extend-rep _) (γ , t)

  π₁-⊕ : ∀ {Γ A} → Con[ Γ ⊕ A , Γ ]
  π₁-⊕ {Γ} {A} = transport (sym $ extend-rep _) (id {Γ ⊕ A}) .fst

  varz : ∀ {Γ A} → (Γ ⊕ A) ⊨ A
  varz {Γ} {A} = transport (sym $ extend-rep _) (id {Γ ⊕ A}) .snd

  wk-tm : ∀ {Γ A B} → Γ ⊨ A → (Γ ⊕ B) ⊨ A
  wk-tm x = sub-tm (transport (sym $ extend-rep _) id .fst) x

  assume : ∀ {Γ A B} → (Γ ⊕ A) ⊨ B → Γ ⊨ (A model-⇒ B)
  assume = transport ⇒-rep

  unassume : ∀ {Γ A B} → Γ ⊨ (A model-⇒ B) →  (Γ ⊕ A) ⊨ B
  unassume = transport (sym ⇒-rep)

  apply1 : ∀ {Γ A B} → Γ ⊨ (A model-⇒ B) → Γ ⊨ A → Γ ⊨ B
  apply1 f x = sub-tm (extend-sub id x) $ unassume f

  fst-tm : ∀ {Γ A B} → Γ ⊨ (A model-∧ B) → Γ ⊨ A
  fst-tm x = transport ∧-rep x .fst

  ex-falso : ∀ {Γ A} → Γ ⊨ model-⊥ → Γ ⊨ A
  ex-falso x = sub-tm (extend-sub id x) ⊥-rep

  ∨-left : ∀ {Γ A B} → Γ ⊨ A → Γ ⊨ (A model-∨ B)
  ∨-left {Γ = Γ} {A} {B} x 
    = let t : Con[ Γ ⊕ A , Γ ⊕ _ ]
          t = transport ∨-rep (id {Γ ⊕ (A model-∨ B)}) .fst
      in ext→term (t ∘ extend-sub id x) 

  ∨-right : ∀ {Γ A B} → Γ ⊨ B → Γ ⊨ (A model-∨ B)
  ∨-right {Γ = Γ} {A} {B} x 
    = let t : Con[ Γ ⊕ B , Γ ⊕ _ ]
          t = transport ∨-rep (id {Γ ⊕ (A model-∨ B)}) .snd
      in ext→term (t ∘ extend-sub id x) 

  ∨-elim : ∀ {Γ A B Q} → (Γ ⊕ A) ⊨ Q  → (Γ ⊕ B) ⊨ Q
          → (Γ ⊕ (A model-∨ B)) ⊨ Q
  ∨-elim l r = ext→term (transport (sym ∨-rep) 
     ((extend-sub (extend-sub (extπ₁ id) (∨-left varz)) l)
    , (extend-sub (extend-sub (extπ₁ id) (∨-right varz)) r)))


module _ {o ℓ} (S : SPwF o ℓ) (T : Theory o) where
  open Theory T
  open SPwF S

  include-ℙrop : (Atom → ∣ Ty ∣) → ℙrop Atom → ∣ Ty ∣
  include-ℙrop f (↑ x) = f x
  include-ℙrop f (p ′∧ q) = include-ℙrop f p model-∧ include-ℙrop f q
  include-ℙrop f (p ′∨ q) = include-ℙrop f p model-∨ include-ℙrop f q
  include-ℙrop f (p ′⇒ q) = include-ℙrop f p model-⇒ include-ℙrop f q
  include-ℙrop f true = model-⊤
  include-ℙrop f false = model-⊥

  include-Ctx : (Atom → ∣ Ty ∣) → Ctx (ℙrop Atom) → Cx
  include-Ctx f [] = top
  include-Ctx f (cx ⨾ x) = include-Ctx f cx ⊕ include-ℙrop f x

record is-T-model {o ℓ} (S : SPwF o ℓ) (T : Theory o) : Type (lsuc (o ⊔ ℓ)) where
   
  open SPwF S
  open Theory T

  field
    atom : Atom → ∣ Ty ∣
    axiom : ∀ {Γ A} → ∣ Axiom Γ A ∣ 
            → include-Ctx S T atom Γ ⊨ include-ℙrop S T atom A
    

record _⇔_ {o o' ℓ ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    (F : Functor C D) (G : Functor C D) : Type (o ⊔ ℓ') where
  constructor Iff
  
  open Precategory
  open Functor


  field
    to : ∀ x → D .Hom (F .F₀ x) (G .F₀ x)
    from : ∀ x → D .Hom (G .F₀ x) (F .F₀ x)


module _ where
  private unquoteDecl eqv = declare-record-iso eqv (quote _⇔_)

  instance
    Extensional-⇔ : ∀ {o o' ℓ ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
      {F : Functor C D} {G : Functor C D} → Extensional (F ⇔ G) (o ⊔ ℓ') 
    Extensional-⇔ = iso→extensional eqv auto

    hlevel-⇔ :  ∀ {n} {o o' ℓ ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
      → {F : Functor C D} {G : Functor C D} 
      → ⦃ _ : ∀ {x y} → H-Level (D .Precategory.Hom x y) n ⦄
      → H-Level (F ⇔ G) n
    hlevel-⇔ {n} {D = D} = hlevel-instance (Iso→is-hlevel! n eqv)
      

record SPwF-hom {o o' ℓ ℓ'}
  (S : SPwF o ℓ) (T : SPwF o' ℓ') : Type (lsuc (o ⊔ ℓ ⊔ o' ⊔ ℓ')) where
  module S = SPwF S
  module T = SPwF T

  field
    Fᶜ : Functor S.Con T.Con
    -- F-cont : is-meet-slat-hom Fᶜ S.Con-meet-slat T.Con-meet-slat
    Fᵗ : ∣ S.Ty ∣ → ∣ T.Ty ∣


  field
    pres-⊤ : Fᶜ F∘ !Const S.top ⇔ !Const T.top
    pres-∧ : Fᶜ F∘ S.×-functor ⇔ T.×-functor F∘ (Fᶜ F× Fᶜ)

    F-⊕ : ∀ {A} → Fᶜ F∘ S.extend A ⇔ T.extend (Fᵗ A) F∘ Fᶜ

    F^tm : ∀ {A} → S.Tm A => T.Tm (Fᵗ A) F∘ Functor.op Fᶜ

  -- bottom and top are automatically preserved by
  -- representability and the fact that F is a continuous
  -- monotone map. But we need to ensure that bottom and
  -- exponentialion is preserved.

  -- field
    -- F-⊥ : T.Tm T.model-⊥ ⇔ S.Tm S.model-⊥
    -- F-⇒ : ∀ {A B} → A T.model-⇒ B ≡ S.model-⇒
  
    
  -- F₀ : Fᶜ .hom
  -- F₁ : Fᶜ .pres-≤

private unquoteDecl eqv = declare-record-iso eqv (quote SPwF-hom)

-- module _ where
--   open SPwF-hom 

--   SPwF-hom-path  : ∀ {o o' ℓ ℓ'}
--     {S : SPwF o ℓ} {T : SPwF o' ℓ'} (F G : SPwF-hom S T)
--     → F .Fᶜ ≡ G .Fᶜ
--     → F .Fᵗ ≡ G .Fᵗ
--     → F ≡ G
--   SPwF-hom-path F G p q i .Fᶜ = p i  
--   SPwF-hom-path F G p q i .Fᵗ = q i
--   SPwF-hom-path {T = T} F G p q i .pres-⊤ = {! hlevel {T = (p i F∘ !Const (SPwF.top _)) ⇔ !Const top} 1 (pres-⊤ F) (pres-⊤ G) i   !} where open SPwF T
--   SPwF-hom-path F G p q i .pres-∧ = {!   !}
--   SPwF-hom-path F G p q i .F-⊕ = {!   !}
--   SPwF-hom-path F G p q i .F^tm = {!   !}

SPwF-hom-is-set : ∀ {o h} {C D : SPwF o h}
              → is-set (SPwF-hom C D)
SPwF-hom-is-set {o = o} {h} {C} {D} = Iso→is-hlevel! 2 eqv where instance
  Fset : H-Level (Functor (C .SPwF.Con) (D .SPwF.Con)) 2
  Fset = basic-instance 2 (Functor-is-set (SPwF.Con-str D))

instance
  H-Level-SPwF-hom : ∀ {n} {o h} {C D : SPwF o h} → H-Level (SPwF-hom C D) (2 + n)
  H-Level-SPwF-hom = basic-instance 2 SPwF-hom-is-set

record SPwF-hom-pres-T {o o' ℓ ℓ'}
  {S : SPwF o ℓ} {T : SPwF o' ℓ'} (F : SPwF-hom S T)
  {N : Theory o} {M : Theory o'} 
  (F' : Theory-hom N M)
  (S-N : is-T-model S N) (T-M : is-T-model T M)
  : Type (lsuc (o ⊔ ℓ ⊔ o' ⊔ ℓ')) where
  module S = SPwF S
  module T = SPwF T
  module N = Theory N
  module M = Theory M
  module S' = is-T-model S-N
  module T' = is-T-model T-M
  
  module F = SPwF-hom F
  module F' = Theory-hom F'
  
  field
    pres-atom : ∀ {A} → T'.atom (F'.F-atom A) ≡ F.Fᵗ (S'.atom A)
    -- pres-axiom : ∀ {Γ A} {ax} → ? ≡ T'.axiom (F'.F-axiom ax)
    
module _ where
  private instance
    H-Level-fun : ∀ {o ℓ} → {C : Precategory o ℓ} → {D : Precategory o ℓ}
                → ⦃ _ : H-Level (D .Precategory.Ob) 2 ⦄
                → H-Level (Functor C D) 2
    H-Level-fun {D = D} = basic-instance 2 (Functor-is-set (hlevel 2))
    
  instance
    unquoteDecl H-Level-SPwF-hom-pres-T = declare-record-hlevel 2 H-Level-SPwF-hom-pres-T (quote SPwF-hom-pres-T)

id-model-hom : ∀ {o ℓ} {S : SPwF o ℓ} → SPwF-hom S S
id-model-hom .SPwF-hom.Fᶜ = Id
id-model-hom {S = S} .SPwF-hom.pres-⊤ = Iff (λ x → SPwF.id S) λ x → SPwF.id S
id-model-hom {S = S} .SPwF-hom.pres-∧ = Iff (λ x → SPwF.id S) λ x → SPwF.id S
id-model-hom .SPwF-hom.Fᵗ x = x
id-model-hom {S = S} .SPwF-hom.F-⊕ = Iff (λ _ → S .SPwF.id) (λ _ → S .SPwF.id)
id-model-hom .SPwF-hom.F^tm = NT (λ _ x → x) λ x y f → trivial!
-- id-model-hom .SPwF-hom.F-⊥ = refl

id-model-hom-T : ∀ {o ℓ} {S : SPwF o ℓ} {N : Theory o} {T : is-T-model S N}
  → SPwF-hom-pres-T id-model-hom (unmake-theory-hom (Precategory.id (Th o))) T T
id-model-hom-T .SPwF-hom-pres-T.pres-atom = refl

-- comp-model-hom : ∀ {o ℓ} → {S T R : SPwF o ℓ}
--                  → (f : SPwF-hom T R) → (g : SPwF-hom S T)
--                  → SPwF-hom S R
-- comp-model-hom f g = scomp where
--   module F = SPwF-hom f
--   module G = SPwF-hom g

--   scomp : SPwF-hom _ _
--   scomp .SPwF-hom.Fᶜ = F.Fᶜ F∘ G.Fᶜ
--   scomp .SPwF-hom.Fᵗ = F.Fᵗ ⊙ G.Fᵗ
--   scomp .SPwF-hom.F-⊕ = {!   !}
--   scomp .SPwF-hom.F^tm = {!   !}
--   scomp .SPwF-hom.F-⊥ = {!   !}


postulate
  sorry : ∀ {o}{A : Type o} → A

Models : ∀ {o ℓ} → Displayed (Th o) (lsuc (o ⊔ ℓ)) (lsuc (o ⊔ ℓ))
Displayed.Ob[ Models {o} {ℓ} ] th = Σ[ S ∈ SPwF o ℓ ] is-T-model S th
Displayed.Hom[ Models ] th-hom (S , N) (T , M) 
  = Σ[ F ∈ SPwF-hom S T ] SPwF-hom-pres-T F (unmake-theory-hom th-hom) N M
Displayed.Hom[ Models ]-set f x y = hlevel 2
Models .Displayed.id' = id-model-hom , id-model-hom-T
Models .Displayed._∘'_ = sorry
Models .Displayed.idr' = sorry
Models .Displayed.idl' = sorry
Models .Displayed.assoc' = sorry

Mod : ∀ o ℓ → Precategory (lsuc (o ⊔ ℓ)) (lsuc (o ⊔ ℓ))
Mod o ℓ = ∫ (Models {o} {ℓ})

module Mod {o} {ℓ} = Displayed (Models {o} {ℓ})

Model : ∀ o ℓ → Type (lsuc (o ⊔ ℓ))
Model o ℓ = Mod o ℓ .Precategory.Ob


Mod→Th : ∀ {o ℓ} → Functor (Mod o ℓ) (Th o)
Mod→Th = πᶠ Models 


 
```                       