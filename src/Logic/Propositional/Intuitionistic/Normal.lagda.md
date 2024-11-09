```agda
module Logic.Propositional.Intuitionistic.Normal where

open import Cat.Prelude
open import Data.Maybe
open import Data.Dec.Base
open import Data.Sum
open import Logic.SimpleContext
open import Logic.Propositional.Intuitionistic
open import Logic.Propositional.Intuitionistic.Syntax


data NF-Imp {ℓ} {Ty : Type ℓ} : ℙrop Ty → ℙrop Ty → Type ℓ
data NF-ℙ {ℓ} {Ty : Type ℓ} : ℙrop Ty → Type ℓ

data NF-Limp {ℓ} {Ty : Type ℓ} : ℙrop Ty → Type ℓ where
  _′∧_ : (P Q : ℙrop Ty) → NF-Limp (P ′∧ Q)
  _′⇒_ : (P Q : ℙrop Ty) → NF-Limp (P ′⇒ Q)
  ↑_   : (a : Ty) → NF-Limp (↑ a)


data NF-Imp {ℓ} {Ty} where
  not : ∀ {x : ℙrop Ty} → NF-Limp x → NF-Imp x false
  top : ∀ {x : ℙrop Ty} → NF-Limp x → NF-Imp x true
  Curried : ∀ {x} → (L : NF-Limp x) → {y z : ℙrop Ty}
            → NF-Imp (x ′∧ y) z → NF-Imp x (y ′⇒ z)
  to-at  : ∀ {x : ℙrop Ty} → NF-Limp x → (y : Ty) → NF-Imp x (↑ y)
  to-prod : ∀ {x y z : ℙrop Ty} → NF-Limp x 
            → NF-Imp x y → NF-Imp x z → NF-Imp x (y ′∧ z)
  to-or : ∀ {x : ℙrop Ty} → NF-Limp x → (y z : ℙrop Ty) → NF-Imp x (y ′∨ z)

  Top-imp : ∀ {x : ℙrop Ty} → NF-ℙ x → NF-Imp true x
  False-imp : ∀ {x : ℙrop Ty} → NF-Imp false x

  Or-imp :  {x y z : ℙrop Ty} → NF-Imp x z → NF-Imp y z → NF-Imp (x ′∨ y) z

data NF-ℙ {ℓ} {Ty} where
  ↑_ : (x : Ty) → NF-ℙ (↑ x)
  _′∧_ : ∀ {x y : ℙrop Ty} → NF-ℙ x → NF-ℙ y → NF-ℙ (x ′∧ y)
  _′∨_ : ∀ (x y : ℙrop Ty) → NF-ℙ (x ′∨ y)
  top  : NF-ℙ true

  imp : ∀ {x y : ℙrop Ty} → NF-Imp x y → NF-ℙ (x ′⇒ y)

  fls : NF-ℙ false

data NF-ctx {ℓ} {Ty : Type ℓ} : Ctx (ℙrop Ty) → Type ℓ where
  [] : NF-ctx []
  _⨾_ : ∀ {Γ x} → NF-ctx Γ → NF-ℙ x → NF-ctx (Γ ⨾ x)



Reflect-Imp : ∀ {ℓ} {Ty : Type ℓ} {P Q} → NF-Imp {Ty = Ty} P Q → Ctx (ℙrop Ty)
Reflect-ℙ : ∀ {ℓ} {Ty : Type ℓ} {P} → NF-ℙ {Ty = Ty} P → Ctx (ℙrop Ty)

Reflect-Imp (not {P} _) = [] ⨾ (P ′⇒ false)
Reflect-Imp (top P) = []
Reflect-Imp (Curried x {y} {z} f) = Reflect-Imp f
Reflect-Imp (to-at {x = x} _ y) = ([] ⨾ (x ′⇒ (↑ y)))
Reflect-Imp (to-prod x f g) = Reflect-Imp f <> Reflect-Imp g
Reflect-Imp (to-or {x = x} _ p q) = ([] ⨾ (x ′⇒ (p ′∨ q)))
Reflect-Imp (Top-imp x) = Reflect-ℙ x
-- Reflect-Imp (And-imp x y z) = [] ⨾ ((x ′∧ y) ′⇒ z)
-- Reflect-Imp (At-imp x y) = [] ⨾ ((↑ x) ′⇒ y)
Reflect-Imp (Or-imp f g) = Reflect-Imp f <> Reflect-Imp g
Reflect-Imp False-imp = []

Reflect-ℙ (↑ x) = [] ⨾ (↑ x)
Reflect-ℙ (P ′∧ Q) = Reflect-ℙ P <> Reflect-ℙ Q
Reflect-ℙ (P ′∨ Q) = [] ⨾ (P ′∨ Q)
Reflect-ℙ (imp x) = Reflect-Imp x
Reflect-ℙ top = []
Reflect-ℙ fls = [] ⨾ false

Reflect : ∀ {ℓ} {Ty : Type ℓ} {Γ} → NF-ctx {Ty = Ty} Γ → Ctx (ℙrop Ty)
Reflect [] = []
Reflect (Γ ⨾ x) = (Reflect Γ) <> Reflect-ℙ x

Reify-imp : ∀ {ℓ} {Ty : Type ℓ} → (P Q : ℙrop Ty) → NF-Imp P Q
Reify-ty : ∀ {ℓ} {Ty : Type ℓ} → (P : ℙrop Ty) → NF-ℙ P

Reify-limp : ∀ {ℓ} {Ty : Type ℓ} {P : ℙrop Ty} → (P' : NF-Limp P)
          →  (Q : ℙrop Ty) → NF-Imp P Q
Reify-limp L (↑ x) = to-at L x
Reify-limp L (P ′∧ Q) = to-prod L (Reify-imp _ P) (Reify-imp _ Q)
Reify-limp L (P ′∨ Q) = to-or L P Q
Reify-limp L (P ′⇒ Q) = Curried L (Reify-imp _ Q)
Reify-limp L true = top L
Reify-limp L false = not L

Reify-imp (P ′∨ Q) R = Or-imp (Reify-imp P R) (Reify-imp Q R)
Reify-imp true Q = Top-imp (Reify-ty Q)
Reify-imp false Q = False-imp
Reify-imp (↑ x) Q = Reify-limp (↑ x) Q
Reify-imp (P ′∧ Q) R = Reify-limp (P ′∧ Q) R
Reify-imp (P ′⇒ Q) R = Reify-limp (P ′⇒ Q) R

Reify-ty (↑ x) = ↑ x
Reify-ty (P ′∧ Q) = (Reify-ty P) ′∧ Reify-ty Q
Reify-ty (P ′∨ Q) = P ′∨ Q
Reify-ty (P ′⇒ Q) = imp (Reify-imp P Q)
Reify-ty true = top
Reify-ty false = fls
    
Reify : ∀ {ℓ} {Ty : Type ℓ} → (Γ : Ctx (ℙrop Ty)) → NF-ctx Γ
Reify [] = []
Reify (Γ ⨾ x) = Reify Γ ⨾ Reify-ty x

Normalise : ∀ {ℓ} {Ty : Type ℓ} → Ctx (ℙrop Ty) → Ctx (ℙrop Ty)
Normalise = Reflect ⊙ Reify
```

For every context $\Gamma$, the type `NF-ctx Γ`
is contractible. 

```agda
NF-ctx-is-contr : ∀ {ℓ} {Ty : Type ℓ} (Γ : Ctx (ℙrop Ty))
   → is-contr (NF-ctx Γ)
NF-ctx-is-contr Γ = contr (Reify Γ) II where
  II-⇒ : ∀ {t r} → (t' : NF-Imp t r) → Reify-imp t r ≡ t'
  II-ty : ∀ {t} → (t' : NF-ℙ t) → Reify-ty t ≡ t'
  
  IIII-Limp : ∀ {t} → (f g : NF-Limp t) → f ≡ g
  IIII-Limp (.P ′∧ .Q) (P ′∧ Q) = refl
  IIII-Limp (.P ′⇒ .Q) (P ′⇒ Q) = refl
  IIII-Limp (↑ .a) (↑ a) = refl

  III-Limp : ∀ {t r} → (t' : NF-Limp t) → (f : NF-Imp t r) → Reify-limp t' r ≡ f
  II-Limp : ∀ {t r} → (t' : NF-Limp t) → (f : NF-Imp t r) → Reify-imp t r ≡ f
  
  III-Limp t' (not x) = ap not (IIII-Limp t' x)
  III-Limp t' (top x) = ap top (IIII-Limp t' x)
  III-Limp t' (Curried L f) i = Curried (IIII-Limp t' L i) (III-Limp (_ ′∧ _) f i)
  III-Limp t' (to-at x y) = ap (λ x → to-at x y) (IIII-Limp t' x)
  III-Limp t' (to-prod x f g) i 
    = to-prod (IIII-Limp t' x i) (II-Limp x f i) (II-Limp x g i)
  III-Limp t' (to-or x y z) i = to-or (IIII-Limp t' x i) y z

  II-Limp t' (not (P ′∧ Q)) = refl 
  II-Limp t' (not (P ′⇒ Q)) = refl
  II-Limp t' (not (↑ a)) = refl
  II-Limp t' (top (P ′∧ Q)) = refl
  II-Limp t' (top (P ′⇒ Q)) = refl
  II-Limp t' (top (↑ a)) = refl
  II-Limp t' (to-at (P ′∧ Q) y) = refl
  II-Limp t' (to-at (P ′⇒ Q) y) = refl
  II-Limp t' (to-at (↑ a) y) = refl
  II-Limp t' (to-or (P ′∧ Q) y z) = refl
  II-Limp t' (to-or (P ′⇒ Q) y z) = refl
  II-Limp t' (to-or (↑ a) y z) = refl
  II-Limp t' (to-prod (P ′∧ Q) f g) = ap₂ (to-prod _) (III-Limp _ f) (III-Limp _ g)
  II-Limp t' (to-prod (P ′⇒ Q) f g) = ap₂ (to-prod _) (III-Limp _ f) (III-Limp _ g)
  II-Limp t' (to-prod (↑ a) f g) = ap₂ (to-prod _) (III-Limp _ f) (III-Limp _ g)
  II-Limp t' (Curried (P ′∧ Q) f) = ap (Curried _) (III-Limp _ f)
  II-Limp t' (Curried (P ′⇒ Q) f) = ap (Curried _) (III-Limp _ f)
  II-Limp t' (Curried (↑ a) f) = ap (Curried _) (III-Limp _ f)

  II-⇒ (not x) = II-Limp x (not x)
  II-⇒ (top x) = II-Limp x (top x)
  II-⇒ (Curried L t) = II-Limp L (Curried L t)
  II-⇒ (to-at x y) = II-Limp x (to-at x y)
  II-⇒ (to-prod x t t₁) = II-Limp x (to-prod x t t₁)
  II-⇒ (to-or x y z) = II-Limp x (to-or x y z)
  II-⇒ (Top-imp x) = ap Top-imp (II-ty x)
  II-⇒ False-imp = refl
  II-⇒ (Or-imp t t₁) = ap₂ Or-imp (II-⇒ t) (II-⇒ t₁)

  II-ty (↑ x) = refl
  II-ty (t ′∧ r) i = II-ty t i ′∧ II-ty r i
  II-ty (x ′∨ y) = refl
  II-ty top = refl
  II-ty (imp x) = ap imp (II-⇒ x)
  II-ty fls = refl
  
  II : ∀ {Γ} → (Γ' : NF-ctx Γ) → Reify Γ ≡ Γ'
  II [] = refl
  II (Γ' ⨾ x) i = (II Γ' i) ⨾ II-ty x i


```

```agda

module Normal {ℓ} (T : Theory ℓ) where
  open Theory T
  open Syn T
  
  falso-ctx : ∀ {Γ Δ} → false ∈ Γ → Sub _⊢_ Γ Δ
  falso-ctx {Δ = []} v = ε
  falso-ctx {Δ = Δ ⨾ x} v = (falso-ctx v) ⦊ (falso v)

  Norm-imp : ∀ (P Q : ℙrop Atom) → Reflect-Imp (Reify-imp P Q) ⊢ (P ′⇒ Q)
  RefRei : ∀ (x : ℙrop Atom) → Reflect-ℙ (Reify-ty x) ⊢ x
  
  Norm-limp : ∀ {P} (P' : NF-Limp P) (Q : ℙrop Atom) → Reflect-Imp (Reify-limp P' Q) ⊢ (P ′⇒ Q)
  Norm-limp P (↑ x) = assume (apply1 (exact (there here)) (exact here))
  Norm-limp P (Q ′∧ R) = assume (intro-∧ 
    (apply1 (ren-tm π₁-rn (Norm-imp _ Q)) (exact here))
    (apply1 (ren-tm (drop-rn π₂-rn) (Norm-imp _ R)) (exact here)))
  Norm-limp P (Q ′∨ R) = exact here
  Norm-limp P (Q ′⇒ R) = assume (
      assume (
        apply1 
         (ren-tm π₁-rn (Norm-limp _ R))
         (intro-∧ (exact (there here)) (exact here))))
  Norm-limp P true = assume triv
  Norm-limp P false = assume (apply1 (exact (there here)) (exact here))

  Norm-imp (P ′∨ P₁) Q = assume (elim-∨ (exact here) 
    (apply1 (ren-tm π₁-rn (Norm-imp P Q)) (exact here))
    
     (apply1 (ren-tm (π₂-rn ∘sub π₁-rn {Δ = ([] ⨾ (P ′∨ P₁)) ⨾ P₁}) (Norm-imp P₁ Q))
      (exact here)))
  Norm-imp true Q = assume (ren-tm π₁-rn (RefRei Q))
  Norm-imp false Q = assume (falso here)
  Norm-imp (P ′⇒ Q) R = Norm-limp (P ′⇒ Q) R
  Norm-imp (P ′∧ Q) R = Norm-limp (P ′∧ Q) R
  Norm-imp (↑ x) Q = Norm-limp (↑ x) Q

  RefRei (↑ x) = exact here
  RefRei (x ′∧ x₁) = intro-∧ (ren-tm (π₁-rn {Γ = Reflect-ℙ (Reify-ty x)}) (RefRei x))
                       (ren-tm (π₂-rn {Δ = Reflect-ℙ (Reify-ty x₁)}) (RefRei x₁))
  RefRei (x ′∨ x₁) = exact here
  RefRei (P ′⇒ Q) = Norm-imp P Q
  RefRei true = triv
  RefRei false = exact here

  Nf→id : ∀ (Γ : Ctx (ℙrop Atom)) → Sub _⊢_ (Normalise Γ) Γ
  Nf→id [] = ε
  Nf→id (Γ ⨾ (↑ x)) = keep-sub (Nf→id Γ)
  Nf→id (Γ ⨾ (x ′∧ x₁)) = (Nf→id Γ ∘sub π₁-sub) 
    ⦊ intro-∧ (ren-tm (π₁-rn ∘sub π₂-rn {Γ = Normalise Γ}) (RefRei x))
           (ren-tm (π₂-rn ∘sub π₂-rn {Γ = Normalise Γ}) (RefRei x₁))
  Nf→id (Γ ⨾ (x ′∨ x₁)) = (drop-sub (Nf→id Γ)) ⦊ exact here
  Nf→id (Γ ⨾ p@(x ′⇒ x₁)) = (Nf→id Γ ∘sub π₁-sub) 
    ⦊ ren-tm π₂-rn (RefRei p)
  Nf→id (Γ ⨾ true) = (Nf→id Γ) ⦊ triv
  Nf→id (Γ ⨾ false) = falso-ctx here

  unNorm-imp : ∀ {Γ} → (p q : ℙrop Atom) → Sub _⊢_ (Γ ⨾ (p ′⇒ q)) (Reflect-Imp (Reify-imp p q))
  id→Nf-ty : ∀ {Γ : Ctx (ℙrop Atom)} → (t : ℙrop Atom) → Sub _⊢_ (Γ ⨾ t) (Reflect-ℙ (Reify-ty t))
  
  unNorm-limp : ∀ {Γ p} → (p' : NF-Limp p) → (q : ℙrop Atom)
       → Sub _⊢_ (Γ ⨾ (p ′⇒ q)) (Reflect-Imp (Reify-limp p' q))
  unNorm-limp p' (↑ x) = ε ⦊ (exact here)
  unNorm-limp p' true = ε
  unNorm-limp p' false = ε ⦊ (exact here)
  unNorm-limp p' (q ′∨ q₁) = ε ⦊ (exact here)
  unNorm-limp {Γ} {p} _ (q ′∧ q₁) 
    = ⟨⟩-sub {Γ = Γ ⨾ _} {Δ = Reflect-Imp (Reify-imp p q)} 
      (unNorm-imp {Γ} p q ∘sub (π₁-sub ⦊ assume (fst-∧ (apply1 (exact (there here)) (exact here)))))
       (unNorm-imp {Γ} p q₁ ∘sub (π₁-sub ⦊ assume (snd-∧ (apply1 (exact (there here)) (exact here)))))
  unNorm-limp {Γ} {p} p' (q ′⇒ q₁) = unNorm-limp {Γ} (p ′∧ q) q₁ ∘sub 
    (π₁-sub ⦊ assume (apply1 (apply1 (exact (there here)) (fst-∧ (exact here)))
     (snd-∧ (exact here))))


  unNorm-imp {Γ} (p ′∨ p₁) q = ⟨⟩-sub {Γ = _ ⨾ _} {Δ = Reflect-Imp (Reify-imp p q)}
     (unNorm-imp {Γ} p q ∘sub (π₁-sub ⦊ assume (apply1 (exact (there here)) (left-∨ (exact here)))))
    (unNorm-imp {Γ} p₁ q ∘sub (π₁-sub ⦊ assume (apply1 (exact (there here)) (right-∨ (exact here)))))
  unNorm-imp {Γ} true q = id→Nf-ty {Γ} q ∘sub (π₁-sub ⦊ apply1 (exact here) triv)
  unNorm-imp false q = ε
  unNorm-imp (p ′⇒ p₁) q = unNorm-limp (p ′⇒ p₁) q
  unNorm-imp (↑ x) q = unNorm-limp (↑ x) q
  unNorm-imp (p ′∧ p₁) q = unNorm-limp (p ′∧ p₁) q

  id→Nf-ty (↑ x) = ε ⦊ (exact here)
  id→Nf-ty {Γ} (t ′∧ t₁) = ⟨⟩-sub {Γ = _ ⨾ (t ′∧ t₁)} {Δ = Reflect-ℙ (Reify-ty t)}
     ((id→Nf-ty {Γ} t) ∘sub (π₁-sub ⦊ (fst-∧ (exact here))))
      (id→Nf-ty {Γ} t₁ ∘sub (π₁-sub ⦊ snd-∧ (exact here)))
  id→Nf-ty (t ′∨ t₁) = ε ⦊ (exact here)
  id→Nf-ty (t ′⇒ t₁) = unNorm-imp t t₁
  id→Nf-ty true = ε
  id→Nf-ty false = ε ⦊ (exact here)

  
  id→Nf : ∀ (Γ : Ctx (ℙrop Atom)) → Sub _⊢_ Γ (Normalise Γ)
  id→Nf [] = ε
  id→Nf (Γ ⨾ (↑ x)) = (drop-sub (id→Nf Γ)) ⦊ (exact here)
  id→Nf (Γ ⨾ (x ′∧ y)) = ⟨⟩-sub {Δ = Normalise Γ} (drop-sub (id→Nf Γ))
     ((⟨⟩-sub {Δ = Reflect-ℙ (Reify-ty x)} 
      (id→Nf-ty {Γ} x ∘sub (π₁-sub ⦊ fst-∧ (exact here)))
      (id→Nf-ty {Γ} y ∘sub (π₁-sub ⦊ snd-∧ (exact here)))))
  id→Nf (Γ ⨾ (x ′∨ y)) = (drop-sub (id→Nf Γ)) ⦊ (exact here)
  id→Nf (Γ ⨾ (x ′⇒ y)) = ⟨⟩-sub {Γ = Γ ⨾ _} {Δ = Normalise Γ}
     (id→Nf Γ ∘sub π₁-sub) (id→Nf-ty _)
  id→Nf (Γ ⨾ true) = drop-sub (id→Nf Γ)
  id→Nf (Γ ⨾ false) = falso-ctx here


  fully-fathful : ∀ {Γ Δ} → Sub _⊢_ (Normalise Γ) (Normalise Δ) → Sub _⊢_ Γ Δ
  fully-fathful {Γ} {Δ} f = (Nf→id Δ ∘sub f) ∘sub id→Nf Γ

  fully-fathful' : ∀ {Γ Δ} → Sub _⊢_ Γ Δ → Sub _⊢_ (Normalise Γ) (Normalise Δ)
  fully-fathful' {Γ} {Δ} f = id→Nf Δ ∘sub (f ∘sub Nf→id Γ)



  Dec→Dec : ∀ {Γ Δ} → Dec (Sub _⊢_ (Normalise Γ) (Normalise Δ)) → Dec (Sub _⊢_ Γ Δ)
  Dec→Dec d with d
  ... | yes a = yes $ fully-fathful a
  ... | no ¬a = no (λ x → ¬a (fully-fathful' x))

  inl-reflect : ∀ {Γ} {t r} {Γ' : NF-ctx Γ} {t' : NF-ℙ t}
                → (Sub _⊢_ (Reflect Γ') (Reflect-ℙ t'))
                → (Reflect Γ') ⊢ (t ′∨ r)
  inl-reflect {Γ' = Γ'} f 
    = subst
       (rec! λ p q → Reflect p ⊢ Reflect-ℙ q)
        (NF-ctx-is-contr _ .paths Γ' ,ₚ {!   !})
         (tm (lemma f)) where
    lemma : ∀ {Γ} {t r}
            → (Sub _⊢_ (Normalise Γ) (Reflect-ℙ (Reify-ty t))) 
            → Sub _⊢_ (Normalise Γ) (Reflect-ℙ (Reify-ty (t ′∨ r)))
    lemma {Γ} {t} {r} σ 
      =    fully-fathful' {Γ ⨾ t} {[] ⨾ (t ′∨ r)} (ε ⦊ (left-∨ (exact here)))
      ∘sub ⟨⟩-sub id-sub σ

    tm : ∀ {Γ t} → Sub _⊢_ Γ ([] ⨾ t) → Γ ⊢ t
    tm (ε ⦊ t) = t



  -- The normalised var type has to be a little more precise
  --  it needs to take into account that a tormal type could be a number of 
  --  types once Reflected, and so the normal vars allow you to 'break-down'
  --  things like products
  data NF-⇒-var {Γ : Ctx (ℙrop Atom)} (Γ' : NF-ctx Γ) : ∀ {t r s : ℙrop Atom}
              (f : NF-Imp t r) (s' : NF-ℙ s) 
              (v : Ren (Reflect (Γ' ⨾ imp f)) (Reflect-ℙ s'))
              → Type ℓ where
    not : ∀ {t} (t' : NF-Limp t)
           →  NF-⇒-var Γ' (not t') (imp (not t')) (ε ⦊ here)
    to-at : ∀ {t} (t' : NF-Limp t) (r : Atom) 
            → NF-⇒-var Γ' (to-at t' r) (imp (to-at t' r)) (ε ⦊ here)

    to-or : ∀ {t} (t' : NF-Limp t) {r s} 
            → NF-⇒-var Γ' (to-or t' r s) (imp (to-or t' r s)) (ε ⦊ here)

    to-prod-fst : ∀ {t r s} (t' : NF-Limp t) {f : NF-Imp t r} (g : NF-Imp t s)
            → NF-⇒-var Γ' (to-prod t' f g) (imp f) (π₁-rn ∘sub π₂-rn {Γ = Reflect Γ'})
    to-prod-snd : ∀ {t r s} (t' : NF-Limp t) (f : NF-Imp t r) {g : NF-Imp t s}
            → NF-⇒-var Γ' (to-prod t' f g) (imp g) (π₂-rn ∘sub π₂-rn {Γ = Reflect Γ'})

    Curried : ∀ {t} {t' : NF-Limp t} {r s} → (f : NF-Imp (t ′∧ r) s)
              → NF-⇒-var Γ' (Curried t' f) (imp f) π₂-rn


    or-imp-fst : ∀ {t r s} → (f : NF-Imp t s) → (g : NF-Imp r s)
                 → NF-⇒-var Γ' (Or-imp f g) (imp f) (π₁-rn ∘sub π₂-rn {Γ = Reflect Γ'})
    or-imp-snd : ∀ {t r s} → (f : NF-Imp t s) → (g : NF-Imp r s)
                 → NF-⇒-var Γ' (Or-imp f g) (imp g) (π₂-rn ∘sub π₂-rn {Γ = Reflect Γ'})                 

    Top-imp : ∀ {x} {x' : NF-ℙ x} → NF-⇒-var Γ' (Top-imp x') x' π₂-rn

  data NF-var : ∀ {Γ : Ctx (ℙrop Atom)} (Γ' : NF-ctx Γ)
      {t : ℙrop Atom}  (t' : NF-ℙ t) (v : Ren (Reflect Γ') (Reflect-ℙ t'))
       → Type ℓ where
    here↑ : ∀ {Γ} {Γ' : NF-ctx Γ} {t : Atom} 
             → NF-var (Γ' ⨾ (↑ t)) (↑ t) (ε ⦊ here)
             
    here∨ : ∀ {Γ} {Γ' : NF-ctx Γ} {t r}
             → NF-var (Γ' ⨾ (t ′∨ r)) (t ′∨ r) (ε ⦊ here)

    here-fls : ∀ {Γ} {Γ' : NF-ctx Γ} → NF-var (Γ' ⨾ fls) fls (ε ⦊ here)

    here-fst : ∀ {Γ} {Γ' : NF-ctx Γ} {t r} {t' : NF-ℙ t} {r' : NF-ℙ r}
      → NF-var (Γ' ⨾ (t' ′∧ r')) t' (π₁-rn ∘sub π₂-rn {Γ = Reflect Γ'})
    here-snd : ∀ {Γ} {Γ' : NF-ctx Γ} {t r} {t' : NF-ℙ t} {r' : NF-ℙ r}
      → NF-var (Γ' ⨾ (t' ′∧ r')) r' (π₂-rn ∘sub π₂-rn {Γ = Reflect Γ'})

    here-imp : ∀ {Γ} {Γ' : NF-ctx Γ} {t r} {f : NF-Imp t r}
              → NF-var (Γ' ⨾ imp f) (imp f) π₂-rn

    drop : ∀ {Γ} {Γ' : NF-ctx Γ} {t} {t' : NF-ℙ t} {r} (r' : NF-ℙ r) 
              {v : Ren (Reflect Γ') (Reflect-ℙ t')}
            → NF-var Γ' t' v → NF-var (Γ' ⨾ r') t' (v ∘sub π₁-rn)


  data NF-⇒-term {Δ} (Δ' : NF-ctx Δ) : ∀ {Γ : Ctx (ℙrop Atom)} (Γ' : NF-ctx Γ)
      {t r : ℙrop Atom}  (t' : NF-Imp t r) (ρ : Ren (Reflect Δ') (Reflect Γ')) → Type ℓ where
   

  

  data NF-term : ∀ {Γ : Ctx (ℙrop Atom)} {t : ℙrop Atom}
      (Γ' : NF-ctx Γ) (t' : NF-ℙ t) (tm : Sub _⊢_ (Reflect Γ') (Reflect-ℙ t'))  → Type ℓ where
    exact : ∀ {Γ} {Γ' : NF-ctx Γ} {t} {t' : NF-ℙ t} 
              {v : Ren (Reflect Γ') (Reflect-ℙ t')}
             → NF-var Γ' t' v →  NF-term Γ' t' (ι₁ v)

    intro-∧ : ∀ {Γ} {Γ' : NF-ctx Γ} {t r} {t' : NF-ℙ t} {r' : NF-ℙ r}
              → {τ : Sub _⊢_ (Reflect Γ') (Reflect-ℙ t')}
              → NF-term Γ' t' τ
              → {ρ : Sub _⊢_ (Reflect Γ') (Reflect-ℙ r')}
              → NF-term Γ' r' ρ
              → NF-term Γ' (t' ′∧ r') (⟨⟩-sub τ ρ)

    
    triv : ∀ {Γ} {Γ' : NF-ctx Γ} → NF-term Γ' top ε

    -- inl-∨ : ∀ {Γ} {Γ' : NF-ctx Γ} {t r} {t' : NF-ℙ t} {r' : NF-ℙ r}
    --            → {τ : Sub _⊢_ (Reflect Γ') (Reflect-ℙ t')}
    --            → NF-term Γ' t' τ → NF-term Γ' (t ′∨ r) {!   !}
    

  -- -- A normal form var is more than just a variable
  -- --  it also considers variables that are the result of an application
  -- --  it is important that it is as an index as opposed to directly refering to
  -- --  NF-tm in the constructors because the arguments may be 'later' in the tree
  -- data NF-var Δ' where
  --   exactly-here : ∀ {Γ} {Γ' : NF-ctx Γ} {t} {t' : NF-ℙ t} 
  --            → {ρ : Sub (Reflect Δ') (Reflect $ Γ' ⨾ t')}
  --            → NF-var Δ' (Γ' ⨾ t') t' ρ

  --   imp-here : ∀ {Γ} {Γ' : NF-ctx Γ} {t r} {t' : NF-Imp t r} 
  --            → {ρ : Sub (Reflect Δ') (Reflect Γ')}
  --            → NF-⇒-term Δ' Γ' t' ρ → NF-var Δ' Γ' (imp t') ρ

  --   drop : ∀ {Γ} {Γ' : NF-ctx Γ} {t} {t' : NF-ℙ t} {r} (r' : NF-ℙ r) 
  --            {ρ : Sub (Reflect Δ') (Reflect Γ')}
  --           → (x : NF-var Δ' Γ' t' ρ) → NF-var Δ' (Γ' ⨾ r') t' {!   !}


  -- data NF-term : ∀ {Γ : Ctx (ℙrop Atom)} {t : ℙrop Atom}
  --     (Γ' : NF-ctx Γ) (t' : NF-ℙ t) {-(tm : Γ ⊢ t)-}  → Type ℓ where
  --   applyN : ∀ {Γ} {Γ' : NF-ctx Γ} {t} {t' : NF-ℙ t} {a} {a' : NF-ℙ a}
  --            → NF-var Γ' t' a' → NF-term Γ' a' → NF-term Γ' t' 

  --   intro-∧ : ∀ {Γ} {Γ' : NF-ctx Γ} {t r} {t' : NF-ℙ t} {r' : NF-ℙ r}
  --                → NF-term Γ' t' → NF-term Γ' r' → NF-term Γ' (t' ′∧ r')

  --   -- assume  : ∀ {Γ} {Γ' : NF-ctx Γ} {t r} {t' : NF-ℙ t} {r' : NF-ℙ r}
  --   --           → NF-⇒-term (Γ' ⨾ t') r' → NF-term Γ' (t' ′⇒ r')

  --   triv : ∀ {Γ} {Γ' : NF-ctx Γ} → NF-term Γ' top

  --   intro-∨ : ∀ {Γ} {Γ' : NF-ctx Γ} {t r} {t' : NF-ℙ t} {r' : NF-ℙ r}
  --           → NF-term Γ' t' ⊎ NF-term Γ' r' → NF-term Γ' (t ′∨ r)

  --   fst-∨ : ∀ {Γ} {Γ' : NF-ctx Γ} {t r} {t' : NF-ℙ t} {r' : NF-ℙ r}
  --           → NF-term Γ' (t' ′∧ r') → NF-term Γ' t'

  --   snd-∨ : ∀ {Γ} {Γ' : NF-ctx Γ} {t r} {t' : NF-ℙ t} {r' : NF-ℙ r}
  --           → NF-term Γ' (t' ′∧ r') → NF-term Γ' r'

  -- data Sat {ℓ} (A : Type ℓ) (B : A → Type ℓ) : Type ℓ where
  --   yes : (a : A) → B a → Sat A B
  --   no :  ((a : A) → ¬ (B a)) → Sat A B

  -- no-var[] : ∀ {t a} (t' : NF-ℙ t) (a' : NF-ℙ a) → ¬ (NF-var [] t' a')
  -- no-var[] t a (imp-here (Or-have x x₁)) = no-var[] _ _ x
  -- no-var[] t a (imp-here (Curry-have x)) = no-var[] _ _ x
  -- no-var[] t a (imp-here (to-prod x x₁)) = no-var[] _ _ x

  
  -- postulate instance
  --   ℙrop-disc : Discrete (ℙrop Atom)
  --   Reflect-equiv : ∀ {x : ℙrop Atom} (x' y' : NF-ℙ x) → x' ≡ᵢ y' 

  -- not-here : ∀ {Γ x t a} {Γ' : NF-ctx Γ} {x' : NF-ℙ x} {t' : NF-ℙ t} {a' : NF-ℙ a}
  --            → ¬ (x ≡ᵢ t)
  --            → NF-var (Γ' ⨾ x') t' a' → NF-var Γ' t' a' 
  -- not-here = {!   !}

  -- var? : ∀ {Γ t} (Γ' : NF-ctx Γ) (t' : NF-ℙ t)
  --         → Sat (Σ _ NF-ℙ) (λ (a , a') → NF-var Γ' t' {a} a')
  -- var? [] t = no (λ a →  no-var[] t (a .snd) )
  -- var? {_} {t} (_⨾_ {Γ} {x} Γ' x')  t' = case x ≡ᵢ? t of λ where 
  --   (yes reflᵢ) → case Reflect-equiv x' t' of λ where 
  --     reflᵢ → yes (true , top) exactly-here
  --   (no ¬a) → case (var? Γ' t') of λ where
  --     (yes a x) → yes a (drop _ x)
  --     (no x) → no (λ a x₂ → x a (not-here ¬a x₂)) 


  -- -- Sat-∨? : 

  -- Sat-NF? : ∀ {Γ t} (Γ' : NF-ctx Γ) (t' : NF-ℙ t) 
  --           → Dec (NF-term Γ' t')
  -- Sat-NF? Γ top = yes triv
  -- Sat-NF? Γ (t ′∧ t₁) = case (Sat-NF? Γ t , Sat-NF? Γ t₁) of λ where 
  --     (yes a) (yes a₁) → yes (intro-∧ a a₁)
  --     (yes a) (no ¬a) → no (λ x₁ → ¬a (snd-∨ x₁))
  --     (no ¬a) x₁ → no (λ x → ¬a (fst-∨ x))
  -- -- for the following cases we need to know whether a variable can discharge the 
  -- -- proof first:
  -- Sat-NF? Γ (imp x) = case (var? Γ (imp x)) of λ where
  --    (yes a x) → case Sat-NF? Γ (a .snd) of λ where 
  --     → {!   !}
  --    (no x) → {!   !}

  -- Sat-NF? Γ (x ′∨ y) = case (var? Γ (x ′∨ y)) of λ where
  --    (yes a x) → case (Sat-NF? Γ (a .snd)) of λ where 
  --         (yes a) → yes (applyN x a)
  --         (no ¬a) → {!   !}
  --    (no x) → {!   !}
  -- --  = case (Sat-NF? Γ (Reify-ty x) , Sat-NF? Γ (Reify-ty y)) of λ where
  -- --     (yes a) b → yes (intro-∨ {r' = Reify-ty y} (inl a))
  -- --     (no ¬a) (yes a) → yes (intro-∨ {t' = Reify-ty x} (inr a))
  -- --     (no ¬a) (no ¬a₁) → no (λ x₁ → {!   !})

  -- Sat-NF? Γ (↑ x) = case (var? Γ (↑ x)) of λ where
  --    (yes a x) → case Sat-NF? Γ (a .snd) of λ where 
  --     → {!   !}
  --    (no x) → {!   !}
  -- Sat-NF? Γ fls = case (var? Γ fls) of λ where
  --    (yes a x) → case Sat-NF? Γ (a .snd) of λ where 
  --     → {!   !}
  --    (no x) → {!   !}

  -- Sat-ty? : ∀ Γ t → Dec (Sub _⊢_ (Normalise Γ) (Reflect-ℙ (Reify-ty t)))
  -- Sat-ty? Γ (↑ x) = {!   !}
  -- Sat-ty? Γ (t ′∧ t₁) = {!   !}
  -- Sat-ty? Γ (t ′∨ t₁) = {!   !}
  -- Sat-ty? Γ (t ′⇒ t₁) = {!   !}
  -- Sat-ty? Γ true = {!   !}
  -- Sat-ty? Γ false = {!   !}
 
  -- Sat? : ∀ Γ Δ → Dec (Sub _⊢_ (Normalise Γ) (Normalise Δ)) 
  -- Sat? Γ [] = yes ε
  -- Sat? Γ (Δ ⨾ x) = case (Sat? Γ Δ , Sat-ty? Γ x) of λ where 
  --   (yes a) (yes b) → yes (⟨⟩-sub {Γ = Normalise Γ} {Δ = Normalise Δ}
  --      a b)
  --   (yes a) (no ¬a) → no (λ x → ¬a (π₂-sub ∘sub x))
  --   (no ¬a) y → no (λ x → ¬a (π₁-sub ∘sub x))
```         