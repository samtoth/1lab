```agda
-- {-# OPTIONS --allow-unsolved-metas #-}
```

# Intuitionistic propositional logic

Looking at categorical semantics of the propositional fragment of
lean covered in the first few lectures. 

```agda
open import Cat.Prelude
open import Order.Base
open import Order.Instances.Props
open import Data.Sum.Base
open import Data.Dec.Base
open import Data.Power
open import Data.Power.Complemented

module Logic.Propositional.Decidable {o ℓ} (B : Poset o ℓ)  where

open Poset B
plvl = o ⊔ ℓ
```

Firstly, we parameterize over a poset which repesent
constants in the theory. Objects of the poset are
atomic propositions, and there is a hom between props
iff there is an implication.

(Actually now I think this is not the right thing
  to parameterize over as the constants should be defined
  by all posible formulars built out of the atomic propositions.
  E.g you ought to be able to say $A \and B ≤ C$)


```agda
data ℙrop : Type plvl where
  ↑ : Ob → ℙrop
  _′∧_ : ℙrop → ℙrop → ℙrop
  _′∨_ : ℙrop → ℙrop → ℙrop
  _′⇒_  : ℙrop → ℙrop → ℙrop
  true false : ℙrop
```

```agda
data Ctx : Type plvl where
  []  : Ctx
  _⨾_ : Ctx → ℙrop → Ctx

_++_ : Ctx → Ctx → Ctx
Γ ++ [] = Γ
Γ ++ (θ ⨾ P) = (Γ ++ θ) ⨾ P


data _∈ᶜ_ (P : ℙrop) : Ctx → Type plvl where
  here  : ∀ {Γ} → P ∈ᶜ (Γ ⨾ P)
  there : ∀ {Γ Q} → P ∈ᶜ Γ → P ∈ᶜ (Γ ⨾ Q)
```
<!--
```agda
instance
  Membership-Ctx : Membership ℙrop Ctx plvl
  Membership-Ctx = record { _∈_ = _∈ᶜ_ }

infixr 12 _′⇒_
infixr 11 _′∧_
infixr 10 _′∨_
infixl 10 _⨾_
infix 9  _⊨_

private variable
  P Q R S : ℙrop
  Γ Δ Θ : Ctx

```
-->

Now I want to encode Thorston's propositional subset of lean.
The following is not exactly the same
as the tactics used, as it is in the form of a tree
which is nicer to work with and think about that a list
of tactics. It should be not so difficult to 'linearize'
it into tactics after the fact. 

We also define a category of renamings in the obvious way.

```agda
data TLS : Ctx → ℙrop → Type plvl where
  -- ↑ : {A B : Ob} → A ≤ B → TLS (Γ ⨾ ↑ A) (↑ B)

  triv : TLS Γ true

  exact : P ∈ Γ → TLS Γ P
  falso : false ∈ Γ → TLS Γ P

  assume : TLS (Γ ⨾ P) Q → TLS Γ (P ′⇒ Q)
  apply1 : TLS Γ (P ′⇒ Q) → (TLS Γ P → TLS Γ Q)

  intro-∧ : TLS Γ P → TLS Γ Q → TLS Γ (P ′∧ Q)
  fst-∧   : TLS Γ (P ′∧ Q) → TLS Γ P
  snd-∧   : TLS Γ (P ′∧ Q) → TLS Γ Q  

  left-∨  : TLS Γ P → TLS Γ (P ′∨ Q)
  right-∨ : TLS Γ Q → TLS Γ (P ′∨ Q)
  elim-∨  : TLS Γ (P ′∨ Q) → TLS (Γ ⨾ P) R → TLS (Γ ⨾ Q) R → TLS Γ R


data Rename : Ctx → Ctx → Type plvl where
  done : Rename [] []
  drop : Rename Γ Δ → Rename (Γ ⨾ P) Δ
  keep : Rename Γ Δ → Rename (Γ ⨾ P) (Δ ⨾ P)

idrn : Rename Γ Γ
idrn {Γ = []} = done
idrn {Γ = Γ ⨾ P} = keep (idrn {Γ = Γ})

_∘rn_ : Rename Δ Θ → Rename Γ Δ → Rename Γ Θ
p      ∘rn done   = p
p      ∘rn drop q = drop (p ∘rn q)
drop p ∘rn keep q = drop (p ∘rn q)
keep p ∘rn keep q = keep (p ∘rn q)
```
<!--
```agda
!rn : Rename Γ []
!rn {Γ = []}    = done
!rn {Γ = Γ ⨾ x} = drop !rn

π₁-rn : Rename (Γ ++ Θ) Γ
π₁-rn {Θ = []}    = idrn
π₁-rn {Θ = Θ ⨾ P} = drop π₁-rn

π₂-rn : Rename (Γ ++ Θ) Θ
π₂-rn {Θ = []}    = !rn
π₂-rn {Θ = Θ ⨾ P} = keep π₂-rn
```
-->

Variables and terms then form presheafs over the category of renamings.

```agda
rename-hyp : Rename Γ Δ → P ∈ᶜ Δ → P ∈ᶜ Γ
rename-hyp (drop rn) mem         = there (rename-hyp rn mem)
rename-hyp (keep rn) here        = here
rename-hyp (keep rn) (there mem) = there (rename-hyp rn mem)

rename : Rename Γ Δ → TLS Δ P → TLS Γ P
rename ρ triv = triv
rename ρ (falso x) = falso (rename-hyp ρ x)
rename ρ (exact x) = exact (rename-hyp ρ x)
rename ρ (assume x) = assume (rename (keep ρ) x)
rename ρ (apply1 f x) = apply1 (rename ρ f) (rename ρ x)
rename ρ (intro-∧ p q) = intro-∧ (rename ρ p) (rename ρ q)
rename ρ (fst-∧ x) = fst-∧ (rename ρ x)
rename ρ (snd-∧ x) = snd-∧ (rename ρ x)
rename ρ (left-∨ x) = left-∨ (rename ρ x)
rename ρ (right-∨ x) = right-∨ (rename ρ x)
rename ρ (elim-∨ x p q) 
  = elim-∨ (rename ρ x) (rename (keep ρ) p) (rename (keep ρ) q)

  
have : TLS Γ P → TLS (Γ ⨾ P) Q → TLS Γ Q
have f g = apply1 (assume g) f

``` 

## Semantics in Prop

Given an interpretation of our base propositions and constants,
we can construct an interpretation of our language into
the propositions of agda.

```agda
module Sound (F : Monotone B Props) where
  open Monotone F renaming (hom to F₀ ; pres-≤ to F₁)

  sem-ℙrop : ℙrop → Ω
  sem-ℙrop (↑ x) = F₀ x
  sem-ℙrop (x ′∧ y) = sem-ℙrop x ∧Ω sem-ℙrop y
  sem-ℙrop (x ′∨ y) = sem-ℙrop x ∨Ω sem-ℙrop y
  sem-ℙrop (x ′⇒ y) = sem-ℙrop x →Ω sem-ℙrop y
  sem-ℙrop true = ⊤Ω
  sem-ℙrop false = ⊥Ω

  sem-ctx : Ctx → Ω
  sem-ctx [] = ⊤Ω
  sem-ctx (Γ ⨾ x) = sem-ctx Γ ∧Ω sem-ℙrop x
 
  instance
    ⟦⟧-ℙrop : ⟦⟧-notation ℙrop
    ⟦⟧-ℙrop = brackets Ω sem-ℙrop

    ⟦⟧-Ctx : ⟦⟧-notation Ctx
    ⟦⟧-Ctx = brackets Ω sem-ctx

  
  
  _⊨_ : Ctx → ℙrop → Type
  Γ ⊨ P = ∣ ⟦ Γ ⟧ ∣ → ∣ ⟦ P ⟧ ∣
  
```

## Soundness

Soundness says that any provable sequent in our term language 
is provable in the semantics. I.e. there is a functor from
the syntax to the category of propositions.

```agda

  sound-exact : P ∈ Γ → Γ ⊨ P
  sound-exact here = snd
  sound-exact (there x) (Γ , _) = sound-exact x Γ

  sound : TLS Γ P → Γ ⊨ P
  sound (exact x) = sound-exact x
  sound (assume x) = curry (sound x)
  sound triv = _
  sound (falso x) f = absurd (sound-exact x f)
  sound (apply1 f x) Γ = sound f Γ (sound x Γ)
  sound (intro-∧ x y) Γ = (sound x Γ , sound y Γ)
  sound (fst-∧ x) Γ = fst (sound x Γ)
  sound (snd-∧ x) Γ = snd (sound x Γ)
  sound (left-∨ x) Γ = inc (inl (sound x Γ))
  sound (right-∨ x) Γ = inc (inr (sound x Γ))
  sound (elim-∨ x y z) Γ = ∥-∥-rec (hlevel 1) (λ where (inl x) → sound y (Γ , x)
                                                       (inr x) → sound z (Γ , x)) (sound x Γ)
  -- sound (↑ f) (_ , x) = F₁ f x
  
```


## Decidability

I would like to show that for any 
formulars $\Gamma$ and $P$, then the type
of proofs for $\Gamma \vdash P$ is decidable.

This would implement a correct by construction
version of Leans  _tauto_ tactic. (And allow me
to cheat on all my homework!!)

Ultimately we want to prove `Dec (TLS Γ P)`

```agda
  module Decidable ⦃ B-disc : Discrete Ob ⦄ where
```   

Given a 


```agda
    instance
      {-# TERMINATING #-}
      ℙrop-disc : Discrete ℙrop
      ℙrop-disc = Discreteᵢ→discrete λ where 
        (↑ x) (↑ y) → case (x ≡ᵢ? y) of λ where
          (yes reflᵢ) → yes reflᵢ
          (no ¬a) → no (λ where reflᵢ → ¬a reflᵢ)
        (x ′∧ y) (x' ′∧ y') → case (x ≡ᵢ? x' , y ≡ᵢ? y') of λ where 
          (yes reflᵢ) (yes reflᵢ) → yes reflᵢ
          (yes a) (no ¬a) → no λ where reflᵢ → ¬a reflᵢ
          (no ¬a) _ → no λ where reflᵢ → ¬a reflᵢ
        (x ′∨ y) (x' ′∨ y') → case (x ≡ᵢ? x' , y ≡ᵢ? y') of λ where 
          (yes reflᵢ) (yes reflᵢ) → yes reflᵢ
          (yes _) (no ¬a) → no λ where reflᵢ → ¬a reflᵢ
          (no ¬a) q → no λ where reflᵢ → ¬a reflᵢ
        (x ′⇒ y) (x' ′⇒ y') → case (x ≡ᵢ? x' , y ≡ᵢ? y') of λ where 
          (yes reflᵢ) (yes reflᵢ) → yes reflᵢ
          (yes _) (no ¬a) → no λ where reflᵢ → ¬a reflᵢ
          (no ¬a) q → no λ where reflᵢ → ¬a reflᵢ
        true true → yes reflᵢ
        false false → yes reflᵢ
        
        (↑ x) (y ′∧ y₁) → no (λ where ())
        (↑ x) (y ′∨ y₁) → no (λ where ())
        (↑ x) (y ′⇒ y₁) → no (λ where ())
        (↑ x) true → no (λ where ())
        (↑ x) false → no (λ where ())
        (x ′∧ x₁) (↑ x₂) → no (λ where ())
        (x ′∧ x₁) (y ′∨ y₁) → no (λ where ())
        (x ′∧ x₁) (y ′⇒ y₁) → no (λ where ())
        (x ′∧ x₁) true → no (λ where ())
        (x ′∧ x₁) false → no (λ where ())
        (x ′∨ x₁) (↑ x₂) → no (λ where ())
        (x ′∨ x₁) (y ′∧ y₁) → no (λ where ())
        (x ′∨ x₁) (y ′⇒ y₁) → no (λ where ())
        (x ′∨ x₁) true → no (λ where ())
        (x ′∨ x₁) false → no (λ where ())
        (x ′⇒ x₁) (↑ x₂) → no (λ where ())
        (x ′⇒ x₁) (y ′∧ y₁) → no (λ where ())
        (x ′⇒ x₁) (y ′∨ y₁) → no (λ where ())
        (x ′⇒ x₁) true → no (λ where ())
        (x ′⇒ x₁) false → no (λ where ())
        true (↑ x) → no (λ where ())
        true (y ′∧ y₁) → no (λ where ())
        true (y ′∨ y₁) → no (λ where ())
        true (y ′⇒ y₁) → no (λ where ())
        true false → no (λ where ())
        false (↑ x) → no (λ where ())
        false (y ′∧ y₁) → no (λ where ())
        false (y ′∨ y₁) → no (λ where ())
        false (y ′⇒ y₁) → no (λ where ())
        false true → no (λ where ())

      {-# TERMINATING #-}
      Ctx-dec : Discrete Ctx
      Ctx-dec = Discreteᵢ→discrete (λ where
        [] [] → yes reflᵢ
        [] (y ⨾ x) → no (λ ())
        (x ⨾ x₁) [] → no (λ ())
        (Γ ⨾ x) (Δ ⨾ y) → case (Γ ≡ᵢ? Δ , x ≡ᵢ? y) of λ where
            (yes reflᵢ) (yes reflᵢ) → yes reflᵢ
            (yes a) (no ¬a) → no (λ where reflᵢ → ¬a reflᵢ)
            (no ¬a) a → no (λ where reflᵢ → ¬a reflᵢ)
          )
      

    _∈?_ : ∀ (P : ℙrop) (Γ : Ctx) → Dec (P ∈ Γ)
    P ∈? [] = no (λ ())
    P ∈? (Γ ⨾ x) = case (P ∈? Γ) of λ where 
      (yes a) → yes (rename-hyp π₁-rn a)
      (no not-there) → case (P ≡ᵢ? x) of λ where 
        (yes reflᵢ) → yes here
        (no not-here) → no (λ where here      → not-here reflᵢ
                                    (there x) → not-there x)

    rename-var : P ∈ Γ → Σ _ λ Δ → Rename Γ (Δ ⨾ P)
    rename-var {P} {Γ ⨾ _} here = Γ , idrn
    rename-var {P} {Γ ⨾ Q} (there v) = case rename-var v of λ where
      Δ x → Δ , drop x
```   

We would like to define a type of proof trees that is naturally
a proposition not just truncated like our syntax. This is
often called a 'normal form'. 

In doing so we need to change our context AND the structure of the
proof trees.

We don't want to care about the order of the context (as before) and 
we also don't wan't to care about the _multiplicity_. This is to say,
we only care if our context has some variable of type $P$, but $P ∧ P$
is equivilant to $P$ as a proposition, so it doesn't matter how many are
in our context. This changes our structure from a list into a (material) Set.




```agda

    -- data Split-cx : Ctx → Ctx → Type plvl where
    --   drop-top   : Split-cx Γ Δ → Split-cx (Γ ⨾ true) Δ
    --   absurd!    : Split-cx (Γ ⨾ false) ([] ⨾ false)

    --   split-∧    : Split-cx Γ Δ → Split-cx (Γ ⨾ (P ′∧ Q)) (Δ ⨾ P ⨾ Q)
      
    --   drop-abs   : Split-cx Γ Δ → Split-cx (Γ ⨾ (false ′⇒ P)) Δ
    --   drop-triv  : Split-cx Γ Δ → Split-cx (Γ ⨾ (P ′⇒ true)) Δ
    --   simp-imp   : Split-cx Γ Δ → Split-cx (Γ ⨾ (true ′⇒ P)) (Δ ⨾ P)

    --   split-∨    : Split-cx Γ Δ 
    --              → Split-cx (Γ ⨾ (P ′∨ Q) ′⇒ R) (Δ ⨾ P ′⇒ R ⨾ Q ′⇒ R)
    --   make-curry :  Split-cx Γ Δ
    --              → Split-cx (Γ ⨾ (P ′⇒ (Q ′⇒ R))) (Δ ⨾ (P ′∧ Q) ′⇒ R)
      

    --   leave↑     : ∀ {P} → Split-cx Γ Δ → Split-cx (Γ ⨾ ↑ P) (Δ ⨾ ↑ P)

    --   leave-oth  : Split-cx Γ Δ → Split-cx (Γ ⨾ (P ′⇒ Q) ′⇒ R)
    
    flat-cx-⇒ : ℙrop → ℙrop → (Ctx → Ctx)
    flat-cx-⇒ P true Γ = Γ
    flat-cx-⇒ P (Q ′⇒ R) Γ = Γ ⨾ (P ′∧ Q) ′⇒ R
    flat-cx-⇒ P Q@(↑ _) Γ = Γ ⨾ P ′⇒ Q
    flat-cx-⇒ P Q@(_ ′∧ _) Γ = Γ ⨾ P ′⇒ Q
    flat-cx-⇒ P Q@(_ ′∨ _) Γ = Γ ⨾ P ′⇒ Q
    flat-cx-⇒ P false Γ = Γ ⨾ P ′⇒ false

    add-ℙrop-flat : ℙrop → (Ctx → Ctx)
    add-ℙrop-flat (↑ x) = _⨾ ↑ x
    add-ℙrop-flat (P ′∧ Q) = (add-ℙrop-flat Q) ⊙ (add-ℙrop-flat P)
    add-ℙrop-flat A@(P ′∨ Q) = _⨾ A
    add-ℙrop-flat true Γ = Γ
    add-ℙrop-flat false Γ = [] ⨾ false
    
    add-ℙrop-flat (true ′⇒ Q) = add-ℙrop-flat Q
    add-ℙrop-flat (false ′⇒ Q) Γ = Γ
    add-ℙrop-flat ((P ′∨ Q) ′⇒ R) 
      = add-ℙrop-flat (Q ′⇒ R) ⊙ add-ℙrop-flat (P ′⇒ R)
    add-ℙrop-flat (P@(↑ x) ′⇒ Q) = flat-cx-⇒ P Q
    add-ℙrop-flat (A@(P ′∧ Q) ′⇒ R) = flat-cx-⇒ A R
    add-ℙrop-flat (A@(P ′⇒ Q) ′⇒ R) = flat-cx-⇒ A R

    flat-cx : Ctx → Ctx
    flat-cx [] = []
    flat-cx (Γ ⨾ x) = add-ℙrop-flat x (flat-cx Γ)

    -- flat-cx [] = []
    -- flat-cx (Γ ⨾ ↑ x) = flat-cx Γ ⨾ ↑ x
    -- flat-cx (Γ ⨾ P ′∧ Q) = flat-cx Γ ⨾ P ⨾ Q
    -- flat-cx (Γ ⨾ A@(P ′∨ Q)) = flat-cx Γ ⨾ A
    -- flat-cx (Γ ⨾ false ′⇒ Q) = flat-cx Γ
    -- flat-cx (Γ ⨾ true ′⇒ Q) = flat-cx Γ ⨾ Q
    -- flat-cx (Γ ⨾ (P ′∨ Q) ′⇒ R) = flat-cx Γ ⨾ P ′⇒ R ⨾ Q ′⇒ R
    -- flat-cx (Γ ⨾ ↑ x ′⇒ Q) = flat-cx-⇒ (↑ x) Q (flat-cx Γ)
    -- flat-cx (Γ ⨾ P@(_ ′∧ _) ′⇒ Q) = flat-cx-⇒ P Q (flat-cx Γ)
    -- flat-cx (Γ ⨾ P@(_ ′⇒ _) ′⇒ Q) = flat-cx-⇒ P Q (flat-cx Γ)
    -- --                 true) = flat-cx Γ
    -- -- flat-cx (Γ ⨾ P ′⇒ Q ′⇒ R) = flat-cx Γ ⨾ P ′∧ Q ′⇒ R
    -- -- flat-cx (Γ ⨾ P ′⇒ Q) = flat-cx Γ ⨾ P ′⇒ Q
    -- flat-cx (Γ ⨾ true) = flat-cx Γ
    -- flat-cx (Γ ⨾ false) = [] ⨾ false

    open import Data.String.Base

    data Result (Γ : Ctx) (P : ℙrop) : Type plvl where
      oh-yes : TLS Γ P → Result Γ P
      nonono : String → Result Γ P

    map-result : (TLS Γ P → TLS Δ Q) → Result Γ P → Result Δ Q
    map-result f (oh-yes x) = oh-yes (f x)
    map-result f (nonono x) = nonono x

    data rn (Γ : Ctx) : Ctx → Type plvl where
      [] : rn Γ []
      _⨾_ : rn Γ Δ → P ∈ Γ → rn Γ (Δ ⨾ P)

    drop-it : rn Γ Δ → rn (Γ ⨾ P) Δ
    drop-it [] = []
    drop-it (r ⨾ x) = drop-it r ⨾ there x
    
    keep-it : rn Γ Δ → rn (Γ ⨾ P) (Δ ⨾ P)
    keep-it r = (drop-it r) ⨾ here 

    id-it : (Γ : Ctx) → rn Γ Γ
    id-it [] = []
    id-it (Γ ⨾ x) = drop-it (id-it Γ) ⨾ here

    data sub (Γ : Ctx) : Ctx → Type plvl where
      [] : sub Γ []
      _⨾_ : sub Γ Δ → TLS Γ P → sub Γ (Δ ⨾ P)

    drop-sub : sub Γ Δ → sub (Γ ⨾ P) Δ
    drop-sub [] = []
    drop-sub (σ ⨾ x) = (drop-sub σ) ⨾ (rename π₁-rn x)

    keep-sub : sub Γ Δ → sub (Γ ⨾ P) (Δ ⨾ P)
    keep-sub σ = drop-sub σ ⨾ exact here

    rn-sub : Rename Γ Δ → sub Γ Δ
    rn-sub done = []
    rn-sub (drop ρ) = drop-sub (rn-sub ρ)
    rn-sub (keep ρ) = keep-sub (rn-sub ρ)

    id-sub : sub Γ Γ
    id-sub = rn-sub idrn

    subst-var : sub Γ Δ → P ∈ Δ → TLS Γ P
    subst-var (σ ⨾ x) here = x
    subst-var (σ ⨾ x) (there v) = subst-var σ (rename-hyp π₁-rn v)

    subst-pr : sub Γ Δ → TLS Δ P → TLS Γ P
    subst-pr σ triv = triv
    subst-pr σ (exact x) = subst-var σ x
    subst-pr σ (falso x) = have (subst-var σ x) (falso here)
    subst-pr σ (assume t) = assume (subst-pr (keep-sub σ) t)
    subst-pr σ (apply1 f x) = apply1 (subst-pr σ f) (subst-pr σ x)
    subst-pr σ (intro-∧ t t₁) 
      = intro-∧ (subst-pr σ t) (subst-pr σ t₁)
    subst-pr σ (fst-∧ t) = fst-∧ (subst-pr σ t)
    subst-pr σ (snd-∧ t) = snd-∧ (subst-pr σ t)
    subst-pr σ (left-∨ t) = left-∨ (subst-pr σ t)
    subst-pr σ (right-∨ t) = right-∨ (subst-pr σ t)
    subst-pr σ (elim-∨ t t₁ t₂) 
      = elim-∨ (subst-pr σ t)
         (subst-pr (keep-sub σ) t₁)
         (subst-pr (keep-sub σ) t₂)


    _∘sub_ : sub Δ Θ → sub Γ Δ → sub Γ Θ
    [] ∘sub ρ = []
    (σ ⨾ x) ∘sub ρ = (σ ∘sub ρ) ⨾ (subst-pr ρ x)

    sub-left : sub Γ Δ → sub (Γ ⨾ P ′∧ Q) (Δ ⨾ P)
    sub-left σ = (drop-sub σ) ⨾ (fst-∧ (exact here))

    sub-right : sub Γ Δ → sub (Γ ⨾ P ′∧ Q) (Δ ⨾ Q)
    sub-right σ = (drop-sub σ) ⨾ (snd-∧ (exact here))

    have-sub : sub (Γ ⨾ P) Δ → TLS Γ P → sub Γ Δ
    have-sub σ t = σ ∘sub (id-sub ⨾ t)

    add-flat-lem : ∀ (f : Ctx → Ctx) → sub Γ (f Δ)
                 → ∀ P → sub (Γ ⨾ P) (add-ℙrop-flat P (f Δ))
    add-flat-lem f σ (↑ x) = keep-sub σ
    add-flat-lem {Γ = Γ} f σ (P ′∧ Q)
      = let p1 = add-flat-lem f σ P 
            p2 = add-flat-lem {Γ ⨾ P} (add-ℙrop-flat P ⊙ f) p1 Q
        in p2 ∘sub (((drop-sub id-sub) ⨾ (fst-∧ (exact here))) ⨾ (snd-∧ (exact here)))
    add-flat-lem f σ (P ′∨ Q) = keep-sub σ
    add-flat-lem f σ true = drop-sub σ
    add-flat-lem f σ false = [] ⨾ exact here
    
    add-flat-lem f σ (true ′⇒ Q) = add-flat-lem f σ Q ∘sub
         ((drop-sub id-sub) ⨾ (apply1 (exact here) triv))
    add-flat-lem f σ (false ′⇒ Q) 
      = σ ∘sub drop-sub id-sub
    add-flat-lem f σ ((P ′∨ Q) ′⇒ R)
       = add-flat-lem 
            (add-ℙrop-flat (P ′⇒ R) ⊙ f) (add-flat-lem f σ (P ′⇒ R)) (Q ′⇒ R)
       ∘sub (((drop-sub id-sub) 
          ⨾ (assume (apply1 (exact (there here)) (left-∨ (exact here)))))
          ⨾ assume (apply1 (exact (there here)) (right-∨ (exact here))))
       
    add-flat-lem f σ ((P ′∧ P₁) ′⇒ A@(↑ x)) = keep-sub σ
    add-flat-lem f σ ((P ′∧ P₁) ′⇒ (Q ′∧ Q₁)) = keep-sub σ
    add-flat-lem f σ ((P ′∧ P₁) ′⇒ (Q ′∨ Q₁)) = keep-sub σ
    add-flat-lem f σ ((P ′∧ Q) ′⇒ true) = drop-sub σ
    add-flat-lem f σ ((P ′∧ Q) ′⇒ false) = keep-sub σ
    add-flat-lem f σ ((P ′∧ Q) ′⇒ R ′⇒ S) = (drop-sub σ) ⨾
       assume (
        apply1 (
            apply1 (exact (there here))
                   (fst-∧ (exact here)))
        (snd-∧ (exact here)))

    add-flat-lem f σ (↑ x ′⇒ (Q ′∨ Q₁)) = keep-sub σ
    add-flat-lem f σ (↑ x ′⇒ (Q ′∧ Q₁)) = keep-sub σ
    add-flat-lem f σ (↑ x ′⇒ ↑ x') = keep-sub σ
    add-flat-lem f σ (↑ x ′⇒ true) = drop-sub σ
    add-flat-lem f σ (↑ x ′⇒ false) = keep-sub σ
    add-flat-lem f σ (↑ x ′⇒ Q ′⇒ R) 
      = (drop-sub σ)
      ⨾ assume (
          apply1 
            (apply1 (exact (there here)) (fst-∧ (exact here)))
            (snd-∧ (exact here)))
    
    add-flat-lem f σ ((P ′⇒ Q) ′⇒ ↑ x) = keep-sub σ
    add-flat-lem f σ ((P ′⇒ Q) ′⇒ (R ′∧ S)) = keep-sub σ
    add-flat-lem f σ ((P ′⇒ Q) ′⇒ (R ′∨ S)) = keep-sub σ
    add-flat-lem f σ ((P ′⇒ Q) ′⇒ true) = drop-sub σ
    add-flat-lem f σ ((P ′⇒ Q) ′⇒ false) = keep-sub σ
    add-flat-lem f σ ((P ′⇒ Q) ′⇒ R ′⇒ S) 
      = drop-sub σ 
      ⨾ assume 
        (apply1 
          (apply1 
            (exact (there here))
            (assume (apply1 (fst-∧ (exact (there here))) (exact here))))
          (snd-∧ (exact here)))

    flat→orig : sub Γ (flat-cx Γ)
    flat→orig {[]} = []
    flat→orig {Γ ⨾ P} = add-flat-lem {Γ} {Γ} flat-cx flat→orig P


    {-# TERMINATING #-}
    search : ∀ Γ P → Result Γ P
    prove : ∀ Γ P → Result Γ P 

    flat-prove : ∀ Γ P → Result Γ P
    flat-prove Γ P = map-result
       (subst-pr flat→orig)
       (prove (flat-cx Γ) _)

    prove Γ (P ′∧ Q) = case (prove Γ P , prove Γ Q) of λ where 
      (oh-yes x) (oh-yes y) → oh-yes (intro-∧ x y)
      (oh-yes x) (nonono err) → nonono $
            "Failed to get the right side of an and.\nErr: " <> err
      (nonono err) _ → nonono $ 
            "Failed to get the left side of an and.\nErr: " <> err
    prove Γ (P ′⇒ Q) = case (flat-prove (Γ ⨾ P) Q) of λ where 
      (oh-yes x) → oh-yes (assume x)
      (nonono err) → nonono $ "Couldn't derrive Γ ⨾ P ⊢ Q. \nErr: "
                    <> err
    prove Γ true = oh-yes triv
    prove Γ P = split-∨ (id-it Γ) where
      split-∨ : rn Γ Δ → Result Γ P
      split-∨ [] = search Γ P
      split-∨ (_⨾_ {P = (A ′∨ B)} Δ v) with flat-prove (Γ ⨾ A) P 
      ... | oh-yes x with flat-prove (Γ ⨾ B) P 
      split-∨ (_⨾_ {_} {.(_ ′∨ _)} _ v) | oh-yes x | oh-yes y 
          = oh-yes (elim-∨ (exact v) x y)
      split-∨ (_⨾_ {_} {.(_ ′∨ _)} _ _) | oh-yes _ | nonono x = nonono ("Case split not successfull, err: " <> x)
      split-∨ _ |  nonono x = nonono ("Case split not successfull, err: " <> x)
      split-∨ (_⨾_ {P = A} Δ v) = split-∨ Δ

    search Γ P with P ∈? Γ 
    ... | yes v = oh-yes (exact v)
    search Γ P | no ¬v = having-gone P (go (id-it Γ))
      where

      go-aux : ∀ {A B} → (A ′⇒ B) ∈ᶜ Γ → (Result Γ P → Result Γ P)
      go-aux {P' ′⇒ Q'} {B} v cont 
        = case (flat-prove (Γ ⨾ Q' ′⇒  B ⨾ P') Q' , flat-prove (Γ ⨾ B) P) of λ where 
            (oh-yes x) (oh-yes y) → {!   !}
            (oh-yes x) (nonono y) → cont
            (nonono x) _ → cont
      go-aux {A} _ cont = cont

      go : rn Γ Δ → Result Γ P
      go [] = nonono "Goal is not derrivable :("
      go (_⨾_ {P = A ′⇒ B} Δ v) = case (A ∈? Γ) of λ where 
        (yes a) → map-result (have (apply1 (exact v) (exact a))) 
            $ flat-prove (Γ ⨾ B) P
        (no ¬a) → go-aux v (go Δ)
        -- case A of λ where 
        --   (P' ′⇒ Q') → case (flat-prove (Γ ⨾ Q' ′⇒  B ⨾ P') Q' , flat-prove (Γ ⨾ B) P) of λ where
        --     (oh-yes x) (oh-yes y) → oh-yes (subst-pr (id-sub ⨾ {! assume  !}) y)
        --     (oh-yes x) (nonono y) → go Δ
        --     (nonono x) _ → go Δ
        --   x → go Δ
      go (Δ ⨾ v) = go Δ



      having-gone : (P : ℙrop) → Result Γ P → Result Γ P
      having-gone _ (oh-yes x) = oh-yes x
      having-gone (P ′∨ Q) (nonono _) with prove Γ P
      ... | oh-yes x = oh-yes (left-∨ x)
      ... | nonono x with prove Γ Q
      ... |    oh-yes q = oh-yes (right-∨ q)
      ... |    nonono x = nonono x 
      having-gone _ (nonono x) = nonono x 
    

--     data LJT : Ctx → ℙrop → Type plvl where
--       assump : ∥ P ∈ Γ ∥ → LJT Γ P
--       ↑ : {P Q : Ob} → P ≤ Q → LJT (Γ ⨾ (↑ P)) (↑ Q)


--       triv : LJT Γ true
--       falso : LJT (Γ ⨾ false) P
--       ∧-elim : ∀ {Γ'} → (LJT (Γ ⨾ P ⨾ Q) R) 
--                       → LJT (Γ' ⨾ (P ′∧ Q)) R
--       ∨-elim : (LJT (Γ ⨾ P) R) → LJT (Γ ⨾ Q) R
--               →  LJT (Γ ⨾ (P ′∧ Q)) R
      
      

--       ∧-intro : LJT Γ P → LJT Γ Q → LJT Γ (P ′∧ Q)
--       ∨-intro : ∥ LJT Γ P ⊎ LJT Γ Q ∥ → LJT Γ (P ′∨ Q)

--       assume : LJT (Γ ⨾ P) Q → LJT Γ (P ′⇒ Q)

--       apply-↑ : ∀ {P} → LJT (Γ ⨾ ↑ P ⨾ Q) R
--                       → LJT (Γ ⨾ ↑ P ⨾ (↑ P ′⇒ Q)) R
                      
      
--       apply-∧ : LJT (Γ ⨾ (P ′⇒ (Q ′⇒ R))) S
--               → LJT (Γ ⨾ P ′∧ Q ′⇒ R) S

--       apply-∨ : LJT (Γ ⨾ (P ′⇒ R) ⨾ Q ′⇒ R) S
--               → LJT (Γ ⨾ (P ′∨ Q ′⇒ R)) S 

--       apply-⇒ : (LJT (Γ ⨾ (Q ′⇒ R)) (P ′⇒ Q))
--               → (LJT (Γ ⨾ R) S)
--               → LJT (Γ ⨾ ((P ′⇒ Q) ′⇒ R)) S

--     rename-LJT : Rename Γ Δ → LJT Δ P → LJT Γ P
--     rename-LJT = {!   !}

--     out-l : LJT Γ (P ′∧ Q) → LJT Γ P
--     out-l = {!   !}
    
--     out-r : LJT Γ (P ′∧ Q) → LJT Γ Q
--     out-r = {!   !}

      
--     LJT? : ∀ Γ P → Dec (LJT Γ P)
--     LJT? Γ (↑ x) = {!   !}
--     LJT? Γ (P ′∧ Q) = case (LJT? Γ P , LJT? Γ Q) of λ where 
--       (yes p) (yes q) → yes (∧-intro p q)
--       (yes a) (no ¬a) → no (λ x → ¬a (out-r x))
--       (no ¬a) _       → no (λ x → ¬a (out-l x))
--     LJT? Γ (P ′∨ Q) = case (LJT? Γ P , LJT? Γ Q) of λ where 
--       (yes a) _        → yes (∨-intro (inc (inl a)))
--       (no ¬a) (yes a)  → yes (∨-intro (inc (inr a)))
--       (no ¬a) (no ¬a₁) → no {!   !}
--     LJT? Γ (P ′⇒ Q) = case (LJT? (Γ ⨾ P) Q) of λ where 
--       (yes a) → yes (assume a)
--       (no ¬a) → no {!   !}
--     LJT? Γ true = yes triv
--     LJT? Γ false = case (false ∈? Γ) of λ where 
--       (yes a) → yes (rename-LJT (rename-var a .snd) falso)
--       (no ¬a) → {!  !}

      
--     -- LJT? Γ' (↑ x) = {!   !}
--     -- LJT? Γ' (P ′∧ Q) with LJT? Γ' P | LJT? Γ' Q 
--     -- ... | yes p | yes q = yes (∧-intro p q)
--     -- ... | yes p | no ¬q = no λ pq → ¬q (out-r pq)
--     -- ... | no ¬p | q     = no λ pq → ¬p (out-l pq)
--     -- LJT? Γ' (P ′∨ Q) with LJT? Γ' P 
--     -- ... | yes p = yes (∨-intro (inc (inl p)))
--     -- ... | no ¬p with LJT? Γ' Q 
--     -- ...      | yes q = yes (∨-intro (inc (inr q)))
--     -- ...      | no ¬q = no (LJT-∨ ¬p ¬q)
--     -- LJT? Γ' (P ′⇒ Q) = yes (assume (λ p → {!   !}))
--     -- LJT? Γ' true = yes true
--     -- LJT? Γ' false with false ∈? Γ'
--     -- ... | yes v = yes (falso v)
--     -- ... | no ¬v = no (LJT-false ¬v)
    
--     instance
--       LJT-dec : Dec (LJT Γ P)
--       LJT-dec = LJT? _ _


--     _⊢?_ : ∀ Γ P → Dec (TLS Γ P)
--     _⊢?_ = {!   !}
```


## Complete

I think completeness says that any thing that is true in the semantics
should be provable in the syntax. 

Given decidability, the problem of completeness gets reduced to saying
that if we can't derrive it in the syntax, then it is not true in the
semantics. (Note that classically this is always equivalent to complteness)

-->

```agda
    -- complete' : ¬ TLS Γ P → ¬ Γ ⊨ P
    -- complete' nsyn f = {!   !}
   
    -- complete : Γ ⊨ P → TLS Γ P
    -- -- complete {Γ} {P} x = ⇒-closed (taut-complete (⊨-closed {Γ} {P} x))
    -- complete {Γ} {P} x with Γ ⊢? P
    -- ... | yes p = p
    -- ... | no p = {!   !}
           
    
    neg : ℙrop → ℙrop
    neg A = A ′⇒ false

          
    nnem : [] ⊨ neg (neg (P ′∨ (neg P)))
    nnem _ f = f (inc (inr (λ x → f (inc (inl x)))))
    
    postulate
      noem : ¬ TLS [] (P ′∨ neg P)

    mt : ∀ {o ℓ} {A : Type o} {B : Type ℓ} → (A → B) → (¬ B → ¬ A)
    mt f nb a = nb (f a)

    not-complete : (∀ {Γ P} → Γ ⊨ P → TLS Γ P) → ℙrop → ⊥
    not-complete cmp P = nnem {P = P} _ λ s → mt cmp (noem {P}) (λ _ → s)
    
```             
                          