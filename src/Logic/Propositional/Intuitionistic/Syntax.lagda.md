
```agda

module Logic.Propositional.Intuitionistic.Syntax where
    
open import Cat.Prelude
open import Order.Base
open import Order.Instances.Props
open import Order.Instances.Product
open import Order.Instances.Pointwise
open import Logic.Propositional.Intuitionistic
open import Logic.SimpleContext
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Functor.Adjoint
open import Cat.Displayed.Total
open import Cat.Displayed.Free
open import Meta.Idiom
open import Data.Sum
open import Cat.Functor.Hom
open import Cat.Functor.Base

private
  ∥-∥-ua : ∀ {ℓ} {A B : Type ℓ}
          → ⦃ _ : H-Level A 1 ⦄ ⦃ _ : H-Level B 1 ⦄ 
          → (A → B) → (B → A) → A ≡ B
  ∥-∥-ua f g = ua (Iso→Equiv (f , (iso g (λ _ → prop!) (λ _ → prop!))))
  
module Syn {ℓ} (T : Theory ℓ) where

  open Theory T

  private variable
    Γ Δ : Ctx (ℙrop Atom)
    P Q R : ℙrop Atom

  data _⊢_ : Ctx (ℙrop Atom) → ℙrop Atom → Type ℓ where
    ax : ∀ {Γ Δ A} → ∣ Axiom Δ A ∣ → Sub (_⊢_) Γ Δ →  Γ ⊢ A

    triv : Γ ⊢ true

    exact : P ∈ Γ → Γ ⊢ P
    falso : false ∈ Γ → Γ ⊢ P

    assume : (Γ ⨾ P) ⊢ Q → Γ ⊢ (P ′⇒ Q)
    apply1 : Γ ⊢ (P ′⇒ Q) → (Γ ⊢ P → Γ ⊢ Q)

    intro-∧ : Γ ⊢ P → Γ ⊢ Q → Γ ⊢ (P ′∧ Q)
    fst-∧   : Γ ⊢ (P ′∧ Q) → Γ ⊢ P
    snd-∧   : Γ ⊢ (P ′∧ Q) → Γ ⊢ Q  

    left-∨  : Γ ⊢ P → Γ ⊢ (P ′∨ Q)
    right-∨ : Γ ⊢ Q → Γ ⊢ (P ′∨ Q)
    elim-∨  : Γ ⊢ (P ′∨ Q) → (Γ ⨾ P) ⊢ R → (Γ ⨾ Q) ⊢ R → Γ ⊢ R


  have : Γ ⊢ P → (Γ ⨾ P) ⊢ Q → Γ ⊢ Q
  have f g = apply1 (assume g) f


  open Var-term {{...}}
  open Subst {{...}}

  instance
    ⊢-var-term : Var-term _⊢_
    ⊢-var-term = record { ι = exact }

  ren-tm : Ren Γ Δ → Δ ⊢ P → Γ ⊢ P
  ren-tm ρ (ax a σ) = ax a (comp-sr σ ρ) where
    comp-sr : ∀ {Γ Δ Θ}
              → Sub _⊢_ Δ Θ
              → Ren Γ Δ
              → Sub _⊢_ Γ Θ
    comp-sr ε σ = ε
    comp-sr (γ ⦊ x) σ = (comp-sr γ σ) ⦊ (ren-tm σ x)
  ren-tm ρ triv = triv
  ren-tm ρ (exact x) = exact (x [ ρ ])
  ren-tm ρ (falso x) = falso (x [ ρ ])
  ren-tm ρ (assume x) = assume (ren-tm (keep-rn ρ) x)
  ren-tm ρ (apply1 f x) = apply1 (ren-tm ρ f) (ren-tm ρ x)
  ren-tm ρ (intro-∧ x x₁) = intro-∧ (ren-tm ρ x) (ren-tm ρ x₁)
  ren-tm ρ (fst-∧ x) = fst-∧ (ren-tm ρ x)
  ren-tm ρ (snd-∧ x) = snd-∧ (ren-tm ρ x)
  ren-tm ρ (left-∨ x) = left-∨ (ren-tm ρ x)
  ren-tm ρ (right-∨ x) = right-∨ (ren-tm ρ x)
  ren-tm ρ (elim-∨ x x₁ x₂) = elim-∨ (ren-tm ρ x) (ren-tm (keep-rn ρ) x₁) (ren-tm (keep-rn ρ) x₂)
 
  instance
    ⊢-rename : Subst _⊢_ _ᶜ∋_
    ⊢-rename = record { _[_] = λ x f → ren-tm f x }

  sub-tm-var : Sub _⊢_ Γ Δ → P ∈ Δ → Γ ⊢ P
  sub-tm-var (_ ⦊ x) here = x
  sub-tm-var (γ ⦊ _) (there v) = sub-tm-var γ v

  sub-ax : Sub _⊢_ Γ Δ → ∣ Axiom Δ P ∣ → Γ ⊢ P
  sub-ax γ a = ax a γ

  sub-tm : Sub _⊢_ Γ Δ → Δ ⊢ P → Γ ⊢ P
  sub-tm γ (ax x p) = ax x (comp-s p γ) where
    comp-s : ∀ {Γ Δ Θ} →
            Sub _⊢_ Γ Δ → Sub _⊢_ Θ Γ 
            → Sub _⊢_ Θ Δ
    comp-s ε σ = ε
    comp-s (γ ⦊ x) σ = (comp-s γ σ) ⦊ (sub-tm σ x)
  sub-tm γ triv = triv
  sub-tm γ (exact x) = sub-tm-var γ x
  sub-tm γ (falso x) = have (sub-tm-var γ x) (falso here)
  sub-tm γ (assume t) = assume (sub-tm (keep-sub γ) t)
  sub-tm γ (apply1 t t₁) = apply1 (sub-tm γ t) (sub-tm γ t₁)
  sub-tm γ (intro-∧ t t₁) = intro-∧ (sub-tm γ t) (sub-tm γ t₁)
  sub-tm γ (fst-∧ t) = fst-∧ (sub-tm γ t)
  sub-tm γ (snd-∧ t) = snd-∧ (sub-tm γ t)
  sub-tm γ (left-∨ t) = left-∨ (sub-tm γ t)
  sub-tm γ (right-∨ t) = right-∨ (sub-tm γ t)
  sub-tm γ (elim-∨ t t₁ t₂) = elim-∨ (sub-tm γ t) (sub-tm (keep-sub γ) t₁) (sub-tm (keep-sub γ) t₂)

  instance
    sub-⊢ : Subst _⊢_ _⊢_
    (sub-⊢ Subst.[ x ]) γ = sub-tm γ x

  sub-elim-∨ : ∀ {Γ A B Δ} 
    → Sub _⊢_ (Γ ⨾ A) Δ → Sub _⊢_ (Γ ⨾ B) Δ 
    → Sub _⊢_ (Γ ⨾ (A ′∨ B)) Δ
  sub-elim-∨ {Δ = []} f g = ε 
  sub-elim-∨ {Δ = Δ ⨾ C} (f ⦊ x) (g ⦊ y) =
       sub-elim-∨ f g ⦊ (elim-∨ (exact here)
           (ren-tm (keep-rn π₁-rn) x)
           (ren-tm (keep-rn π₁-rn) y))

  subs : Precategory ℓ ℓ
  subs .Precategory.Ob = Ctx (ℙrop Atom)
  subs .Precategory.Hom Γ Δ = ∥ Sub _⊢_ Γ Δ ∥
  subs .Precategory.Hom-set _ _ = hlevel 2
  subs .Precategory.id = inc id-sub
  subs .Precategory._∘_ = rec! (λ x y → inc (x ∘sub y))
  subs .Precategory.idl _ = prop!
  subs .Precategory.idr _ = prop!
  subs .Precategory.assoc _ _ _ = prop!
  
  subs-terminal : Terminal subs
  subs-terminal .Terminal.top = []
  subs-terminal .Terminal.has⊤ x = contr (inc ε) (λ _ → prop!)

  subs-products : ∀ x y → Product subs x y
  subs-products x y = prod where
    prod : Product subs x y
    prod .Product.apex = x ++ y
    prod .Product.π₁ = inc π₁-sub
    prod .Product.π₂ = inc π₂-sub
    prod .Product.has-is-product .is-product.⟨_,_⟩ 
     = rec! λ f g → inc (⟨⟩-sub f g)
    prod .Product.has-is-product .is-product.π₁∘⟨⟩ = prop!
    prod .Product.has-is-product .is-product.π₂∘⟨⟩ = prop!
    prod .Product.has-is-product .is-product.unique _ _ = prop!


  Tm : ℙrop Atom → Functor (subs ^op) Props'
  Tm A .Functor.F₀ Γ = elΩ (Γ ⊢ A)
  Tm A .Functor.F₁ = rec! (λ γ x → inc (x [ γ ]))
  Tm A .Functor.F-id = prop!
  Tm A .Functor.F-∘ _ _ = prop!
  
  extend : ℙrop Atom → Functor subs subs
  extend A .Functor.F₀ = _⨾ A
  extend A .Functor.F₁ = rec! (λ γ → inc (keep-sub γ))
  extend A .Functor.F-id = prop!
  extend A .Functor.F-∘ _ _ = prop!



  syn-SPwF : SPwF ℓ ℓ
  syn-SPwF .SPwF.Con = subs
  syn-SPwF .SPwF.Con-thin _ _ = hlevel 1
  syn-SPwF .SPwF.Con-ter = subs-terminal
  syn-SPwF .SPwF.Con-prod = subs-products
  syn-SPwF .SPwF.Con-str = hlevel 2
  syn-SPwF .SPwF.Ty = el! (ℙrop Atom)
  syn-SPwF .SPwF.Tm = Tm
  syn-SPwF .SPwF.extend = extend
  syn-SPwF .SPwF.extend-rep A = ∥-∥-ua 
            (rec! (λ γ x → inc (γ ⦊ x)))
            (rec! (λ where (γ ⦊ x) → (inc γ , inc x)))
  syn-SPwF .SPwF.model-⊤ = true
  syn-SPwF .SPwF.⊤-rep = inc triv
  syn-SPwF .SPwF.model-⊥ = false
  syn-SPwF .SPwF.⊥-rep = inc (falso here)
  syn-SPwF .SPwF._model-∧_ = _′∧_
  syn-SPwF .SPwF.∧-rep = ∥-∥-ua 
              (rec! (λ x → inc (fst-∧ x) , inc (snd-∧ x)))
              (rec! (λ x y → inc (intro-∧ x y)))
  syn-SPwF .SPwF._model-∨_ = _′∨_
  syn-SPwF .SPwF.∨-rep = ∥-∥-ua
    (rec! (λ x → (
        inc (x ∘sub (π₁-sub ⦊ (left-∨ (exact here))))) 
      , inc (x ∘sub (π₁-sub ⦊ right-∨ (exact here)))))
    (rec! (λ x y → inc (sub-elim-∨ x y)))
  syn-SPwF .SPwF._model-⇒_ = _′⇒_
  syn-SPwF .SPwF.⇒-rep = ∥-∥-ua 
        (rec! (λ x → inc (assume x)))
        (rec! (λ x → inc (apply1 (x [ π₁-rn ]) (exact here))))

  
  include-ℙrop-ℙrop : ∀ A → include-ℙrop syn-SPwF T ↑_ A ≡ A
  include-ℙrop-ℙrop (↑ x) = refl
  include-ℙrop-ℙrop (A ′∧ B) i = include-ℙrop-ℙrop A i ′∧ include-ℙrop-ℙrop B i
  include-ℙrop-ℙrop (A ′∨ B) i = include-ℙrop-ℙrop A i ′∨ include-ℙrop-ℙrop B i
  include-ℙrop-ℙrop (A ′⇒ B) i = include-ℙrop-ℙrop A i ′⇒ include-ℙrop-ℙrop B i
  include-ℙrop-ℙrop true = refl
  include-ℙrop-ℙrop false = refl

  include-Ctx-Ctx : ∀ Γ → include-Ctx syn-SPwF T ↑_ Γ ≡ Γ
  include-Ctx-Ctx [] = refl
  include-Ctx-Ctx (Γ ⨾ x) i = include-Ctx-Ctx Γ i ⨾ include-ℙrop-ℙrop x i

  syn-T-model : is-T-model syn-SPwF T
  syn-T-model .is-T-model.atom = ↑_
  syn-T-model .is-T-model.axiom x = inc 
    (subst {A = Ctx (ℙrop Atom) × ℙrop Atom} (λ (Γ , A) → Γ ⊢ A) 
        (sym (include-Ctx-Ctx _ ,ₚ include-ℙrop-ℙrop _)) (ax x id-sub))

  syn-model : Mod.Ob[ T ]
  syn-model = (syn-SPwF , syn-T-model)

```

Syntax is left adjoint to forgetful functor from models to theory

```agda


-- fold-mod : ∀ {o} (T S : Theory o) → (f : Th.Hom T S) → (N : Mod.Ob[ S ])
--   → Mod.Hom[ f ] (syn-model T) N
-- fold-mod T S tf@(total-hom f f') M = shom , shom-pres where
--   open SPwF (M .fst)
--   module M = SPwF (M .fst)
--   open is-T-model (M .snd)
--   module T = Theory T

--   ιprop : ℙrop T.Atom → ∣ Ty ∣
--   ιprop = include-ℙrop (M .fst) T (atom ⊙ f)

--   ιctx : Ctx (ℙrop T.Atom) → Cx
--   ιctx = include-Ctx (M .fst) T (atom ⊙ f)

--   ιvar : ∀ {Γ A} → A ∈ᶜ Γ → ιctx Γ ⊨ ιprop A
--   ιvar here = varz
--   ιvar (there v) = wk-tm (ιvar v)

--   Fᵗ : ∀ {Γ A} → _⊢_ T Γ A → ιctx Γ ⊨ ιprop A
--   Fᵗ (ax x) = {! axiom (f' _ x)  !}
--   Fᵗ triv = ⊤-rep
--   Fᵗ (exact x) = ιvar x
--   Fᵗ (falso x) = ex-falso (ιvar x)
--   Fᵗ (assume t) = transport ⇒-rep (Fᵗ t)
--   Fᵗ (apply1 t t₁) = M.apply1 (Fᵗ t) (Fᵗ t₁)
--   Fᵗ (intro-∧ t t₁) = transport (sym ∧-rep) ((Fᵗ t) , (Fᵗ t₁))
--   Fᵗ (fst-∧ t) = transport ∧-rep (Fᵗ t) .fst
--   Fᵗ (snd-∧ t) = transport ∧-rep (Fᵗ t) .snd
--   Fᵗ (left-∨ t) = ∨-left (Fᵗ t)
--   Fᵗ (right-∨ t) = ∨-right (Fᵗ t)
--   Fᵗ (elim-∨ t l r) = M.sub-tm (extend-sub id (Fᵗ t)) 
--     (∨-elim (Fᵗ l) (Fᵗ r))

--   Fc₁ : ∀ {Γ Δ} → Sub (_⊢_ T) Γ Δ → Con[ ιctx Γ , ιctx Δ ]
--   Fc₁ ε = !
--   Fc₁ (γ ⦊ x) = transport (extend-rep _) ((Fc₁ γ) , Fᵗ x)

--   F-ext→ : ∀ Γ A
--      → M.Con[ ιctx (Γ ⨾ A) , ιctx Γ ⊕ ιprop A ]
--   F-ext→ [] _ = M.id
--   F-ext→ (Γ ⨾ x) y = (F-ext→ Γ x) ⊕₁ (ιprop y)

--   F-ext← : ∀ Γ A
--     → M.Con[ ιctx Γ ⊕ ιprop A , ιctx (Γ ⨾ A) ]
--   F-ext← Γ A = M.id

--   ⊗-⊕-ac : ∀ Γ Δ A → M.Con[ (Γ M.⊗₀ Δ) ⊕ A , Γ M.⊗₀ (Δ ⊕ A) ]
--   ⊗-⊕-ac Γ Δ A = ⟨ π₁ ∘ π₁-⊕ , extend-sub (π₂ ∘ π₁-⊕) varz ⟩

--   ⊗-⊕-ac← : ∀ Γ Δ A → M.Con[ Γ M.⊗₀ (Δ ⊕ A) , (Γ M.⊗₀ Δ) ⊕ A ]
--   ⊗-⊕-ac← Γ Δ A = extend-sub ⟨ π₁ , π₁-⊕ ∘ π₂ ⟩ (M.sub-tm π₂ varz)
  
--   shom : SPwF-hom (syn-SPwF T) (M .fst)
--   shom .SPwF-hom.Fᶜ .Functor.F₀ = ιctx
--   shom .SPwF-hom.Fᶜ .Functor.F₁ = rec! Fc₁
--   shom .SPwF-hom.Fᶜ .Functor.F-id = prop!
--   shom .SPwF-hom.Fᶜ .Functor.F-∘ _ _ = prop!
--   shom .SPwF-hom.pres-⊤ = Iff 
--     (λ x → M.id) (λ x → M.id)
--   shom .SPwF-hom.pres-∧ = Iff (elim! too) (elim! fro) where
--     too : ∀ x y → M.Con[ ιctx (x ++ y) , ιctx x M.⊗₀ ιctx y ]
--     too x [] = M.⟨ M.id , M.! ⟩
--     too x (Γ ⨾ y) = ⊗-⊕-ac (ιctx x) (ιctx Γ) (ιprop y)
--                M.∘ (too x Γ ⊕₁ (ιprop y))
--                M.∘ F-ext→ (x ++ Γ) y

--     fro : ∀ x y → Con[ ιctx x ⊗₀ ιctx y , ιctx (x ++ y) ]
--     fro _ [] = π₁
--     fro Γ (Δ ⨾ y) = (fro Γ Δ ⊕₁ (ιprop y))
--                   ∘ ⊗-⊕-ac← (ιctx Γ) (ιctx Δ) (ιprop y)
--                   ∘ (id ⊗₁ F-ext→ Δ y)

--   shom .SPwF-hom.Fᵗ = ιprop
--   shom .SPwF-hom.F-⊕ {A} = Iff (λ x → F-ext→ x A) (λ _ → M.id)
--   shom .SPwF-hom.F^tm = NT (λ Γ → rec! Fᵗ) λ _ _ _  → {!   !}
--   -- shom .SPwF-hom.F-⊥ = {!   !}

--   shom-pres : SPwF-hom-pres-T shom (unmake-theory-hom tf) (syn-T-model T) (M .snd)
--   shom-pres .SPwF-hom-pres-T.pres-atom = refl
            

-- fold-unique : ∀ {ℓ} {x y : Theory ℓ} {Y : Mod.Ob[ y ]} (f : Precategory.Hom (Th ℓ) x y)
--                 (g : SPwF-hom (syn-SPwF x) (Y .fst))
--                 → fold-mod _ _ f Y .fst ≡ g
-- fold-unique {_} {x} {y} {Y = Y} f g = {!   !} where
--   open SPwF-hom
--   F-ob : ∀ n → Functor.F₀ (Fᶜ (fold-mod x y f Y .fst)) n ≡
--       Functor.F₀ (Fᶜ g) n
--   F-ob [] = sym {! ∥-∥-ua  !}
--   F-ob (n ⨾ x) = {!   !}

--   Fᶜ-eq : fold-mod x y f Y .fst .Fᶜ ≡ g .Fᶜ
--   Fᶜ-eq = Functor-path (λ x → {!   !}) {!   !}

-- make-free-model : ∀ {ℓ} → Free-objects (Models {ℓ} {ℓ})
-- make-free-model .Free-objects.free {X} = syn-SPwF X , syn-T-model _
-- make-free-model .Free-objects.fold {X} {Y} Y' f = fold-mod X Y f Y'
-- make-free-model .Free-objects.unique f (g , g') = {!   !} ,ₚ {!   !} 
```             