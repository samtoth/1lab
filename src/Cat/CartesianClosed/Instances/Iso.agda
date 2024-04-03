open import Cat.Functor.Equivalence
open import Cat.Instances.Product
open import Cat.Instances.Functor
open import Cat.Diagram.Exponential
open import Cat.Diagram.Terminal
open import Cat.Diagram.Pullback
open import Cat.Diagram.Product
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Adjoint
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Adjoint.Compose
open import Cat.Functor.Naturality
open import Cat.Functor.Base
open import Cat.Functor.Compose
import Cat.Reasoning
import Cat.Morphism
import Cat.Functor.Reasoning
import Cat.Functor.Bifunctor as Bifunctor
open import Cat.Functor.Bifunctor.Iso
open import Cat.Prelude

module Cat.CartesianClosed.Instances.Iso {o1 o2 h1 h2} 
    {C : Precategory o1 h1} {D : Precategory o2 h2}
    (fc : Finitely-complete C)
    (F : Functor C D) (iso : is-precat-iso F)
    where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D

    open is-equivalence (is-precat-iso→is-equivalence iso)
    open is-precat-iso iso
    module Cf = Finitely-complete fc

    module F = Cat.Functor.Reasoning F
    module F-lex = is-lex (right-adjoint→lex F⁻¹⊣F)
    module F⁻¹ = Functor F⁻¹

    open _=>_
    
      
  R-finitely-complete : Finitely-complete D
  R-finitely-complete = complete where
    open Finitely-complete
    open Terminal
    open Pullback
    open Product
    module [D,D] = Cat.Morphism (Cat[ D , D ])
    
    term : Terminal D
    term .top = F.₀ (top Cf.terminal)
    term .has⊤ = right-adjoint→terminal F⁻¹⊣F (has⊤ Cf.terminal)


    product : ∀ A B → Product D A B
    product A B = prod where
      module Prod = Product (Cf.products (F⁻¹.₀ A) (F⁻¹.₀ B))
      
      prod : Product D A B
      prod .apex = F.₀ Prod.apex 
      prod .π₁ = counit.ε _ D.∘ F.₁ Prod.π₁
      prod .π₂ = counit.ε _ D.∘ F.₁ Prod.π₂
      prod .has-is-product = is-product-iso D (counit-iso _) (counit-iso _)
         (F-lex.pres-product (has⊤ Cf.terminal) Prod.has-is-product)

    pb : has-pullbacks D
    pb {A} {B} {X} f g = the-pb where

      module PB = Pullback (Cf.pullbacks (F⁻¹.₁ f) (F⁻¹.₁ g))
      module Pb = is-pullback (right-adjoint→is-pullback F⁻¹⊣F PB.has-is-pb)

      the-pb : Pullback D f g
      the-pb .apex = F.₀ PB.apex
      the-pb .p₁ = counit.ε _ D.∘ F.₁ PB.p₁
      the-pb .p₂ = counit.ε _ D.∘ F.₁ PB.p₂
      the-pb .has-is-pb = pb' where
        open is-pullback
        pb' : is-pullback D _ f _ g
        pb' .square = square' where abstract
          square' : f D.∘ counit.ε _ D.∘ F.₁ PB.p₁ ≡ g D.∘ counit.ε _ D.∘ F.₁ PB.p₂
          square' = 
            f D.∘ counit.ε _ D.∘ F.₁ PB.p₁              ≡⟨ D.extendl (sym $ counit.is-natural _ _ _) ⟩
            counit.ε _ D.∘ F.₁ (F⁻¹.₁ f) D.∘ F.₁ PB.p₁  ≡⟨ D.refl⟩∘⟨ Pb.square ⟩
            counit.ε _ D.∘ F.₁ (F⁻¹.₁ g) D.∘ F.₁ PB.p₂  ≡⟨ D.extendl (counit.is-natural _ _ _) ⟩
            g D.∘ counit.ε B D.∘ F.₁ PB.p₂              ∎

        pb' .universal {p₁' = p₁'} {p₂'} p = Pb.universal {p₁' = counit⁻¹ .η _ D.∘ p₁'} {counit⁻¹ .η _ D.∘ p₂'} path' where abstract
             path' : F.₁ (F⁻¹.₁ f) D.∘ (counit⁻¹ .η _) D.∘ p₁' ≡ F.₁ (F⁻¹.₁ g) D.∘ (counit⁻¹ .η B) D.∘ p₂'
             path' = 
              F.₁ (F⁻¹.₁ f) D.∘ counit⁻¹ .η _ D.∘ p₁' ≡⟨ D.extendl (sym $ counit⁻¹ .is-natural _ _ _) ⟩
              counit⁻¹ .η _ D.∘ f D.∘ p₁'             ≡⟨ D.refl⟩∘⟨ p ⟩
              counit⁻¹ .η _ D.∘ g D.∘ p₂'             ≡⟨ D.extendl (counit⁻¹ .is-natural _ _ _) ⟩
              F.₁ (F⁻¹.₁ g) D.∘ counit⁻¹ .η _ D.∘ p₂' ∎
              
        pb' .p₁∘universal = D.pullr Pb.p₁∘universal ∙ D.cancell (counit-iso _ .D.is-invertible.invl)
        pb' .p₂∘universal = D.pullr Pb.p₂∘universal ∙ D.cancell (counit-iso _ .D.is-invertible.invl)
        pb' .unique p q = Pb.unique 
          (sym (D.assoc _ _  _ ∙ ap (D._∘ _) (D.cancell (counit-iso _ .D.is-invertible.invr))) ∙ ap (_ D.∘_) p)
          (sym (D.assoc _ _  _ ∙ ap (D._∘ _) (D.cancell (counit-iso _ .D.is-invertible.invr))) ∙ ap (_ D.∘_) q)



    complete : Finitely-complete _
    complete .terminal = term
    complete .products = product
    complete .equalisers = with-pullbacks D term pb .Finitely-complete.equalisers
    complete .pullbacks = pb
 
  private module Df = Finitely-complete R-finitely-complete

  private 
    module Cat[C×C,D] = Cat.Reasoning (Cat[ C ×ᶜ C , D ])
    module Cp = Binary-products C Cf.products
    module Dp = Binary-products D Df.products
      

  pres-product-F⁻¹ : F⁻¹ F∘ Dp.×-functor => Cp.×-functor F∘ (F⁻¹ F× F⁻¹)
  pres-product-F⁻¹ .η x = Cp.⟨ F⁻¹.₁ Dp.π₁ , F⁻¹.₁ Dp.π₂ ⟩
  pres-product-F⁻¹ .is-natural (a , x) (b , y) (f , g) 
    = Cp.⟨ F⁻¹.₁ Dp.π₁ , F⁻¹.₁ Dp.π₂ ⟩ C.∘ F⁻¹.₁ (f Dp.⊗₁ g)                       ≡⟨ Cp.⟨⟩∘ _ ⟩
      Cp.⟨ F⁻¹.₁ Dp.π₁ C.∘ F⁻¹.₁ (f Dp.⊗₁ g) , F⁻¹.₁ Dp.π₂ C.∘ F⁻¹.₁ (f Dp.⊗₁ g) ⟩ ≡⟨ ap₂ Cp.⟨_,_⟩ (sym $ F⁻¹.F-∘ _ _) (sym $ F⁻¹.F-∘ _ _) ⟩
      Cp.⟨ F⁻¹.₁ (Dp.π₁ D.∘ (f Dp.⊗₁ g)) , F⁻¹.₁ (Dp.π₂ D.∘ (f Dp.⊗₁ g)) ⟩         ≡⟨ ap₂ Cp.⟨_,_⟩ (ap F⁻¹.₁ Dp.π₁∘⟨⟩) (ap F⁻¹.₁ Dp.π₂∘⟨⟩) ⟩
      Cp.⟨ F⁻¹.₁ (f D.∘ Dp.π₁) , F⁻¹.₁ (g D.∘ Dp.π₂) ⟩                             ≡⟨ ap₂ Cp.⟨_,_⟩ (F⁻¹.F-∘ _ _) (F⁻¹.F-∘ _ _) ⟩
      Cp.⟨ F⁻¹.₁ f C.∘ F⁻¹.₁ Dp.π₁ , F⁻¹.₁ g C.∘ F⁻¹.₁ Dp.π₂ ⟩                     ≡⟨ sym (Cp.⟨⟩-unique _ (C.pulll Cp.π₁∘⟨⟩ ∙ C.pullr Cp.π₁∘⟨⟩) ((C.pulll Cp.π₂∘⟨⟩ ∙ C.pullr Cp.π₂∘⟨⟩)) ) ⟩
      (F⁻¹.₁ f Cp.⊗₁ F⁻¹.₁ g) C.∘ Cp.⟨ F⁻¹.₁ Dp.π₁ , F⁻¹.₁ Dp.π₂ ⟩ ∎

  pres-product-iso-F⁻¹ : ∀ x → C.is-invertible (pres-product-F⁻¹ .η x)
  pres-product-iso-F⁻¹ (x , y) = inv' where
    module F⁻¹p = is-product (right-adjoint→is-product F⊣F⁻¹ (Df.products x y .Product.has-is-product))
    open Cat.Morphism.is-invertible
    open Cat.Morphism.Inverses

    inv' : C.is-invertible (pres-product-F⁻¹ .η (x , y))    
    inv' .inv = F⁻¹p.⟨ Cp.π₁ , Cp.π₂ ⟩
    inv' .inverses .invl 
      = Cp.⟨ F⁻¹.₁ Dp.π₁ , F⁻¹.₁ Dp.π₂ ⟩ C.∘ F⁻¹p.⟨ Cp.π₁ , Cp.π₂ ⟩ ≡⟨ Cp.⟨⟩∘ _ ⟩
        Cp.⟨ F⁻¹.₁ Dp.π₁ C.∘ _ , F⁻¹.₁ Dp.π₂ C.∘ _ ⟩                ≡⟨ ap₂ Cp.⟨_,_⟩ F⁻¹p.π₁∘factor F⁻¹p.π₂∘factor ⟩
        Cp.⟨ Cp.π₁ , Cp.π₂ ⟩                                        ≡⟨ Cp.⟨⟩-η ⟩
        C.id ∎
    inv' .inverses .invr 
      = F⁻¹p.⟨ Cp.π₁ , Cp.π₂ ⟩ C.∘ Cp.⟨ F⁻¹.₁ Dp.π₁ , F⁻¹.₁ Dp.π₂ ⟩ ≡⟨ F⁻¹p.⟨⟩∘ _ ⟩
        F⁻¹p.⟨ Cp.π₁ C.∘ _ , Cp.π₂ C.∘ _ ⟩                          ≡⟨ ap₂ F⁻¹p.⟨_,_⟩ Cp.π₁∘⟨⟩ Cp.π₂∘⟨⟩ ⟩
        F⁻¹p.⟨ F⁻¹.₁ Dp.π₁ , F⁻¹.₁ Dp.π₂ ⟩                          ≡⟨ F⁻¹p.⟨⟩-η ⟩
        C.id ∎

  pres-product-iso : F⁻¹ F∘ Dp.×-functor ≅ⁿ Cp.×-functor F∘ (F⁻¹ F× F⁻¹)
  pres-product-iso = is-invertibleⁿ→isoⁿ (invertible→invertibleⁿ pres-product-F⁻¹ pres-product-iso-F⁻¹)

  module _ (cc : Cartesian-closed C Cf.products Cf.terminal) where
    open Cartesian-closed


    R-cartesian-closed : Cartesian-closed D Df.products Df.terminal
    R-cartesian-closed = product-adjoint→cartesian-closed D Df.products Df.terminal exp adj where
      module [D,D] = Cat.Reasoning Cat[ D , D ]

      _^- : C.Ob → Functor C C
      _^- = Bifunctor.Right ([-,-] C _ _ cc)

      exp : D.Ob → Functor D D
      exp A = F F∘ (F⁻¹.₀ A ^-) F∘ F⁻¹

      adj1 : ∀ {A} → (F F∘ (Bifunctor.Left Cp.×-functor (F⁻¹.₀ A))) F∘ F⁻¹ ⊣ exp A
      adj1 {A} = LF⊣GR F⁻¹⊣F (LF⊣GR (product⊣exponential C _ _ cc {F⁻¹.₀ A}) F⊣F⁻¹)

      II : ∀ {A} → Bifunctor.Left Cp.×-functor (F⁻¹.₀ A) F∘ F⁻¹ ≅ⁿ F⁻¹ F∘ Bifunctor.Left Dp.×-functor A
      II {A} = lem2 ∘ni lem ∘ni lem3 where
        lem : Bifunctor.Left (Cp.×-functor F∘ (F⁻¹ F× F⁻¹)) A ≅ⁿ Bifunctor.Left (F⁻¹ F∘ Dp.×-functor) A
        lem = Left-iso _ _ pres-product-iso A ni⁻¹

        lem2 : (Bifunctor.Left Cp.×-functor (F⁻¹ .Functor.F₀ A) F∘ F⁻¹) ≅ⁿ Bifunctor.Left (Cp.×-functor F∘ (F⁻¹ F× F⁻¹)) A
        lem2 = Left∘-F×- _ _ _ _ ni⁻¹

        lem3 : Bifunctor.Left (F⁻¹ F∘ Dp.×-functor) A ≅ⁿ F⁻¹ F∘ Bifunctor.Left Dp.×-functor A
        lem3 = -∘Left _ _ _


      pres-prod : ∀ {A} → ((F F∘ Bifunctor.Left Cp.×-functor (F⁻¹.₀ A)) F∘ F⁻¹) ≅ⁿ
                            (Bifunctor.Left Dp.×-functor A)
      pres-prod = ni-assoc ni⁻¹ ∘ni (_ ▸ni II) ∘ni ni-assoc ∘ni (F∘-iso-id-l F∘F⁻¹≅Id)

      adj : ∀ A → Bifunctor.Left Dp.×-functor A ⊣ exp A
      adj A = adjoint-natural-isol pres-prod adj1


  -- Alternatively, D is cartesian-closed with respect to any choice of limits
  module _ (cc : Cartesian-closed C Cf.products Cf.terminal) (df' : Finitely-complete D) where
    open Cartesian-closed
    module Df' = Finitely-complete df'

    R-cartesian-closed' : Cartesian-closed D Df'.products Df'.terminal
    R-cartesian-closed' = product-adjoint→cartesian-closed D Df'.products Df'.terminal exp adj where
      module [D,D] = Cat.Reasoning Cat[ D , D ]
      module Dp' = Binary-products D Df'.products

      module Dcc = Cartesian-closed (R-cartesian-closed cc)

      exp : D.Ob → Functor D D
      exp = Bifunctor.Right ([-,-] D Df.products Df.terminal (R-cartesian-closed cc))

      adj : ∀ A → Bifunctor.Left Dp'.×-functor A ⊣ exp A
      adj A = adjoint-natural-isol (Left-iso _ _ (×-functor-Unique D Df.products Df'.products) _) (product⊣exponential D Df.products Df.terminal (R-cartesian-closed cc))
   
  -- pres-product : F F∘ Cp.×-functor => Dp.×-functor F∘ (F F× F)
  -- pres-product .η (x , y) = Dp.⟨ F.₁ Cp.π₁ , F.₁ Cp.π₂ ⟩
  -- pres-product .is-natural (a , x) (b , y) (f , g) =
  --    Dp.⟨ F.₁ Cp.π₁ , F.₁ Cp.π₂ ⟩ D.∘ F.₁ (f Cp.⊗₁ g)                     ≡⟨ Dp.⟨⟩∘ _ ⟩
  --    Dp.⟨ F.₁ Cp.π₁ D.∘ F.₁ (f Cp.⊗₁ g) , F.₁ Cp.π₂ D.∘ F.₁ (f Cp.⊗₁ g) ⟩ ≡⟨ ap₂ Dp.⟨_,_⟩ (sym $ F.F-∘ _ _) (sym $ F.F-∘ _ _) ⟩
  --    Dp.⟨ F.₁ (Cp.π₁ C.∘ (f Cp.⊗₁ g)) , F.₁ (Cp.π₂ C.∘ (f Cp.⊗₁ g)) ⟩     ≡⟨ ap₂ Dp.⟨_,_⟩ (ap F.₁ Cp.π₁∘⟨⟩) (ap F.₁ Cp.π₂∘⟨⟩) ⟩
  --    Dp.⟨ F.₁ (f C.∘ Cp.π₁) , F.₁ (g C.∘ Cp.π₂) ⟩                         ≡⟨ ap₂ Dp.⟨_,_⟩ (F.F-∘ _ _) (F.F-∘ _ _) ⟩
  --    Dp.⟨ F.₁ f D.∘ F.₁ Cp.π₁ , F.₁ g D.∘ F.₁ Cp.π₂ ⟩                     ≡⟨ sym (Dp.⟨⟩-unique _ (D.pulll Dp.π₁∘⟨⟩ ∙ D.pullr Dp.π₁∘⟨⟩) ((D.pulll Dp.π₂∘⟨⟩ ∙ D.pullr Dp.π₂∘⟨⟩)) ) ⟩
  --    (F.₁ f Dp.⊗₁ F.₁ g) D.∘  Dp.⟨ F.₁ Cp.π₁ , F.₁ Cp.π₂ ⟩                ∎
  
  -- pres-product-iso : ∀ x → D.is-invertible (pres-product .η x)
  -- pres-product-iso (x , y) = inv' where
  --   module Fp = is-product (right-adjoint→is-product F⁻¹⊣F (Cf.products x y .Product.has-is-product))
  --   open Cat.Morphism.is-invertible
  --   open Cat.Morphism.Inverses

  --   inv' : D.is-invertible (pres-product .η (x , y))
  --   inv' .inv = Fp.⟨ Dp.π₁ , Dp.π₂ ⟩
  --   inv' .inverses .invl = 
  --     Dp.⟨ F.₁ Cp.π₁ , F.₁ Cp.π₂ ⟩ D.∘ Fp.⟨ Dp.π₁ , Dp.π₂ ⟩ ≡⟨ Dp.⟨⟩∘ _ ⟩
  --     Dp.⟨ F.₁ Cp.π₁ D.∘ _ , F.₁ Cp.π₂ D.∘ _ ⟩              ≡⟨ ap₂ Dp.⟨_,_⟩ Fp.π₁∘factor Fp.π₂∘factor ⟩
  --     Dp.⟨ Dp.π₁ , Dp.π₂ ⟩                                  ≡⟨ Dp.⟨⟩-η ⟩
  --     D.id                                                  ∎
  --   inv' .inverses .invr = 
  --     Fp.⟨ Dp.π₁ , Dp.π₂ ⟩ D.∘ Dp.⟨ F.₁ Cp.π₁ , F.₁ Cp.π₂ ⟩ ≡⟨ Fp.⟨⟩∘ _ ⟩
  --     Fp.⟨ Dp.π₁ D.∘ _ , Dp.π₂ D.∘ _ ⟩                      ≡⟨ ap₂ Fp.⟨_,_⟩ Dp.π₁∘⟨⟩ Dp.π₂∘⟨⟩ ⟩
  --     Fp.⟨ F.₁ Cp.π₁ , F.₁ Cp.π₂ ⟩                          ≡⟨ Fp.⟨⟩-η ⟩
  --     D.id                                                  ∎

  -- pres-product⁻¹ : Dp.×-functor F∘ (F F× F) => F F∘ Cp.×-functor
  -- pres-product⁻¹ .η _ = pres-product-iso _ .D.is-invertible.inv
  -- pres-product⁻¹ .is-natural (x , y) (a , b) (f , g) = 
  --   a×b.⟨ Dp.π₁ , Dp.π₂ ⟩ D.∘ (F.₁ f) Dp.⊗₁ (F.₁ g)  ≡⟨ a×b.⟨⟩∘ _ ⟩
  --   a×b.⟨ Dp.π₁ D.∘ _ , Dp.π₂ D.∘ _ ⟩                ≡⟨ ap₂ a×b.⟨_,_⟩ Dp.π₁∘⟨⟩ Dp.π₂∘⟨⟩ ⟩
  --   a×b.⟨ F.₁ f D.∘ Dp.π₁ , F.₁ g D.∘ Dp.π₂ ⟩        ≡⟨ sym (a×b.unique _ leftside rightside) ⟩
  --   (F.₁ (f Cp.⊗₁ g)) D.∘ x×y.⟨ Dp.π₁ , Dp.π₂ ⟩      ∎ where

  --   module x×y = is-product (right-adjoint→is-product F⁻¹⊣F (Cf.products x y .Product.has-is-product))
  --   module a×b = is-product (right-adjoint→is-product F⁻¹⊣F (Cf.products a b .Product.has-is-product))

  --   leftside : F.₁ (fc .Finitely-complete.products a b .Product.π₁) D.∘
  --      (F.₁ Cp.⟨ f C.∘ Cp.π₁ , g C.∘ Cp.π₂ ⟩ D.∘
  --           x×y.⟨ Dp.π₁ , Dp.π₂ ⟩)
  --    ≡ F.₁ f D.∘ Dp.π₁
  --   leftside = 
  --     F.₁ _ D.∘ F.₁ _ D.∘ _     ≡⟨ D.pulll (sym $ F.F-∘ _ _) ⟩
  --     F.₁ (_ C.∘ _) D.∘ _       ≡⟨ ap F.₁ Cp.π₁∘⟨⟩ D.⟩∘⟨refl ⟩
  --     F.₁ (f C.∘ Cp.π₁) D.∘ _   ≡⟨ D.pushl (F.F-∘ _ _) ⟩
  --     F.₁ f D.∘ F.₁ Cp.π₁ D.∘ _ ≡⟨ D.refl⟩∘⟨ x×y.π₁∘factor ⟩
  --     F.₁ f D.∘ Dp.π₁           ∎

  --   rightside = 
  --     F.₁ _ D.∘ F.₁ _ D.∘ _     ≡⟨ D.pulll (sym $ F.F-∘ _ _) ⟩
  --     F.₁ (_ C.∘ _) D.∘ _       ≡⟨ ap F.₁ Cp.π₂∘⟨⟩ D.⟩∘⟨refl ⟩
  --     F.₁ (g C.∘ Cp.π₂) D.∘ _   ≡⟨ D.pushl (F.F-∘ _ _) ⟩
  --     F.₁ g D.∘ F.₁ Cp.π₂ D.∘ _ ≡⟨ D.refl⟩∘⟨ x×y.π₂∘factor ⟩
  --     F.₁ g D.∘ Dp.π₂           ∎ 