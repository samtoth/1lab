
<!--
```agda
open import Cat.Prelude hiding (zero)
open import Cat.Abelian.Base
open import Cat.Abelian.Images
open import Cat.Diagram.Zero
open import Cat.Diagram.Image
open import Cat.Diagram.Equaliser.Kernel
open import Cat.Diagram.Coequaliser
```
-->

```agda
module Cat.Abelian.Exact {o ℓ : Level} {𝓒 : Precategory o ℓ} (Ab : is-abelian 𝓒) where
    
open is-abelian Ab
open ∅ renaming (∅ to zero)

private module Imgs {A B} (f : Hom A B) = Image 𝓒 (images Ab f)
open Imgs

private variable
  A B C : Ob

```

# Exact sequences

A pair of composable morphisms in an Abelian category,
$$
A \xrightarrow{f} B \xrightarrow{g} C
$$

is said to be exact when the image of f is equal to the kernel of g and $g \circ f = 0$

~~~{.quiver}
\[\begin{tikzcd}
	& B && A && C \\
	\\
	& {\mathit{Im}(f)} \\
	\\
	{\mathit{Ker}(g)}
	\arrow["g", curve={height=-12pt}, from=1-2, to=1-6]
	\arrow["f", from=1-4, to=1-2]
	\arrow["0"', from=1-4, to=1-6]
	\arrow[from=1-4, to=3-2]
	\arrow[curve={height=-12pt}, dashed, from=1-4, to=5-1]
	\arrow["i", hook, from=3-2, to=1-2]
	\arrow[dashed, from=3-2, to=5-1]
	\arrow[curve={height=-12pt}, hook, from=5-1, to=1-2]
	\arrow["0"', curve={height=30pt}, from=5-1, to=1-6]
\end{tikzcd}\]
~~~

```agda
Im→Ker : (f : Hom A B) → (g : Hom B C) → g ∘ f ≡ zero→ → Hom (Im f) (Ker.ker g)
Im→Ker {A} {B} f g p = universal f (Ker.kernel g) (kernels-are-subobjects _ ∅ _ (Ker.has-is-kernel g))
                        (Ker.universal g {A} {f} (p ∙ (sym $ zero-∘r f))) (Ker.factors g) 

is-mono-Im→Ker : ∀ (f : Hom A B) → (g : Hom B C) → (p : g ∘ f ≡ zero→)
               → is-monic (Im→Ker f g p)
is-mono-Im→Ker f g p = monic-cancell (subst (is-monic)
                       (sym $ universal-factors f) (Im→codomain-is-monic f))
```

```agda
record Exact (f : Hom A B) (g : Hom B C) : Type (o ⊔ ℓ) where
  field ∘-zero : g ∘ f ≡ zero→
        exact : Coker.coeq f ∘ Ker.kernel g  ≡ zero→

  im-iso : Im f ≅ Ker.ker g
  im-iso = {!   !}
```

A morphism $f : A \to B$ is monic iff $0 \xrightarrow{} A \xrightarrow{f} B$ is exact.

```agda
-- Coker0 : Path (Hom A (Coker.coapex {A} zero→)) (Coker.coeq zero→) zero→
-- Coker0 {A} = {!   !} where
--   lem : zero→ {A} ≡ Coker.universal zero→ (zero-∘r 0m ∙ sym (zero-∘l _)) ∘ Coker.coeq zero→ 
--   lem = sym (Coker.factors zero→)

mono→exact-l : ∀ {f : Hom A B} → is-monic f → Exact {zero} zero→ f
mono→exact-l x .Exact.∘-zero = ¡-unique₂ _ _
mono→exact-l {A} x .Exact.exact = {! Coker.coeq  !} ∙ zero-∘r (Ker.kernel _) 
  -- coker-zero : Path (Hom A (Coker.coapex zero→)) (Coker.coeq zero→) zero→
  -- coker-zero = {!    !}

exact-l→mono : ∀ {f : Hom A B} → Exact {zero} zero→ f → is-monic f
exact-l→mono = {!   !}
```

Dually, a morphism $f : A \to B$ is epic iff $A \xrightarrow{f} B \xrightarrow{} 0$ is exact. 

```agda
epi→exact-r : ∀ {f : Hom A B} → is-epic f → Exact {C = zero} f zero→
epi→exact-r = {!   !}


exact-r→epi : ∀ {f : Hom A B} → is-epic f → Exact {C = zero} f zero→
exact-r→epi = {!   !}
```


## Category of Exact sequences

```agda
Exacts : Precategory o ℓ
Exacts = {!   !}

```