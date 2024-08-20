# Limits in Displayed categories

```agda
open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Diagram.Limit.Base
open import Cat.Displayed.Total
open import Cat.Functor.Kan.Base
open import Cat.Instances.Shape.Terminal

import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM
import Cat.Reasoning as CR

module Cat.Displayed.Total.Limits
    {o ℓ o' ℓ'} {B : Precategory o ℓ}
    (E : Displayed B o' ℓ')
    where
    
open CR B
open Displayed E
open DR E
open DM E

```

A functor $F : E \to B$ is said to create a limit $D : \mathcal{J} \to E$,
when then limit $F\circ D : \mathcal{J} \to B$ exists in $B$, $D$ has a limit
in $E$ and the functor $F$ both preserves and reflects it.

if $(x,\eta)$ is a limit for a diagram $\mathcal{J}\to B$, 

~~~{.quiver}
\begin{tikzcd}
  && \{*\} \\
  \\
  {\cJ} &&& {} & {\cC}
  \arrow[from=3-1, to=1-3]
  \arrow["{!X}"', from=1-3, to=3-5]
  \arrow[""{name=0, anchor=center, inner sep=0}, from=3-1, to=3-5]
  \arrow["\eta"{description}, shorten <=4pt, shorten >=4pt, Rightarrow, from=1-3, to=0]
\end{tikzcd}
~~~

```agda
record make-displayed-limit {ι κ} {J : Precategory ι κ}
            (D : Functor J (∫ E))
            (has-lim : Limit (πᶠ E F∘ D))  : Type (ι ⊔ κ ⊔ ℓ' ⊔ o') where
    open Limit has-lim
    open _=>_
    module J = Precategory J
    module D = Functor D
    open Total-hom

    field apex' : Ob[ apex ]
          ψ'     : (j : J.Ob) → Hom[ cone .η j ] apex' (snd (D.₀ j))
          commutes' : ∀ {x y} (f : J.Hom x y) → D.₁ f .preserves ∘' ψ' x ≡[ commutes f ] ψ' y


    total-limit : Limit D
    total-limit .Ran.Ext = const! (apex , apex')
    total-limit .Ran.eps .η j = total-hom (cone .η j) (ψ' j)
    total-limit .Ran.eps .is-natural x y f = total-hom-path E (idr _ ∙ (sym $ commutes f)) (to-pathp $
            hom[ idr _ ∙ sym (commutes _) ] (ψ' y ∘' id') ≡˘⟨ hom[]-∙ _ _ ⟩
            hom[ commutes _ ]⁻ (hom[ idr _ ] (ψ' y ∘' id')) ≡⟨ hom[]⟩⟨ idr[] ⟩
            hom[ commutes _ ]⁻ (ψ' y)       ≡⟨ from-pathp $ symP (commutes' f) ⟩
            D.₁ f .preserves ∘' ψ' x ∎)
    total-limit .Ran.has-ran .is-ran.σ = {!   !}
    total-limit .Ran.has-ran .is-ran.σ-comm = {!   !}
    total-limit .Ran.has-ran .is-ran.σ-uniq = {!   !}
```  