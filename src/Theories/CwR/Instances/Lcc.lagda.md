<!--
```agda
open import Cat.Prelude
open import Cat.CartesianClosed.Locally
open import Cat.Instances.Sets.Complete
open import Cat.Instances.Sets.CartesianClosed
open import Cat.Functor.WideSubcategory
open import Cat.Displayed.Cartesian.Discrete
open import Theories.CwR
```
-->

```agda
module Theories.CwR.Instances.Lcc where
```

Any locally cartesian closed category is trivially a CwR
where the class of representable maps is the entire category.

```agda
module _ {o} {ℓ} {𝓒 : Precategory o ℓ} (lcc : Locally-cartesian-closed 𝓒) where

  open Locally-cartesian-closed lcc

  lcc→CwR : CwR-structure _ 𝓒
  lcc→CwR .CwR-structure.has-is-lex = has-is-lex
  lcc→CwR .CwR-structure.R .Wide-subcat.P _ = ⊤
  lcc→CwR .CwR-structure.R .Wide-subcat.P-prop _ = hlevel!
  lcc→CwR .CwR-structure.R .Wide-subcat.P-id = _
  lcc→CwR .CwR-structure.R .Wide-subcat.P-∘ = _
  lcc→CwR .CwR-structure.R-stable = _
  lcc→CwR .CwR-structure.f* {f = f} _ = lcc→dependent-product 𝓒 lcc f
  lcc→CwR .CwR-structure.f⊣f* {f = f} _ = lcc→pullback⊣dependent-product 𝓒 lcc f
```

```agda
Sets-CwR : ∀ {ℓ} → CwR-structure _ (Sets ℓ)
Sets-CwR = lcc→CwR Sets-lcc
```

```agda
DFibs-CwR : ∀ {o ℓ} (𝓒 : Precategory o ℓ) → CwR-structure _ (Discrete-fibrations 𝓒)
DFibs-CwR 𝓒 = lcc→CwR (subst Locally-cartesian-closed (sym $ DFibs≡PSh 𝓒) {!   !})
```