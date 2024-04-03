<!--
```agda
open import Cat.Functor.Properties
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning

open _=>_ using (is-natural)
open Functor
```
-->

```agda
module Cat.Diagram.Monad where
```

<!--
```
module _ {o h : _} (C : Precategory o h) where
  private module C = Cat.Reasoning C
```
-->

# Monads {defines=monad}

A **monad on a category** $\cC$ is one way of categorifying the
concept of [monoid]. Specifically, rather than living in a monoidal
category, a monad lives in a bicategory. Here, we concern ourselves with
the case of monads in the bicategory of categories, so that we may say:
A monad is an endofunctor $M$, equipped with a `unit`{.Agda} natural
transformation $\Id \To M$, and a `multiplication`{.Agda
ident=mult} $(M \circ M) \To M$.

[monoid]: Algebra.Monoid.html

```agda
  record Monad : Type (o ⊔ h) where
    no-eta-equality
    field
      M    : Functor C C
      unit : Id => M
      mult : (M F∘ M) => M
```

<!--
```agda
    module unit = _=>_ unit
    module mult = _=>_ mult

    M₀   = M .F₀
    M₁   = M .F₁
    M-id = M .F-id
    M-∘  = M .F-∘
    open unit using (η) public
    open mult renaming (η to μ) using () public
```
-->

Furthermore, these natural transformations must satisfy identity and
associativity laws exactly analogous to those of a monoid.

```agda
    field
      left-ident  : ∀ {x} → μ x C.∘ M₁ (η x) ≡ C.id
      right-ident : ∀ {x} → μ x C.∘ η (M₀ x) ≡ C.id
      mult-assoc  : ∀ {x} → μ x C.∘ M₁ (μ x) ≡ μ x C.∘ μ (M₀ x)
```

# Algebras over a monad {defines="monad-algebra algebra-over-a-monad"}

One way of interpreting a monad $M$ is as giving a _signature_ for an
algebraic theory. For instance, the [[free monoid]] monad describes the
signature for the theory of monoids, and the [[free group|free group
construction]] monad describes the theory of groups.

Under this light, an **algebra over a monad** is a way of _evaluating_
the abstract operations given by a monadic expression to a concrete
value. Formally, an algebra for $M$ is given by a choice of object $A$
and a morphism $\nu : M(A) \to A$.

```agda
  record Algebra-on (M : Monad) (ob : C.Ob) : Type (o ⊔ h) where
    no-eta-equality
    open Monad M

    field
      ν : C.Hom (M₀ ob) ob
```

This morphism must satisfy equations categorifying those which define a
monoid action. If we think of $M$ as specifying a signature of
_effects_, then `v-unit`{.Agda} says that the `unit`{.Agda} has no
effects, and `v-mult`{.Agda} says that, given two layers $M(M(A))$, it
doesn't matter whether you first join then evaluate, or evaluate twice.

```agda
      ν-unit : ν C.∘ η ob ≡ C.id
      ν-mult : ν C.∘ M₁ ν ≡ ν C.∘ μ ob

  Algebra : Monad → Type (o ⊔ h)
  Algebra M = Σ _ (Algebra-on M)
```

<!--
```agda
  Algebra-on-pathp
    : ∀ {M} {X Y} (p : X ≡ Y) {A : Algebra-on M X} {B : Algebra-on M Y}
    → PathP (λ i → C.Hom (Monad.M₀ M (p i)) (p i)) (A .Algebra-on.ν) (B .Algebra-on.ν)
    → PathP (λ i → Algebra-on M (p i)) A B
  Algebra-on-pathp over mults i .Algebra-on.ν = mults i
  Algebra-on-pathp {M} over {A} {B} mults i .Algebra-on.ν-unit =
    is-prop→pathp (λ i → C.Hom-set _ _ (mults i C.∘ M.η _) (C.id {x = over i}))
      (A .Algebra-on.ν-unit) (B .Algebra-on.ν-unit) i
    where module M = Monad M
  Algebra-on-pathp {M} over {A} {B} mults i .Algebra-on.ν-mult =
    is-prop→pathp (λ i → C.Hom-set _ _ (mults i C.∘ M.M₁ (mults i)) (mults i C.∘ M.μ _))
      (A .Algebra-on.ν-mult) (B .Algebra-on.ν-mult) i
    where module M = Monad M
```
-->

# Eilenberg-Moore category {defines=eilenberg-moore-category}

If we take a monad $M$ as the signature of an (algebraic) theory, and
$M$-algebras as giving _models_ of that theory, then we can ask (like
with everything in category theory): Are there maps between
interpretations? The answer (as always!) is yes: An `algebra
homomorphism`{.Agda ident=Algebra-hom} is a map of the underlying
objects which "commutes with the algebras".

```agda
  record Algebra-hom (M : Monad) (X Y : Algebra M) : Type (o ⊔ h) where
    no-eta-equality
    constructor algebra-hom
    private
      module X = Algebra-on (X .snd)
      module Y = Algebra-on (Y .snd)

    open Monad M

    field
      morphism : C.Hom (X .fst) (Y .fst)
      commutes : morphism C.∘ X.ν ≡ Y.ν C.∘ M₁ morphism

  open Algebra-hom
```

We can be more specific about "commuting with the algebras" by drawing a
square: A map $m : X \to Y$ in the ambient category is a homomorphism of
$M$-algebras when the square below commutes.

~~~{.quiver}
\[\begin{tikzcd}
  {M(X)} && {M(Y)} \\
  \\
  {X} && {Y}
  \arrow["{M_1(m)}", from=1-1, to=1-3]
  \arrow["{\nu}"', from=1-1, to=3-1]
  \arrow["{\nu\prime}", from=1-3, to=3-3]
  \arrow["m"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

Since `commutes`{.Agda} is an identification between morphisms, it
inhabits a proposition (because `Hom-sets are sets`{.Agda
ident=C.Hom-set}), equality of algebra homomorphisms only depends on an
equality of their underlying morphisms.

```agda
  Algebra-hom-path
    : {M : Monad} {X Y : Algebra M} {F G : Algebra-hom M X Y}
    → morphism F ≡ morphism G
    → F ≡ G
  Algebra-hom-path x i .morphism = x i
  Algebra-hom-path {M = M} {X} {Y} {F} {G} x i .commutes =
    is-prop→pathp (λ i → C.Hom-set _ _ (x i C.∘ X .snd .Algebra-on.ν)
                                      (Y .snd .Algebra-on.ν C.∘ Monad.M₁ M (x i)))
      (F .commutes) (G .commutes) i
```

<!--
```agda
  Algebra-hom-pathp
    : {M : Monad} {W X Y Z : Algebra M}
      {F : Algebra-hom M W X}
      {G : Algebra-hom M Y Z}
      (p : W ≡ Y)
      (q : X ≡ Z)
    → PathP _ (morphism F) (morphism G)
    → PathP (λ i → Algebra-hom M (p i) (q i)) F G
  Algebra-hom-pathp p q r i .morphism = r i
  Algebra-hom-pathp {M = M} {W} {X} {Y} {Z} {F} {G} p q r i .commutes =
    is-prop→pathp (λ i → C.Hom-set _ _ (r i C.∘ p i .snd .Algebra-on.ν)
                                      (q i .snd .Algebra-on.ν C.∘ Monad.M₁ M (r i)))
      (F .commutes) (G .commutes) i
```
-->

<!--
```agda
open Algebra-hom public

open _=>_ using (η)

module _ {o ℓ} {C : Precategory o ℓ} {M : Monad C} where instance
  private module C = Cat.Reasoning C

  Extensional-Algebra-Hom
    : ∀ {ℓr} {a b} {A : Algebra-on C M a} {B : Algebra-on C M b}
    → ⦃ sa : Extensional (C.Hom a b) ℓr ⦄
    → Extensional (Algebra-hom C M (a , A) (b , B)) ℓr
  Extensional-Algebra-Hom ⦃ sa ⦄ = injection→extensional!
    (Algebra-hom-path C) sa

  Funlike-Algebra-hom
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {X Y}
    → ⦃ i : Funlike (C.Hom (X .fst) (Y .fst)) A B ⦄
    → Funlike (Algebra-hom C M X Y) A B
  Funlike-Algebra-hom ⦃ i ⦄ .Funlike._#_ f x = f .morphism # x

unquoteDecl H-Level-Algebra-hom = declare-record-hlevel 2 H-Level-Algebra-hom (quote Algebra-hom)

module _ {o ℓ} (C : Precategory o ℓ) where
  private module C = Cat.Reasoning C
```
-->

Since the square we drew above commutes for the identity morphism, and
we can show that the composite of two algebra homomorphisms is an
algebra homomorphism, they assemble into a category: The
**Eilenberg-Moore** category of $M$.

```agda
  module _ (M : Monad C) where
    private
      module M = Monad M
    open M hiding (M)
    open Precategory
    open Algebra-on

    Eilenberg-Moore : Precategory _ _
    Eilenberg-Moore .Ob = Algebra C M
    Eilenberg-Moore .Hom X Y = Algebra-hom C M X Y
```

Defining the identity and composition maps is mostly an exercise in
categorical yoga:

```agda
    Eilenberg-Moore .id {o , x} .morphism = C.id
    Eilenberg-Moore .id {o , x} .commutes =
      C.id C.∘ ν x     ≡⟨ C.id-comm-sym ⟩
      ν x C.∘ C.id     ≡⟨ ap (C._∘_ _) (sym M-id) ⟩
      ν x C.∘ M₁ C.id  ∎

    Eilenberg-Moore ._∘_ {_ , x} {_ , y} {_ , z} F G .morphism =
      morphism F C.∘ morphism G
    Eilenberg-Moore ._∘_ {_ , x} {_ , y} {_ , z} F G .commutes =
      (morphism F C.∘ morphism G) C.∘ ν x            ≡⟨ C.extendr (commutes G) ⟩
      ⌜ morphism F C.∘ ν y ⌝ C.∘ M₁ (morphism G)     ≡⟨ ap! (commutes F) ⟩
      (ν z C.∘ M₁ (morphism F)) C.∘ M₁ (morphism G)  ≡⟨ C.pullr (sym (M-∘ _ _)) ⟩
      ν z C.∘ M₁ (morphism F C.∘ morphism G)         ∎
```

<details>
<summary>
Because we have characterised equality of algebra homomorphisms as
equality of their underlying maps, the Eilenberg-Moore category inherits
the identity and associativity laws from its underlying category.
</summary>

```agda
    Eilenberg-Moore .idr f = ext (C.idr _)
    Eilenberg-Moore .idl f = ext (C.idl _)
    Eilenberg-Moore .assoc f g h = ext (C.assoc _ _ _)
    Eilenberg-Moore .Hom-set X Y = hlevel 2
```

</details>

By projecting the underlying object of the algebras, and the underlying
morphisms of the homomorphisms between them, we can define a functor
from `Eilenberg-Moore`{.Agda} back to the underlying category:

```agda
    Forget : Functor Eilenberg-Moore C
    Forget .F₀ = fst
    Forget .F₁ = Algebra-hom.morphism
    Forget .F-id = refl
    Forget .F-∘ f g = refl
```

The lemma `Algebra-hom-path`{.Agda} says exactly that this functor is
faithful.

```agda
    Forget-is-faithful : is-faithful Forget
    Forget-is-faithful = ext
```

## Free algebras {defines="free-algebra"}

In exactly the same way that we may construct a _[free group]_ by taking
the inhabitants of some set $X$ as generating the "words" of a group, we
can, given an object $A$ of the underlying category, build a **free
$M$-algebra** on $A$. Keeping with our interpretation of monads as
logical signatures, this is the _syntactic model_ of $M$, with a set of
"neutrals" chosen from the object $A$.

[free group]: Algebra.Group.Free.html

This construction is a lot simpler to do in generality than in any
specific case: We can always turn $A$ into an $M$-algebra by taking the
underlying object to be $M(A)$, and the algebra map to be the monadic
multiplication; The associativity and unit laws of the monad _itself_
become those of the $M$-action.

```agda
    Free : Functor C Eilenberg-Moore
    Free .F₀ A .fst = M₀ A
    Free .F₀ A .snd .ν = mult .η A
    Free .F₀ A .snd .ν-mult = mult-assoc
    Free .F₀ A .snd .ν-unit = right-ident
```

The construction of free $M$-algebras is furthermore functorial on the
underlying objects; Since the monadic multiplication is a natural
transformation $M\circ M \To M$, the naturality condition (drawn below)
doubles as showing that the functorial action of $M$ can be taken as an
algebraic action:

~~~{.quiver}
\[\begin{tikzcd}
  MMA && MMB \\
  \\
  MA && MB
  \arrow["MMf", from=1-1, to=1-3]
  \arrow["Mf"', from=3-1, to=3-3]
  \arrow["{\mu_A}"', from=1-1, to=3-1]
  \arrow["{\mu_B}", from=1-3, to=3-3]
\end{tikzcd}\]
~~~

```agda
    Free .F₁ f .morphism = M₁ f
    Free .F₁ f .commutes = sym $ mult.is-natural _ _ _
    Free .F-id = ext M-id
    Free .F-∘ f g = ext (M-∘ f g)
```

This is a free construction in the precise sense of the word: it's the
[left adjoint] to the functor `Forget`{.Agda}, so in particular it
provides a systematic, [universal] way of mapping from $\cC$ to
$\cC^M$.

[left adjoint]: Cat.Functor.Adjoint.html
[universal]: Cat.Functor.Adjoint.html#universal-morphisms

```agda
    open _⊣_

    Free⊣Forget : Free ⊣ Forget
    Free⊣Forget .unit = NT M.η M.unit.is-natural
    Free⊣Forget .counit .η x =
      record { morphism = x .snd .ν
             ; commutes = sym (x .snd .ν-mult)
             }
    Free⊣Forget .counit .is-natural x y f =
      ext (sym (commutes f))
    Free⊣Forget .zig = ext left-ident
    Free⊣Forget .zag {x} = x .snd .ν-unit
```

<!--
```agda
module _ {o h : _} {C : Precategory o h} {M N : Monad C} where
  private
    module C = Cat.Reasoning C
    module M = Monad M
    module N = Monad N

  Monad-path
    : (p0 : ∀ x → M.M₀ x ≡ N.M₀ x)
    → (p1 : ∀ {x y} (f : C.Hom x y) → PathP (λ i → C.Hom (p0 x i) (p0 y i)) (M.M₁ f) (N.M₁ f))
    → (∀ x → PathP (λ i → C.Hom x (p0 x i)) (M.η x) (N.η x))
    → (∀ x → PathP (λ i → C.Hom (p0 (p0 x i) i) (p0 x i)) (M.μ x) (N.μ x))
    → M ≡ N
  Monad-path p0 p1 punit pmult = path where
    M=N : M.M ≡ N.M
    M=N = Functor-path p0 p1

    path : M ≡ N
    path i .Monad.M = M=N i
    path i .Monad.unit =
      Nat-pathp refl M=N {a = M.unit} {b = N.unit} punit i
    path i .Monad.mult =
      Nat-pathp (ap₂ _F∘_ M=N M=N) M=N {a = M.mult} {b = N.mult} pmult i
    path i .Monad.left-ident {x = x} =
      is-prop→pathp (λ i → C.Hom-set (p0 x i) (p0 x i) (pmult x i C.∘ p1 (punit x i) i) C.id)
        M.left-ident
        N.left-ident i
    path i .Monad.right-ident {x = x} =
      is-prop→pathp (λ i → C.Hom-set (p0 x i) (p0 x i) (pmult x i C.∘ punit (p0 x i) i) C.id)
        M.right-ident
        N.right-ident i
    path i .Monad.mult-assoc {x} =
      is-prop→pathp (λ i → C.Hom-set (p0 (p0 (p0 x i) i) i) (p0 x i) (pmult x i C.∘ p1 (pmult x i) i) (pmult x i C.∘ pmult (p0 x i) i))
        M.mult-assoc
        N.mult-assoc i
```
-->
