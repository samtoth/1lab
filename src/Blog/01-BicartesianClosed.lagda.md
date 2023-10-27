<!--
```agda
open import Cat.Prelude hiding (⌜_⌝;_∧_;_∨_;¬_) renaming (⊤ to 𝟙; ⊥ to 𝟘)
open Functor

open import Cat.Diagram.Product
import Cat.Morphism
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Colimit.Finite
open import Cat.Diagram.Exponential
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Monad
open import Cat.Functor.Adjoint
open import Data.Bool
```
-->

```agda
module Blog.01-BicartesianClosed where
``` 


# Bi-cartesian closed categories and Proposition Logic

In my first year computer science degree we are doing a course on propositional
logic and I wanted to write small post to show the connection that exists 
between them and a special class of [[categories|category]] called bi-cartesian closed
categories.

As an extremely quick refresher, we are introduced to propositional logic as a theory
whith boolean values usually denoted by letters $P,Q,R,S,...$, and a set of logical
connectives including $-\land-$, $-\lor-$, $-\Rightarrow-$ and $\neg-$ (with their usual meanings).
In adition we have the binary relation $P\vdash Q$ (pronounced entails) which externally
reflects the internal implication operator. i.e. $P\vdash Q$ just when $P\Rightarrow Q$ is a tautology.

If you are at all familiar with categories you might be starting to smell something here. It is quite
trivial to verify a few facts about entailment. Namely, any proposition entails itelf; and, given
$P\vdash Q$ and $Q\vdash R$ we can derive $P\vdash R$. There are many ways to verify this,
but perhaps most simply we can use a truth table.
<details>
$((P \Rightarrow Q) \land (Q \Rightarrow R)) \Rightarrow (P \Rightarrow R)$ is a tautology
 as witnessed by the following truth table:

| P | Q | R | $P\Rightarrow Q$ | $Q\Rightarrow R$ | $P\Rightarrow R$ |
|---|---|---|---|---|---|
| 0 | 0 | 0 | 1 | 1 | 1 |
| 0 | 0 | 1 | 1 | 1 | 1 |
| 0 | 1 | 0 | 1 | 0 | 1 |
| 0 | 1 | 1 | 1 | 1 | 1 |
| 1 | 0 | 0 | 0 | 1 | 0 |
| 1 | 0 | 1 | 0 | 1 | 1 |
| 1 | 1 | 0 | 1 | 0 | 0 |
| 1 | 1 | 1 | 1 | 1 | 1 |
</details>

:::{.note}
Technical aside:

Because booleans form a set (in the sense of [`Homotopy Type Theory`]), there can be at most
one unique term witnessing the equality of any two bools.
:::


[`Homotopy Type Theory`]: 1Lab.Intro.html

From this, we have enough information to give a category of booleans and entailments beween them:

```agda
Bool⊢ : Precategory lzero lzero
```

Our objects are booleans and, as desired, there is a morphism only when the implication is true for
all x and y.
```agda
Bool⊢ .Precategory.Ob = Bool
Bool⊢ .Precategory.Hom x y = imp x y ≡ true
```

Both the identity entailment and the composition ot entailments are defined by
'pattern matching', which if you haven't come across before (in the special case
 of bools) you can think of a bit like writing down a truth table and considering
all different values of the variables involved. 

```agda
Bool⊢ .Precategory.id {true} = refl
Bool⊢ .Precategory.id {false} = refl

Precategory._∘_ Bool⊢ {true} {_}     {true}  _ _ = refl
Precategory._∘_ Bool⊢ {true} {true}  {false} x _ = x
Precategory._∘_ Bool⊢ {true} {false} {false} _ y = y
Precategory._∘_ Bool⊢ {false} {_}    {_}     _ _ = refl
```
<!--
```agda
Bool⊢ .Precategory.Hom-set x y = hlevel 2

Bool⊢ .Precategory.idr f = Bool-is-set _ _ _ _
Bool⊢ .Precategory.idl f = Bool-is-set _ _ _ _
Bool⊢ .Precategory.assoc f g h = Bool-is-set _ _ _ _
```
--->

So we now have the basic structure of a category down... but there is a lot more structure
to these entailment relations than just identity and composition right?
Well it turns out category theory already has a name for most of this structure... (no prizes
for guessing this one).
Before fully diving into Bicartesian-closed categories, let's consider a motivating 
example: $-\land-$.

It's defining properties are that both $P \land Q \vdash P$ and
$P \land Q \vdash Q$. In adition it is easy to check that given
$A \vdash P \land Q$ then we must have both that $A \vdash P$ *and* $A \vdash Q$ by
simple composition. This can be summed up in the following diagram:

~~~{.quiver}
\[\begin{tikzcd}
  & A \\
  P & P \land Q & Q 
  \arrow[from=2-2, to=2-1]
  \arrow[from=2-2, to=2-3]
  \arrow[from=1-2, to=2-1]
  \arrow[from=1-2, to=2-2]
  \arrow[from=1-2, to=2-3]
\end{tikzcd}\]
~~~

Of course, this is looking very familiar, the good old categorical [[Product]]. We
can show formally that $-\land-$ is a product by the following term:

```agda
Bool-Products : has-products Bool⊢
Bool-Products a b .Product.apex = and a b

Bool-Products true true .Product.π₁ = refl
Bool-Products true false .Product.π₁ = refl
Bool-Products false b .Product.π₁ = refl

Bool-Products true b .Product.π₂ = id {b} where open Precategory Bool⊢
Bool-Products false b .Product.π₂ = refl

is-product.⟨_,_⟩ (Bool-Products true b .Product.has-is-product) {true} _ y = y
is-product.⟨_,_⟩ (Bool-Products false b .Product.has-is-product) {true} x _ = x
is-product.⟨_,_⟩ (Bool-Products a b .Product.has-is-product) {false} _ _ = refl
```
<!--
```agda
Bool-Products a b .Product.has-is-product .is-product.π₁∘factor = Bool-is-set _ _ _ _
Bool-Products a b .Product.has-is-product .is-product.π₂∘factor = Bool-is-set _ _ _ _
Bool-Products a b .Product.has-is-product .is-product.unique f g h = Bool-is-set _ _ _ _
```
--->

And so it turns out each of the operations that were introduced have a corresponding categorical
phrasing.

|  Proposition | limit  | Proposition | colimit  |
| --- | --- | --- | --- |
| $-\land-$ | [[Product]] | $-\lor-$ | [[Coproduct]] |
| $\top$ | [`Terminal`] | $\bot$ | [`Initial`] |
| $-\Rightarrow -$ | [`Exponential`] | $-\Leftarrow -$ | Coexponential | 

It is too much to cover in detail but if you explore the links you will be able to see how to give
a fairly trivial instance of each limit for our category `Bool⊢`.



```agda
record Bicartesian-closed {o} {ℓ}  (𝓒 : Precategory o ℓ) : Type (o ⊔ lsuc ℓ) where
    field complete : Finitely-complete 𝓒
    field cocomplete : Finitely-cocomplete 𝓒

    open Finitely-complete complete
    open Finitely-cocomplete cocomplete

    field cc : Cartesian-closed 𝓒 products terminal

    open Cat.Morphism 𝓒 renaming (Hom to _⊢_) public
    open Binary-products 𝓒 products renaming (_⊗₀_ to _∧_) public
    open Binary-coproducts 𝓒 coproducts hiding (unique₂) renaming (_⊕₀_ to _∨_) public
    open Cartesian-closed cc hiding (unique₂) public
    open Terminal terminal renaming (top to ⊤) public
    open Initial initial renaming (bot to ⊥) public

    coswap : ∀ {A B} → (A ∨ B) ⊢ (B ∨ A)
    coswap = [ in₁ , in₀ ]

    _⇒_ : ∀ A B → Ob
    _⇒_ = Exp.B^A

    
    ¬ : Ob → Ob
    ¬ A = A ⇒ ⊥
 

    
``` 