```agda
open import Cat.Prelude hiding (_+_; _*_)
open import Algebra.Monoid
open import Algebra.Ring
open import Algebra.Ring.Commutative
open import Data.Sum

module Algebra.Ring.Division where
```

A Division Ring is a nontrivial ring where any non-zero element has a
multiplicative inverse.

Constructively, there are many non-equivalent notions of a division ring. 
[See nlab](https://ncatlab.org/nlab/show/field)

~~We will use the discrete field definition here, encoding the above statement
as either an element is 0 or it is invertible, hence giving us a decision
procedure for equality with 0. Furthormore, it gives us that the ring is
nontrivial, i.e. $0\neq1$~~

```
module _ {ℓ : Level} (R : Ring ℓ) where

    open Ring-on (R .snd)


    is-trivial-ring : Type _
    is-trivial-ring = 0r ≡ 1r

    is-trivial-ring-is-prop : is-prop is-trivial-ring
    is-trivial-ring-is-prop = hlevel 1

    is-division-ring : Type _
    is-division-ring = ∀ x → ¬ is-trivial-ring → ¬ x ≡ 0r → has-monoid-inverse *-monoid x

    is-division-ring-is-prop : is-prop (is-division-ring)
    is-division-ring-is-prop = hlevel 1

record DRing-on {ℓ} (R : Type ℓ) : Type ℓ where
    field
        has-ring-on   : Ring-on R
    open Ring-on has-ring-on public
    field
        division-ring : is-division-ring (el! R , has-ring-on)
```

Finally, a field is a Division Ring where the underlying ring
is commutative

```agda
record Field-on {ℓ} (R : Type ℓ) : Type ℓ where
    field
        has-CRing-on   : CRing-on R
    open CRing-on has-CRing-on public
    field
        division-ring : is-division-ring (el! R , has-ring-on)
```
