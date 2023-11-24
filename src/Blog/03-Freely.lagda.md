<!--
```agda
{-# OPTIONS -v test:20 #-}
open import 1Lab.Prelude

open import 1Lab.Reflection
open import 1Lab.Reflection.Record

module Blog.03-Freely where
```
--->

So often we want a category with some extra structure that is freely generated
from some objects.
```agda

-- Fields→Data

```




```agda
free-object : TC Name → TC Name → Name → TC ⊤
free-object getName getImplName `R = do
  record-type `R-con fields ← getDefinition `R
    where _ → typeError (nameErr `R ∷ strErr " is not a record type" ∷ [])
  

  let fields = field-names→paths fields

  `R-ty ← getType `R
  con-ty ← getType `R-con 
  
--   record→iso `R λ args → do
--     let con-ty = instantiate′ `R-ty con-ty
--     `S ← pi-term→sigma con-ty
--     returnTC `S

  debugPrint "test" 20 
      ("R-ty: " ∷ termErr `R-ty ∷ "\ncon-ty: " ∷ termErr con-ty ∷ [])
  
  nm ← getName
  declareData nm 0 `R-ty
  
  defineData nm []
--   defineFun nm
--     ( redo-clauses fields ++
--       undo-clauses fields ++
--       redo-undo-clauses fields ++
--       undo-redo-clauses fields)


  implName <- getImplName
  declareDef (argN implName) =<< debug! =<< unquoteTC ((lit (name `R)))
  defineFun implName []
  returnTC tt
```


```agda


private
  module _ {ℓ} (A : Type ℓ) where
    record T : Type ℓ where
      no-eta-equality
      field
        ⦃ fp ⦄ : A
        {f} : A → A
        fixed : f fp ≡ fp

    unquoteDecl FreeT FreeT-T = free-object (returnTC FreeT) (returnTC FreeT-T) (quote T)

    -- _ : FreeT
    -- _ = {!   !} 

``` 