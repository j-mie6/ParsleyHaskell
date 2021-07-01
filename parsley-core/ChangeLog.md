# Revision history for `parsley-core`

## 1.0.0.0  -- 2021-06-12

* First version. Released on an unsuspecting world.
* Core factored out of the main `parsley` package

## 1.0.1.0 -- 2021-06-26

* Introduced `Lam` to the API and conversion functions for `Core.Defunc`
* Extra type ascriptions added to generated code

## 1.0.1.1 -- 2021-06-27

* Added input factoring to `try p <|> q` and also forms with `f <$> try p <|> q` and `try p $> x <|> q`

## 1.1.0.0 -- 2021-07-01

* Switched both backends to make use of `Lam` instead of `Core.Defunc`, reducing burden on GHC
* Added duplication avoidance optimisation when value to be duplicated is `Lam.Var True`