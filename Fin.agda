-- This Fin data type was pulled from one of our previous assignments in class

module Fin where

open import Agda.Builtin.Nat
  using (Nat; suc; zero)

data Fin : Nat → Set where
  zero : ∀ {n}
    → Fin (suc n)
  suc : ∀ {n} → Fin n
    → Fin (suc n)
  
  
maximum : {n : Nat} → Fin (suc n)
maximum {zero} = zero
maximum {suc n} = suc maximum