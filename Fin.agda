-- This Fin data type was pulled from one of our previous assignments in class

module Fin where

open import Agda.Builtin.Nat
  using (Nat; suc; zero)

data Fin : Nat → Set where
  fzero : ∀ {n}
    → Fin (suc n)
  fsuc : ∀ {n} → Fin n
    → Fin (suc n)
  
  
maximum : {n : Nat} → Fin (suc n)
maximum {zero} = fzero
maximum {suc n} = fsuc maximum