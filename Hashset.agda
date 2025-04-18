module Hashset where

open import Agda.Builtin.Nat
open import LinkedList

data Hashset (A : Set) : Set where 
    capacity : Nat → Hashset A
