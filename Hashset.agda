module Hashset where

open import Agda.Builtin.Nat
    using (_+_; Nat; suc; zero)
open import Fin
open import LinkedList

record Hashset (A : Nat) : Set where 
    constructor
        hashset
    field
        capacity : Nat

-- return the index that the new set member should be placed in
hash-index : {n : Nat} → (x : Nat) → Nat
hash-index zero = zero
hash-index (suc x) = {!    !}

add : (A : Nat) → Hashset A → Hashset A
add = {!    !}
