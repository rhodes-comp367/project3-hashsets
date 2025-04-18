module Hashset where

open import Agda.Builtin.Nat
    using (_+_; _*_; Nat; suc; zero)
open import Data.Nat.DivMod
open import Fin
open import LinkedList

data _≤_ : Nat → Nat → Set where -- https://plfa.inf.ed.ac.uk/Relations/#:~:text=The%20relation%20less%20than%20or,2%202%20%E2%89%A4%203%20...
  z≤n : ∀ {n : Nat}
      --------
    → zero ≤ n
  s≤s : ∀ {m n : Nat}
    → m ≤ n
      -------------
    → suc m ≤ suc n

record Hashset (A : Nat) : Set where 
    constructor
        hashset
    field
        capacity : Nat
        not-zero : 1 ≤ capacity -- the capacity must be at least 1 (might need to ask about this)

-- return the index that the new set member should be placed in
-- since we're only storing Nats, the hash code is simply the Nat, and we use mod to compute the bucket/index to store it in
hash-index : {A : Nat} → (x : Nat) → Hashset A → Nat -- thinking we should use Fin since we're dealing with a finite range of numbers
hash-index x (hashset (suc c) nz) = x % (suc c)

add : {A : Nat} → (x : Nat) → Hashset A → Hashset A
add = {!    !}

get : (A : Nat) → Hashset A → Nat
get = {!   !}
