module Hashset where

open import Agda.Builtin.Nat
    using (_+_; _*_; Nat; suc; zero)
open import Data.Nat.DivMod
open import Data.Vec
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Fin
open import LinkedList

-- We are to prove: 
-- that when we put/remove, the hash number stays the same 

data _≤_ : Nat → Nat → Set where -- https://plfa.inf.ed.ac.uk/Relations/#:~:text=The%20relation%20less%20than%20or,2%202%20%E2%89%A4%203%20...
  z≤n : ∀ {n : Nat}
      --------
    → zero ≤ n
  s≤s : ∀ {m n : Nat}
    → m ≤ n
      -------------
    → suc m ≤ suc n

record Hashset (n : Nat) : Set where  -- n represents the capacity
    constructor
        hashset
    field
        buckets : Vec (LinkedList Nat) n -- Vec's that store the linked lists  
        not-zero : 1 ≤ n -- the capacity must be at least 1 (might need to ask about this)

-- converting Nat → Fin 
 
convertFin : {n : Nat} → Fin (suc n)  
convertFin {zero} = fzero
convertFin {suc n} = fsuc convertFin

-- mod that returns a Fin
_fin%_ : {n : Nat} → Nat → Nat → Fin (suc n) 
zero fin% zero = convertFin
zero fin% suc n = fzero
suc m fin% n = m fin% n

-- return the index that the new set member should be placed in
-- since we're only storing Nats, the hash code is simply the Nat, and we use mod to compute the bucket/index to store it in
hash-index : {n : Nat} → (x : Nat) → Hashset n → Fin (suc n) -- thinking we should use Fin since we're dealing with a finite range of numbers
hash-index {n} x (hashset b nz) = x fin% n

put : {n : Nat} → (x : Nat) → Hashset n → Hashset n
put = {!    !}

retrieve : {n : Nat} → (x : Nat) → Hashset n → Nat
retrieve = {!   !}

revoke : {n : Nat} → (x : Nat) → Hashset n → Hashset n
revoke = {!   !}

is-member : {n : Nat} → (x : Nat) → Hashset n → Bool
is-member = {!   !}

-- inserting the same item more than once always produces the same hashset (i.e. subsequent insertions of 'x' will not change anything)
idempotency : {n : Nat} → (x : Nat) → (hs : Hashset n) → put x (put x hs) ≡ put x hs
idempotency x (hashset b nz) = {!    !}