[![Review Assignment Due Date](https://classroom.github.com/assets/deadline-readme-button-22041afd0340ce965d47ae6ef1cefeee28c7c493a6346c4f15d667ab976d596c.svg)](https://classroom.github.com/a/dPwN1w3S)
# Final project

**Explain the general theme and specific features of your project.**
We wanted to prove specific elements of hash sets and linked lists, specifically adding and removing items from the hash set. We divided the project into two portions- one for linked lists (inside the hashset) and the hashset itself. Matthew worked mostly on linked lists, and I worked mostly on hash sets. For a linked list, we made functions for adding, removing, and checking if the linked list contains the Nat. For a hash set, we also had a put (adding it into the hash set), remove, and seeing if the hash set contains the Nat. 

We have several helper functions to check if the linked list and hash set already has the Nat inputted, ensuring we don't have any duplicates.

For dependent types, we are proved that each time we remove a Nat from a linked list, it would be removed. We also want to prove that if the item is added and the Nat is already existing, there would not be a duplicate. It would also prove that the list would contain the Nat added. 


**Cite any resources or existing code you used.**

We used Agda builtin libraries such as Nat, Bool, Equality, and Data.maybe. We also utilized ChatGPT to get an idea of how to go about certain functions such as remove-first, especially to understand the skeletal code. For hash set, I used ChatGPT for skeletal code for index and vec-apply as I wanted to ensure the definition would be compatible with other functions. 

**Discuss any challenges, or anything you'd like feedback on.**
Our main challenge was trying to set up the entire project as the idea of proving how hash set worked took a while to map out. Another challenge we had was trying to debug our definitions and holes. Because of how busy the projects got and the collective struggle to debug, I also realized you were very busy and was hard having a second to ask questions. 
NOTE: in LinkedList, I had to keep in remove-contains (even though it's not complete) for a proof in Hashset (see revoke-is-member).

