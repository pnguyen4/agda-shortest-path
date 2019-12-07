module Project where
open import Basics002

-- boilerplate --
idxval : ∀ {n : ℕ} → idx n → ℕ
idxval Z = 0
idxval (S i) = 1 + idxval i

lemma1 : ∀ (n : ℕ) → n <? S n ≡ [<]
lemma1 Z = ↯
lemma1 (S n) = lemma1 n

lemma2 : ∀ (n : ℕ) → ∀ (i : idx n) → idxval i <? S n ≡ [<]
lemma2 (S x) Z = ↯
lemma2 (S x) (S i) = lemma2 x i

lemma3 : ∀ (n : ℕ) → ∀ (i : idx n) → idxval i <? n ≡ [<]
lemma3 Z ()
lemma3 (S n) Z = ↯
lemma3 (S n) (S i) = lemma3 n i

-- return ids of adjancent vertices --
{-# TERMINATING #-}
neighbors : ∀ {n : ℕ} → vec[ S n ] 𝔹 → list (idx (S n))
neighbors {n} v = neighbors' v (𝕚 n {S n} {{lemma1 n}}) []
  where
  reduce : ∀ {n : ℕ} → idx (S n) → idx (S n)
  reduce Z = Z
  reduce {n} (S Z) = (𝕚 Z {S n})
  reduce {n} (S m) = (𝕚 (idxval m) {S n} {{lemma2 n m}})

  neighbors' : ∀ {n : ℕ} → vec[ S n ] 𝔹 → idx (S n) → list (idx (S n)) → list (idx (S n))
  neighbors' v Z l with v #[ Z ]
  … | I = Z ∷ l
  … | O = l
  neighbors' {n} v m l with v #[ m ]
  … | I = neighbors' v (reduce m) (m ∷ l)
  … | O = neighbors' v (reduce m) l

lookup : ∀ {n : ℕ} → idx n → list (idx n) → 𝔹
lookup x [] = O
lookup x (y ∷ ys) with idxval x ≡? idxval y
… | I = I
… | O = lookup x ys

filter-list : ∀ {n : ℕ} → list (idx n) → list (idx n) → list (idx n)
filter-list [] ys = []
filter-list (x ∷ xs) ys with lookup x ys
… | I = filter-list xs ys
… | O = x ∷ filter-list xs ys

{-- BFS Traverse : returns list of nodes ordered by first seen to last --}
--------------------------------------------------------------------------
{-# TERMINATING #-}
bfs-traverse : ∀ {n : ℕ} → graph[ S n ] → idx (S n) → list (idx (S n))
bfs-traverse G ι₀ = bfs-traverse' G [ ι₀ ] [] [ ι₀ ]
  where
  bfs-traverse' :
    ∀ {n : ℕ}
    → graph[ S n ]                         -- G: graph represented as adjacency matrix
    → list (idx (S n)) → list (idx (S n))  -- Q: processing queue, L: search result list
    → list (idx (S n))                     -- σ: seen list to avoid cycles
    → list (idx (S n))
  {- Terminates when queue is empty, that is, when all possible neighbors are seen -}
  bfs-traverse' G Q L σ with Q
  … | [] = L
  … | x ∷ xs with filter-list (neighbors (G #[ x ])) σ
  … | [] = bfs-traverse' G xs (L ⧺ [ x ]) σ
  … | ys = bfs-traverse' G (xs ⧺ ys) (L ⧺ [ x ]) (σ ⧺ ys)

{-- Breadth-First Search : returns shortest path between two nodes in graph --}
-------------------------------------------------------------------------------
{-# TERMINATING #-}
bfs : ∀ {n : ℕ} → graph[ S n ] → idx (S n) → idx (S n) → list ℕ
bfs {n} G ι₀ ι₁ = let prev = bfs' G ι₀ ι₁ [ ι₀ ] [ ι₀ ] (const[vec]< S n > ι₁)
                  in return-path prev ι₁ []
  where
  update-prevs : ∀ {n : ℕ} → vec[ S n ] (idx (S n)) → idx (S n) → list (idx (S n)) → vec[ S n ] (idx (S n))
  update-prevs ρ x [] = ρ
  update-prevs {n} ρ x (y ∷ ys) = let i = (𝕚 (idxval x) {(S n)} {{lemma3 (S n) x}})
                                  in update-prevs (ρ #[ y ↦ i ]) x ys
  {- Terminates when queue is empty, that is, when all possible neighbors are seen -}
  bfs' :
    ∀ {n}
    → graph[ S n ]                         -- G: graph represented as adjacency matrix
    → idx (S n) → idx (S n)                -- ι₀: starting node ID, ι₁: target node ID
    → list (idx (S n)) → list (idx (S n))  -- Q: processing queue, σ: seen list
    → vec[ S n ] (idx (S n))               -- ρ: previous nodes list, default value is target
    → vec[ S n ] (idx (S n))
  bfs' G ι₀ ι₁ Q σ ρ with Q
  … | [] = ρ
  … | x ∷ xs with filter-list (neighbors (G #[ x ])) σ
  … | [] = bfs' G ι₀ ι₁ xs σ ρ
  … | ys = bfs' G ι₀ ι₁ (xs ⧺ ys) (σ ⧺ ys) (update-prevs ρ x ys)

  -- Terminates when prev is target, aka when source is found.
  -- Value of prev[source] will always be target because source never gets passed into
  -- update-prevs due to the fact that seenlist starts with source and thus gets filtered.
  return-path : vec[ S n ] (idx (S n)) → idx (S n) → list ℕ → list ℕ
  return-path prev ι res with idxval(prev #[ ι ]) ≡? idxval ι₁
  … | O = return-path prev (prev #[ ι ]) (idxval (prev #[ ι ]) ∷ res)
  … | I with idxval ι₀ ≡? idxval ι₁ | res
  … | O | [] = res                        -- path to node does not exist
  … | O | xs = res ⧺ [ idxval ι₁ ]        -- path found from ι₀ to ι₁
  … | I | _ = res ⧺ [ idxval ι₁ ]         -- path found, search for self


{-- Miscellaneous Tests --}
_ : 𝕚 2 {3} ≡ S (S Z)
_ = ↯
_ : 𝕚 1 {3} ≡ S Z
_ = ↯
_ : let n = (𝕚 0 {3}) in idxval n ≡ 0
_ = ↯
_ : let n = (𝕚 2 {3}) in idxval n ≡ 2
_ = ↯
_ : neighbors [ I , O , I ] ≡ [ 𝕚 0 , 𝕚 2 ]
_ = ↯
_ : filter-list [ 𝕚 0 {7} , 𝕚 1 {7} ] [ 𝕚 0 {7} ] ≡ [ 𝕚 1 {7} ]
_ = ↯
_ : lookup (𝕚 1 {7}) [ 𝕚 0 {7} , 𝕚 1 {7} ] ≡ I
_ = ↯
_ : lookup (𝕚 5 {7}) [ 𝕚 0 {7} , 𝕚 1 {7} ] ≡ O
_ = ↯
_ : neighbors [ O , I , I , O , O , O , O ]  ≡ [ 𝕚 1 , 𝕚 2 ]
_ = ↯
_ : filter-list (neighbors [ I , O , O , I , I , O , O ] ) [ 𝕚 0 ] ≡ [ 𝕚 3 , 𝕚 4 ]
_ = ↯
_ : const[vec]< 3 > (𝕚 3 {4}) ≡ [ 𝕚 3 , 𝕚 3 , 𝕚 3 ]
_ = ↯

{-- BFS Traverse and Search Demo --}
------------------------------------
tree1 : graph[ 7 ]
tree1 = [ [ O , I , I , O , O , O , O ]
        , [ I , O , O , I , I , O , O ]    --          (0)
        , [ I , O , O , O , O , I , I ]    --         /   \
        , [ O , I , O , O , O , O , O ]    --        /     \
        , [ O , I , O , O , O , O , O ]    --     (1)       (2)
        , [ O , O , I , O , O , O , O ]    --    /   \     /   \
        , [ O , O , I , O , O , O , O ]    --  (3)   (4) (5)   (6)
        ]
{- traversal logic
input: tree1, 0
pass#     queue        result            seenlist
0:        [0]          []                [0]
1:        [1,2]        [0]               [0,1,2]
2:        [2,3,4]      [0,1]             [0,1,2,3,4]
3:        [3,4,5,6]    [0,1,2]           [0,1,2,3,4,5,6]
4:        [4,5,6]      [0,1,2,3]         [0,1,2,3,4,5,6]
5:        [5,6]        [0,1,2,3,4]       [0,1,2,3,4,5,6]
6:        [6]          [0,1,2,3,4,5]     [0,1,2,3,4,5,6]
7:        []           [0,1,2,3,4,5,6]   [0,1,2,3,4,5,6]
-}
_ : bfs-traverse tree1 Z ≡ [ 𝕚 0 , 𝕚 1 , 𝕚 2 , 𝕚 3 , 𝕚 4 , 𝕚 5 , 𝕚 6 ]
_ = ↯
-- find path from 0 to itself, no hop
_ : bfs tree1 Z Z ≡ [ 0 ]
_ = ↯
-- find path from 0 to 2, one hop
_ : bfs tree1 Z (𝕚 2) ≡ [ 0 , 2 ]
_ = ↯
-- find path from 0 to 2, two hops
_ : bfs tree1 Z (𝕚 6) ≡ [ 0 , 2 , 6 ]
_ = ↯

undirectedgraph1 : graph[ 5 ]
undirectedgraph1 = [ [ O , I , I , O , O ]
                   , [ I , O , I , I , O ]
                   , [ I , I , O , I , I ]  --    (1)-(3)
                   , [ O , I , I , O , I ]  --    / \ / \
                   , [ O , O , I , I , O ]  --  (0)-(2)-(4)
                   ]
{- traversal logic
input: undirectedgraph1 0
pass#     queue        result       seenlist
0:        [0]          []           [0]
1:        [1,2]        [0]          [0,1,2]
2:        [2,3]        [0,1]        [0,1,2,3]
3:        [3,4]        [0,1,2]      [0,1,2,3,4]
4:        [4]          [0,1,2,3]    [0,1,2,3,4]
5:        []           [0,1,3,3,4]  [0,1,2,3,4]
-}
_ : bfs-traverse undirectedgraph1 Z ≡ [ 𝕚 0 , 𝕚 1 , 𝕚 2 , 𝕚 3 , 𝕚 4 ]
_ = ↯
-- note that path 1-2-4 is equal in length to path 1-3-4 but
-- lower numbered nodes get precedence in this implementation.
_ : bfs undirectedgraph1 (𝕚 1) (𝕚 4) ≡ [ 1 , 2 , 4 ]
_ = ↯

undirectedgraph2 : graph[ 7 ]
undirectedgraph2 = [ [ O , I , O , O , O , O , O ]
                   , [ I , O , I , O , I , O , O ]  --
                   , [ O , I , O , I , O , O , O ]  --  (6) <- isolated node
                   , [ O , O , I , O , O , I , O ]  --
                   , [ O , I , O , O , O , I , O ]  --        (2)-(3)
                   , [ O , O , O , I , I , O , O ]  --        /     \
                   , [ O , O , O , O , O , O , O ]  --  (0)-(1)-(4)-(5)
                   ]
-- path between 0 and 6 doesn't exist, 6 has no connections
_ : bfs undirectedgraph2 Z (𝕚 6) ≡ []
_ = ↯
-- path between 0 and 5 exists, does not return 0-1-2-3-5
_ : bfs undirectedgraph2 Z (𝕚 5) ≡ [ 0 , 1 , 4 , 5 ]
_ = ↯

-- Fundamental idea of PROVING BFS finds shortest path:
--
-- Shortest path to node starting from itself is through itself                                  [dist = 0]
-- Shortest path to unweigted adjacent node is to that node.                                     [dist = 1]
-- Shortest path from u to v : (shortest path from u to neighbor of v, with dist d) + (neighbor v to v)   [dist = d+1]
-- INDUCTION on d

{- IDEAPAD
1. v is reachable from u if bfs G u v contains v
2. perhaps even showing that shortest-path(s to t) = (s to neighbor) ++ shortest-path(neighbor to t)
3.
bfs G i1 i2 returns list i1...i2
if (bfs G u v) contains v:
  if i1=i2 and path=[i1] then it is a shortest-path
  if i1≢i2 and path=[i1,i2] then it is a shortest-path
  if i1≢i2 and path=[i1,...,x,i2] assume bfs G i1 x is shortest path
     then show (bfs G i1 x) + (x,i2) is shortest path frcom i1 to i2
-}
