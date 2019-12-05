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

-- return ids of adjancent vertices --
{-# TERMINATING #-}
neighbors : ∀ {n : ℕ} → vec[ S n ] 𝔹 → list (idx (S n))
neighbors {n} v = neighbors' v (𝕚 n {S n} {{lemma1 n}}) []
  where
  red : ∀ {n : ℕ} → idx (S n) → idx (S n)
  red Z = Z
  red {n} (S Z) = (𝕚 Z {S n})
  red {n} (S m) = (𝕚 (idxval m) {S n} {{lemma2 n m}})

  neighbors' : ∀ {n : ℕ} → vec[ S n ] 𝔹 → idx (S n) → list (idx (S n)) → list (idx (S n))
  neighbors' v Z l with v #[ Z ]
  … | I = Z ∷ l
  … | O = l
  neighbors' {n} v m l with v #[ m ]
  … | I = neighbors' v (red m) (m ∷ l)
  … | O = neighbors' v (red m) l

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

{-# TERMINATING #-}
bfs-traverse' :
  ∀ {n : ℕ}
  → graph[ S n ]                          -- G: graph represented as adjacency matrix
  → list (idx (S n)) → list (idx (S n))   -- Q: processing queue, L: search result list
  → list (idx (S n))                      -- σ: seen list to detect cycles
  → list (idx (S n))
bfs-traverse' G Q L σ with Q
… | [] = L
… | x ∷ xs with filter-list (neighbors (G #[ x ])) σ
… | [] = bfs-traverse' G xs (L ⧺ [ x ]) σ
… | ys = bfs-traverse' G (xs ⧺ ys) (L ⧺ [ x ]) (σ ⧺ ys)

bfs-traverse : ∀ { n } → graph[ S n ] → idx (S n) → list (idx (S n))
bfs-traverse G ι₀ = bfs-traverse' G [ ι₀ ] [] [ ι₀ ]

{--  FUN STUFF, PUT ASIDE FOR NOW
-- dijkstra work
min : ∀ {n : ℕ} → list (idx n) → (idx n) → (idx n) → (idx n)
min l x y with idxval x <? idxval y
… | [<] = x
… | [≥] = y

foldr : ∀ {n} {A B : Set} → (A → B → B) → B → vec[ n ] A → B
foldr f z [] = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

closest-neighbor : ∀ {n} → list (idx n) → idx n
closest-neighbor xs = {!!}

Dgraph[_] : ℕ → Set
Dgraph[ n ] = matrix[ n , n ] (ℕ ∧ ℕ)

-- tuple containing node id and edge weight
Dentry : ∀ {n} → (m : ℕ) → vec[ n ] ℕ  → vec[ n ] (ℕ ∧ ℕ)
Dentry m [] = []
Dentry m (x ∷ xs) = ⟨ m , x ⟩ ∷ Dentry (S m) xs

network : Dgraph[ 7 ]
network = let ∞ = 9999 in        -- 💩 --
          [ Dentry Z [ 0 , 4 , 3 , 7 , ∞ , ∞ , ∞ ]
          , Dentry Z [ 4 , 0 , ∞ , 1 , ∞ , 5 , ∞ ]
          , Dentry Z [ 3 , ∞ , 0 , 3 , 5 , ∞ , ∞ ]
          , Dentry Z [ 7 , 1 , 3 , 0 , 2 , 2 , 7 ]
          , Dentry Z [ ∞ , ∞ , 5 , 2 , 0 , ∞ , 2 ]
          , Dentry Z [ ∞ , 5 , ∞ , 2 , ∞ , 0 , 5 ]
          , Dentry Z [ ∞ , ∞ , ∞ , 7 , 2 , 5 , 0 ]
          ]

dijkstra' : ∀ {n} → idx n → Dgraph[ n ] → vec[ n ] ℕ → list ℕ → vec[ n ] ℕ
dijkstra' ι₀ G dist R = {!!}

--dijkstra : ∀ {n} → idx n → Dgraph[ n ] → vec[ n ] ℕ
--dijkstra {n} ι₀ G = dijkstra' ι₀ G (G #[ ι₀ ]) []
--}

zip : ∀ {A : Set} → (A → A → A) → list A → list A → list A
zip f x [] = x
zip f [] y = y
zip f (x ∷ xs) (y ∷ ys) = f x y ∷ zip f xs ys

-- Breadth-first search returns shortest path between two nodes in graph.
-- (path length measured by # of edges)
--
-- Function returns path when target found in seenlist or emptylist when
-- queue is empty due to node has no child and target not in seenlist.
bfs' :
  ∀ {n}
  → graph[ n ]                  -- G: graph represented as adjacency matrix
  → idx n → idx n               -- ι₀: starting node ID, ι₁: target node ID
  → list (idx n) → list (idx n) -- Q: processing queue, P: pending path
  → vec[ n ] 𝔹                  -- σ: seen list to detect cycle
  → list (idx n)
bfs' G ι₀ ι₁ Q P σ with σ #[ ι₁ ]
… | I = {!!}
… | O = {!!}

bfs : ∀ { n } → graph[ n ] → idx n → idx n → list (idx n)
bfs G ι₀ ι₁ = bfs' G ι₀ ι₁ [ ι₀ ] [] (const[vec]< _ > O)

tolist : ∀ {A : Set} {n} → vec[ n ] A → list A
tolist [] = []
tolist (x ∷ xs) = x ∷ tolist xs

head[vec] : ∀ {A : Set} {n} → vec[ S n ] A → A
head[vec] (x ∷ xs) = x

tail[vec] : ∀ {A : Set} {n} → vec[ S n ] A → vec[ n ] A
tail[vec] (x ∷ xs) = xs

{-
unicode notes:
  ↦ is \r|-
-}

_ : (𝕚 2 {3}) ≡ S (S Z)
_ = ↯

_ : (𝕚 1 {3}) ≡ S Z
_ = ↯

_ : let n = (𝕚 0 {3}) in idxval n ≡ 0
_ = ↯

_ : let n = (𝕚 2 {3}) in idxval n ≡ 2
_ = ↯

_ : neighbors [ I , O , I ] ≡ [ Z , S (S Z) ]
_ = ↯

_ : filter-list [ (𝕚 0 {7}) , (𝕚 1 {7}) ] [ (𝕚 0 {7}) ] ≡ [ (𝕚 1 {7}) ]
_ = ↯
_ : lookup (𝕚 1 {7}) [ (𝕚 0 {7}) , (𝕚 1 {7}) ] ≡ I
_ = ↯
_ : lookup (𝕚 5 {7}) [ (𝕚 0 {7}) , (𝕚 1 {7}) ] ≡ O
_ = ↯
_ : neighbors [ O , I , I , O , O , O , O ]  ≡ [ S Z , S(S Z) ]
_ = ↯
_ : filter-list (neighbors [ I , O , O , I , I , O , O ] ) [ Z ] ≡ [ S(S(S Z)) , S(S(S(S Z))) ]
_ = ↯

undirectedgraph1 : graph[ 5 ]
undirectedgraph1 = [ [ O , I , I , O , O ]
                 , [ I , O , I , I , O ]
                 , [ I , I , O , I , I ]
                 , [ O , I , I , O , I ]
                 , [ O , O , I , I , O ]
                 ]
{-
input: undirectedgraph1 0
pass#     queue        result       seenlist += neighbors
0:        [0]          []           [0]
1:        [1,2]        [0]          [0,1,2]
2:        [2,3]        [0,1]        [0,1,2,3]
3:        [3,4]        [0,1,2]      [0,1,2,3,4]
4:        [4]          [0,1,2,3]    [0,1,2,3,4]
5:        []           [0,1,3,3,4]  [0,1,2,3,4]
-}

_ : bfs-traverse undirectedgraph1 Z ≡ [ Z , S Z , S(S Z) , S(S(S Z)) , S(S(S(S Z))) ]
_ = ↯

tree1 : graph[ 7 ]
tree1 = [ [ O , I , I , O , O , O , O ]
        , [ I , O , O , I , I , O , O ]
        , [ I , O , O , O , O , I , I ]
        , [ O , I , O , O , O , O , O ]
        , [ O , I , O , O , O , O , O ]
        , [ O , O , I , O , O , O , O ]
        , [ O , O , I , O , O , O , O ]
        ]

{-
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

_ : bfs-traverse tree1 Z ≡ [ Z , S Z , S(S Z), S(S(S Z)), S(S(S(S Z))), S(S(S(S(S Z)))), S(S(S(S(S(S Z))))) ]
_ = ↯
