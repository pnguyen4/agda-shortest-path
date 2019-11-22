module Project where
open import Basics001

topology1 : graph[ 5 ]
topology1 = [ [ O , I , I , O , O ]
            , [ I , O , I , I , O ]
            , [ I , I , O , I , I ]
            , [ O , I , I , O , I ]
            , [ O , O , I , I , O ]
            ]

-- Primarily going to be used with "_⧺_"
zip : ∀ {A : Set} → (A → A → A) → list A → list A → list A
zip f x [] = x
zip f [] y = y
zip f (x ∷ xs) (y ∷ ys) = f x y ∷ zip f xs ys

map : ∀ {A B : Set} → (A → B) → list A → list B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : ∀ {A B : Set} → (A → B → B) → B → list A → B
foldr f z [] = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

concat-lists : ∀ {A : Set} → list (list A) → list A
concat-lists [] = []
concat-lists (x ∷ xs) = x ⧺ concat-lists xs

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
… | I = P
… | O with length[list] Q
… | Z = []
… | S n = {!!}
{-
… | S n = let ι₀' = {!!}
              Q' = {!!}
              P' = P ⧺ [ ι₀ ]
              σ' = {!!}
              in {!!}
              --merge( map bfs on children )
-}

_idx<?_ : ∀ {n} → idx n → ℕ → <!
_ idx<? Z = [≥]
Z idx<? _ = [<]
(S m) idx<? (S n) = m idx<? n

{-
{-# TERMINATING #-}
-- retrieve list of indices from graph entry
children : ∀ { n } → vec[ n ] 𝔹 → idx n → list (idx n) → list (idx n)
children {n} v i res with i idx<? n
… | [≥] = res
… | [<] with v #[ i ]
… | I = children v {!!} res
… | O = children v {!!} (res ⧺ [ i ])
-}

tolist : ∀ {A : Set} {n} → vec[ n ] A → list A
tolist [] = []
tolist (x ∷ xs) = x ∷ tolist xs

length[vec] : ∀ {A : Set} {n} → vec[ n ] A → ℕ
length[vec] {n = n} _ = n

head[vec] : ∀ {A : Set} {n} → vec[ S n ] A → A
head[vec] (x ∷ xs) = x

tail[vec] : ∀ {A : Set} {n} → vec[ S n ] A → vec[ n ] A
tail[vec] (x ∷ xs) = xs

{-# TERMINATING #-}
children' : ∀ {n} → vec[ n ] 𝔹 → idx n → list (idx n) → list (idx n)
children' v i res with length[vec] v
… | Z = res
… | S m with head[vec] v
… | O = children' {!tail[vec] v!} (S {!!}) res
… | I = children' {!tail[vec] v!} (S {!!}) (res ⧺ [ i ])

index : {n : ℕ} → idx n → ℕ
index {n} i = n

children : ∀ {n} → graph[ n ] → idx n → list (idx n)
children g i = let v = g #[ i ] in children' v i []

{-# TERMINATING #-}
bfs-traversal' :
  ∀ {n}
  → graph[ n ]                  -- G: graph represented as adjacency matrix
  → list (idx n) → list (idx n) -- Q: processing queue, L: search result list
  → list (idx n)
--  → vec[ n ] 𝔹                  -- σ: seen list to detect cycle
bfs-traversal' G Q L with Q
… | [] = L
… | x ∷ xs with children G x
… | [] = bfs-traversal' G xs (L ⧺ [ x ])
… | ys = bfs-traversal' G (xs ⧺ ys) (L ⧺ [ x ])

bfs-traversal : ∀ { n } → graph[ n ] → idx n → list (idx n)
bfs-traversal G ι₀ = bfs-traversal' G [ ι₀ ] []

bfs : ∀ { n } → graph[ n ] → idx n → idx n → list (idx n)
bfs G ι₀ ι₁ = bfs' G ι₀ ι₁ [ ι₀ ] [] (const[vec]< _ > O)

{-
-- Breadth-first search returns shortest path between two nodes in graph.
-- (path length measured by # of edges)
-- BFS (graph, start node, end node, path, seen list) → (path, seen list)
bfs' : ∀ {n} → graph[ n ] → idx n → idx n → list (idx n) → vec[ n ] 𝔹 -> list (idx n) ∧ vec[ n ] 𝔹
bfs' G ι₀ ι₁ L σ with σ #[ ι₁ ]
… | I = ⟨ L , σ ⟩
… | O with length[list] L
… | Z = ⟨ [] , σ #[ ι₀ ↦ I ] ⟩
… | S n = {!!}
-}


{-
unicode notes:
  ↦ is \r|-
-}
