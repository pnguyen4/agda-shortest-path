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

-- Breadth-first search returns shortest path between two nodes in graph.
-- (path length measured by # of edges)
bfs' :
  ∀ {n}
  → graph[ n ]                  -- G: Graph represented as adjacency matrix
  → idx n → idx n               -- ι₀: starting node ID, ι₁: target node ID
  → list (idx n) → list (idx n) -- Q: processing queue, P: pending path
  → vec[ n ] 𝔹                  -- σ: seen list to detect cycle
  → list (idx n) ∧ vec[ n ] 𝔹
bfs' G ι₀ ι₁ Q P σ with σ #[ ι₁ ]
… | I = ⟨ P , σ ⟩
… | O with length[list] Q
… | Z = ⟨ [] , σ #[ ι₀ ↦ I ] ⟩
… | S n = {!!}
-- function returns path when target found in seenlist or
-- emptylist when queue is empty due to node has no child and target not in seenlist.

bfs : ∀ { n } → graph[ n ] → idx n → idx n → list (idx n)
bfs G ι₀ ι₁ = let ⟨ x , y ⟩ = bfs' G ι₀ ι₁ [ ι₀ ] [] (const[vec]< _ > O) in x

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
