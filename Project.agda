module Project where
open import Basics001
  
topology1 : graph[ 5 ]
topology1 = [ [ O , I , I , O , O ]
            , [ I , O , I , I , O ]
            , [ I , I , O , I , I ]
            , [ O , I , I , O , I ]
            , [ O , O , I , I , O ]
            ]

-- Breadth-first search returns shortest path between two nodes in graph.
-- (path length measured by # of edges)
-- BFS (graph, start node, end node, seen list) → (node_found, path)
bfs : ∀ {n} → graph[ n ] → idx n → idx n → vec[ n ] ℕ -> list (idx n) ∧ vec[ n ] 𝔹
bfs = ?
