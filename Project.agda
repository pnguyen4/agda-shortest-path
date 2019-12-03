module Project where
open import Basics002

_-_ : ℕ → ℕ → ℕ
m - Z = m
Z - S n = Z
S m - S n = m - n

-- boilerplate proofs --
lemma1 : ∀ (n : ℕ) → n <? S n ≡ [<]
lemma1 Z = ↯
lemma1 (S n) = lemma1 n

top : ∀ {n : ℕ} → idx n → ℕ
top Z = 0
top (S i) = 1 + top i

lemma2 : ∀ (n : ℕ) → ∀ (i : idx n) → top i <? S n ≡ [<]
lemma2 (S x) Z = ↯
lemma2 (S x) (S i) = lemma2 x i

red : ∀ {n : ℕ} → idx (S n) → idx (S n)
red Z = Z
red {n} (S Z) = (𝕚 Z {S n})
red {n} (S m) = (𝕚 (top m) {S n} {{lemma2 n m}})

{-# TERMINATING #-}
neighbors : ∀ {n : ℕ} → vec[ S n ] 𝔹 → list (idx (S n))
neighbors {n} v = neighbors' v (𝕚 n {S n} {{lemma1 n}}) []
  where
  neighbors' : ∀ {n : ℕ} → vec[ S n ] 𝔹 → idx (S n) → list (idx (S n)) → list (idx (S n))
  neighbors' v Z l with v #[ Z ]
  … | I = Z ∷ l
  … | O = l
  neighbors' {n} v m l with v #[ m ]
  … | I = neighbors' v (red m) (m ∷ l)
  … | O = neighbors' v (red m) l

_ : neighbors [ I , O , I ] ≡ [ Z , S (S Z) ]
_ = ↯

_ : neighbors [ O , I , I , O , O ] ≡ [ S Z , S (S Z) ]
_ = ↯

topology1 : graph[ 5 ]
topology1 = [ [ O , I , I , O , O ]
            , [ I , O , I , I , O ]
            , [ I , I , O , I , I ]
            , [ O , I , I , O , I ]
            , [ O , O , I , I , O ]
            ]

{-# TERMINATING #-}
bfs-traversal' :
  ∀ {n : ℕ}
  → graph[ S n ]                    -- G: graph represented as adjacency matrix
  → list (idx (S n)) → list (idx (S n))   -- Q: processing queue, L: search result list
  → list (idx (S n))                  -- σ: seen list to detect cycle
--  → vec[ n ] 𝔹
bfs-traversal' G Q L with Q
… | [] = L
… | x ∷ xs with neighbors (G #[ x ])
… | [] = bfs-traversal' G xs (L ⧺ [ x ])
… | ys = bfs-traversal' G (xs ⧺ ys) (L ⧺ [ x ])

bfs-traversal : ∀ { n } → graph[ S n ] → idx (S n) → list (idx (S n))
bfs-traversal G ι₀ = bfs-traversal' G [ ι₀ ] []

--_ : bfs-traversal topology1 Z ≡ {!!}
--_ = ↯

{--

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

min : list ℕ → (ℕ ∧ ℕ) → (ℕ ∧ ℕ) → (ℕ ∧ ℕ)
min R ⟨ π₁ , π₂ ⟩ ⟨ π₃ , π₄ ⟩ with π₃ <? π₄
… | [<] = ⟨ π₁ , π₂ ⟩
… | [≥] = ⟨ π₃ , π₄ ⟩

foldr : ∀ {n} {A B : Set} → (A → B → B) → B → vec[ n ] A → B
foldr f z [] = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

get-closest-neighbor : ∀ {n} → vec[ S n ] (ℕ ∧ ℕ) → list ℕ → ℕ
get-closest-neighbor V R = let ⟨ i , _ ⟩ = foldr min (V #[ Z ]) V in i

--dijkstra : ∀ {n} → idx n → Dgraph[ n ] → vec[ n ] ℕ
--dijkstra {n} ι₀ G = dijkstra' ι₀ G (G #[ ι₀ ]) []
--}

{--- OLD WORK

-- Primarily going to be used with "_⧺_"
zip : ∀ {A : Set} → (A → A → A) → list A → list A → list A
zip f x [] = x
zip f [] y = y
zip f (x ∷ xs) (y ∷ ys) = f x y ∷ zip f xs ys

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
… | O with length Q
… | Z = []
… | S n = {!!}
{-
… | S n = let ι₀' = {!!}
              Q' = {!!}
              P' = P ⧺ [ ι₀ ]
              σ' = {!!}
              in {!!}
              --merge( map bfs on neighbors )
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

--}

_ : (𝕚 _ {3}) ≡ S (S Z)
_ = ↯

_ : (𝕚 _ {3}) ≡ S Z
_ = ↯

--_ : 1 ≡ top (𝕚 0 {1})
--_ = ↯

--_ : (𝕚 (top (𝕚 1 {3})) {5} {{lemma1 5}}) ≡ S (S (S Z))
--_ = ↯
