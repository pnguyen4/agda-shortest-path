module Project where
open import Basics002

-- boilerplate --
top : ∀ {n : ℕ} → idx n → ℕ
top Z = 0
top (S i) = 1 + top i

lemma1 : ∀ (n : ℕ) → n <? S n ≡ [<]
lemma1 Z = ↯
lemma1 (S n) = lemma1 n

lemma2 : ∀ (n : ℕ) → ∀ (i : idx n) → top i <? S n ≡ [<]
lemma2 (S x) Z = ↯
lemma2 (S x) (S i) = lemma2 x i

red : ∀ {n : ℕ} → idx (S n) → idx (S n)
red Z = Z
red {n} (S Z) = (𝕚 Z {S n})
red {n} (S m) = (𝕚 (top m) {S n} {{lemma2 n m}})

-- return ids of adjancent vertices --
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

lookup : ∀ {n : ℕ} → idx n → list (idx n) → 𝔹
lookup x [] = O
lookup x (y ∷ ys) with top x ≡? top y
… | I = I
… | O = lookup x ys

filter-list : ∀ {n : ℕ} → list (idx n) → list (idx n) → list (idx n) 
filter-list [] ys = ys
filter-list (x ∷ xs) ys with lookup x ys
… | I = x ∷ filter-list xs ys
… | O = filter-list xs ys

{-# TERMINATING #-}
bfs-traversal' :
  ∀ {n : ℕ}
  → graph[ S n ]                          -- G: graph represented as adjacency matrix
  → list (idx (S n)) → list (idx (S n))   -- Q: processing queue, L: search result list
  → list (idx (S n))                      -- σ: seen list to detect cycle
bfs-traversal' G Q L with Q
… | [] = L
… | x ∷ xs with filter-list L (neighbors (G #[ x ]))
… | [] = bfs-traversal' G xs (L ⧺ [ x ])
… | ys = bfs-traversal' G (xs ⧺ ys) (L ⧺ [ x ])

bfs-traversal : ∀ { n } → graph[ S n ] → idx (S n) → list (idx (S n))
bfs-traversal G ι₀ = bfs-traversal' G [ ι₀ ] []

-- dijkstra work

min : ∀ {n : ℕ} → list (idx n) → (idx n) → (idx n) → (idx n) 
min l x y with top x <? top y
… | [<] = x
… | [≥] = y

foldr : ∀ {n} {A B : Set} → (A → B → B) → B → vec[ n ] A → B
foldr f z [] = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

closest-neighbor : ∀ {n} → list (idx n) → idx n 
closest-neighbor xs = {!!}

{--  FUN STUFF, PUT ASIDE FOR NOW

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

_ : let n = (𝕚 0 {3}) in top n ≡ 0
_ = ↯

_ : let n = (𝕚 2 {3}) in top n ≡ 2
_ = ↯

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

tree1 : graph[ 7 ]
tree1 = [ [ O , I , I , O , O , O , O ]
        , [ I , O , O , I , I , O , O ]
        , [ I , O , O , O , O , I , I ]
        , [ O , I , O , O , O , O , O ]
        , [ O , I , O , O , O , O , O ]
        , [ O , O , I , O , O , O , O ]
        , [ O , O , I , O , O , O , O ] 
        ]
