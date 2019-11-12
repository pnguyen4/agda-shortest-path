
# Project Proposal

### Members of group:

Phillip Nguyen (just me)

## GitHub ids for all members of your group:

pnguyen4

### Algorithm or datastructure name:

Dijkstra's shortest path algorithm

### Algorithm or datastructure reference:

https://www-m3.ma.tum.de/foswiki/pub/MN0506/WebHome/dijkstra.pdf
https://en.wikipedia.org/wiki/Dijkstra's_algorithm

### Theorem(s) you plan to prove:

1. Breadth-first search returns shortest path between two nodes in graph (path length measured by # of edges).
2. Dijkstra's algorithm (with all edge weights being equal) solution contains shortest path for starting node to every other node.
3. BFS graph (n1 in graph) (n2 in graph) is contained in DA-no-weights graph node_1 ≡ True
    or maybe something like:  graph -> node -> list node -> map (BFS graph n) ns ≡ DA graph n
4. Dijustra's algorithm (with weights considered) yields lowest cost paths between starting node and every other node (measured by sum of weights).
5. Breadth-first search terminates.
6. Dijkstra's algorithm without weights terminates.
6. Dijkstra's algorithm terminates.

### Datatypes you will use or need not already provided:

weighted graph

### Minimum Viable Product (MVP):

I want to at least show that Dijkstra's algorithm will return the shortest path between two nodes. This
will initially be demonstrated with a simplified Dijkstra's algorithm where all weighs equal 1.
I believe that the best way to go about this is to relate it to breadth-first search and I'll probably
just assume that breadth-first search returns the shortest path (as a starting point).

