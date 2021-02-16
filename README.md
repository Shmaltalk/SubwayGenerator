# SubwayGenerator


## Description of Project
Given an undirected, weighted graph representing all subway stops in a city, this model generates possible subway maps such that a passenger would be able to get from any arbitrary stop to any other arbitrary stop in at most some given x time. The weights of the graph represent a theoretical time that traveling between two stops would take.

## Constraints/Design Choices
A town map is a graph that represents all possible connectons between subway stops and the time it would take to travel between them. It must be...
- connected:
- undirected
- weighted
- irreflexive

A generated subway system is a set of subway lines, each of which stops at at least 2 stops. Passengers can switch between two lines at stops where they both stop. Lines must be:
- undirected: trains go back and forth on a single path
- distinct: no two lines are identical
- acyclic
- not branching

A subway system must...
- cover all subway stops in the map
- be connected
- take less than a given x time to get between any two stops
