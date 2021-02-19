# SubwayGenerator


## Description of Project
Given an undirected, weighted graph representing all subway stops in a city, this model generates possible subway maps such that a passenger would be able to get from any arbitrary stop to any other arbitrary stop in at most some given x time. The weights of the graph represent a theoretical time that traveling between two stops would take.

## Constraints/Design Choices
A town map is a graph that represents all possible connections between subway stops and the time it would take to travel between them. It must be...
- connected
- undirected
- weighted
- irreflexive

A generated subway system is a set of subway lines, each of which stops at at least 2 stops. Passengers can switch between two lines at stops where they both stop. 

Properties of lines
- undirected (symmetric): the trains go back and forth on a single path, so if the subway goes from a stop s1 to a stop s2, then it also goes from s2 to s1.
- connected: any two stops on the line should be reachable from each other.
- not branching: each stop should be directly connected to at most 2 other stops: the one before it and the one after it.
- has endpoints: there should be exactly two stops (the endpoints of the line) that are each directly connected to only one other stop.

A subway system must...
- cover all subway stops in the map
- be connected
- have all its lines be distinct
- take less than a given x time to get between any two stops
