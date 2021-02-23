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


## sig and pred specifics
Stop
- This defines the basic structure underlying a town and a subway system; what stops need to be reached
- It holds a set of connections that are all other Stops that can be reached directly from the current Stop and how long it would take to travel between the current stop to each of those

Route
- This defines the path of a single subway line
- It helps separate out all different lines included in the subway system

StopPath
- Defines a path between two stops by taking the proposed subway system
- Is helpful for finding the distance of that path (defined in connections) since it groups the relevant path segments from Route together

isTown

validRoutes

isLine

isSubwaySystem

validStopPaths
- Makes sure that all StopPaths are valid
- Ensures the start Stop can reach the end Stop by the given route segments
- Sets dist to be the combined distance of all route segments
- DOES NOT constrain the route to be linear. Since we are constraining a max distance between any two stops, extra line segments (even if they aren't exactly on the path) can't change a false check to a true one. (if <direct path dist> + <extra> is less than <max allowed dist> then <direct path dist> must be less than <max allowed dist>)

maxDistance
- Actually places the constraint that all stops must be within a certain travel distance
- Checks that all pairs of stops have a valid StopPath with a distance less than the given maximum distance
