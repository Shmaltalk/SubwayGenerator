# SubwayGenerator


## Description of Project
Suppose you are planning a subway system to be built in a city. Given a set representing all locations at which you want the subway to stop, as well as an undirected, weighted graph representing the possible connections that could be built between them, this model generates possible subway maps such that a passenger would be able to get from any arbitrary stop to any other arbitrary stop in at most some given x time. The weights of the graph represent a theoretical time that traveling between two stops would take.

## Constraints/Design Choices
A town map is a graph that represents all possible connections between subway stops and the time it would take to travel between them. It must be...
- connected: Any two stops in a town should be reachable from each other
- undirected: You should be able to travel identically to and from any two stops in the same amount of time. While this may not be true when traveling on streets, since we want to build a subway system travel would be underground and unaffected by things like buildings or one way streets.
- weighted: It should take some positive, nonzero amount of time to travel between any two subway stops
- irreflexive: There should not be a direct path from a subway stop to itself with a non-zero travel time (staying still could be interpreted as "traveling from a stop to itself", but since this would take 0 travel time we do not include it in the model)

A generated subway system is a set of subway lines, each of which stops at at least 2 stops. Passengers can switch between two lines at stops where they both stop. 

Properties of lines
- undirected (symmetric): the trains go back and forth on a single path, so if the subway goes from a stop s1 to a stop s2, then it also goes from s2 to s1.
- connected: any two stops on the line should be reachable from each other.
- has endpoints: there should be exactly two stops (the endpoints of the line) that are each directly connected to only one other stop. (Even though it's possible in the real world to have a subway line whose path is a loop, i.e. no endpoints, we chose to exclude this from our model. This constraint also rules out trivial subway "lines" that are empty or only contain a single stop.)
- not branching: each stop should be directly connected to at most 2 other stops, the one before it and the one after it. (Again, branching is possible in a real-world subway line, but we chose to exclude it for simplicity.)

Properties of a subway system
- must cover all subway stops in the map
- must be connected
- no line should be contained in another line, since such a line would be useless (however, we do allow lines to overlap, since you could have two subway lines whose paths run side by side for a while)
- must take less than a given x time to get between any two stops

## tests and run statements

Please see the code for descriptions of individual tests. Overall, we tested each individual predicate with positive (should pass) and negative (should fail) tests, then included some examples to confirm the system works as a whole.

We also have a run statement which creates possible subway maps for a town with 4 stops; the distance can be adjusted and other constraints can be added to produce different maps. (When viewing in Sterling, we recommend using Show as Attribute for all fields to get rid of clutter.)


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
- Places physically reasonable constraints on the connections relation
- Ensures that the map of possible connections between stops is connected, undirected, irreflexive, and has all positive weights

validRoutes
- Ensures the subway routes generated are physically reasonable, i.e., their union is contained in the set of possible connections (note: this is equivalent to checking that each individual subway route is contained in the set of connections)

isLine
- Checks whether a given path (relation from Stop to Stop) is a valid subway line
- Ensures that the path is undirected, connected, has endpoints, and has no branching

isSubwaySystem
- Checks that the map is a town (isTown)
- Checks that the routes generated are valid (validRoutes) and that each route is a subway line (isLine)
- Checks that any two stops are connected by the route paths
- Checks that no subway line is contained in another line

validStopPaths
- Makes sure that all StopPaths are valid
- Ensures the start Stop can reach the end Stop by the given route segments
- Sets dist to be the combined distance of all route segments
- DOES NOT constrain the route to be linear. Since we are constraining a max distance between any two stops, extra line segments (even if they aren't exactly on the path) can't change a false check to a true one. (if <direct path dist> + <extra> is less than <max allowed dist> then <direct path dist> must be less than <max allowed dist>)

maxDistance
- Actually places the constraint that all stops must be within a certain travel distance
- Checks that all pairs of stops have a valid StopPath with a distance less than the given maximum distance
