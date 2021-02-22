#lang forge --"curiosity_modeling" "075knkr5cf0ofmn1@gmail.com"



sig Stop {
    connections: set Stop->Int
}

sig Route {
    path: set Stop->Stop
}

sig StopPath {
    stop1: one Stop,
    stop2: one Stop,
    route: set Stop->Stop,
    dist: one Int
}

pred isTown {
    -- connected
    all s: Stop | Stop in s.*(connections.Int)
    
    -- undirected
    ~(connections.Int) in (connections.Int)

    -- weighted (all pairs of directly connected stops must have some positive, non-zero distance between them)
    (some connections) implies { all dist: Stop.(Stop.connections) | sum[dist] > 0 }
    
    -- any two stops have the same distance (in both directions)
    all s1, s2: Stop | (s1->s2 in (connections.Int)) implies {
        one (s1.(s2.connections) + s2.(s1.connections))
    }

    -- irreflexive
    no (connections.Int) & iden
}


pred validRoutes {
    -- all route paths must be in the set of stop connections
    Route.path in connections.Int
}


pred isLine[p: Stop->Stop] {
    -- undirected (symmetric)
    ~p in p

    let span = p.Stop + Stop.p {
        -- the span of the line is connected
        span->span in *p
    }
    
    -- non-branching (every stop is connected to at most two other
    -- stops, the ones "before" and "after" it)
    all s: Stop | #s.p <= 2
    
    -- line should have two distinct endpoints, each of which will be connected
    -- to only one other stop
    -- (note: this also ensures that the line contains at least 2 stops)
    #{s: Stop | #s.p = 1} = 2
}

pred isSubwaySystem {
    isTown

    -- all route paths are lines
    all r: Route | isLine[r.path]

    -- any two stops are connected by the route paths
    Stop->Stop in *(Route.path)

    -- no line is contained in another line
    all r1, r2: Route | r1.path in r2.path implies r1 = r2
}

pred validStopPaths {
    --some StopPath -- just for visualization purposes
    all n: Stop.(Stop.connections) | sum[n] <= 5 -- to prevent integer overflow

    all s: StopPath | {
        some s.route
        s.route in Route.path -- ensure all routes in StopPath are on subway lines
        s.stop2 in (s.stop1).^(s.route) -- stop1 can reach stop2 from the given route
        
        // dist is the total distance of all connections in the route
        sum[s.dist] = {
            sum start: s.route.Stop | sum end: start.(s.route) | {
                sum[end.(start.connections)]
            }
        }
    }
}

pred maxDistance[max: Int] {
    all s1: Stop, s2:(Stop - s1) | { 
        some sp: StopPath | {
            sp.stop1 = s1
            sp.stop2 = s2
            sum[sp.dist] <= sum[max]
        }
    }
}

run {validRoutes and isSubwaySystem and validStopPaths and maxDistance[sing[15]]} for exactly 3 Stop, 8 Int -- 8 just to make it a round byte

/*
-- test town
test expect {
    isConnected: isTown for {
        Stop = Stop0 + Stop1 + Stop2
        connections = Stop0->Stop1->sing[2] + Stop1->Stop0->sing[2]
    } is unsat
    isUndirected: isTown for {
        Stop = Stop0 + Stop1 + Stop2
        connections = Stop0->Stop1->sing[2] + Stop1->Stop2->sing[4]
    } is unsat
    isWeighted: isTown for {
        Stop = Stop0 + Stop1
        connections = Stop0->Stop1->none + Stop1->Stop0->none
    } is unsat
    isIrreflexive: isTown for {
        Stop = Stop0 + Stop1
        connections = Stop0->Stop1->sing[2] + Stop1->Stop0->sing[2] + Stop0->Stop0->sing[1]
    } is unsat
    consistentWeight: isTown for {
        Stop = Stop0 + Stop1
        connections = Stop0->Stop1->sing[2] + Stop1->Stop0->sing[4]
    } is unsat
    positiveDistances: isTown for {
        Stop = Stop0 + Stop1
        connections = Stop0->Stop1->sing[-2] + Stop1->Stop0->sing[-2]
    } is unsat
}

example noStopsOK is isTown for {
    Stop = none
    connections = none->none->none
}

example oneStopOK is isTown for {
    Stop = Stop0
    connections = none->none->none
}

example smallTown is isTown for {
    Stop = Stop0 + Stop1
    connections = Stop0->Stop1->sing[2] + Stop1->Stop0->sing[2]
}






-- test validRoutes

-- no stops, empty route
example validRoutesTest1 is { validRoutes } for {
    Stop = none
    connections = none
    Route = Route0
    path = none
}

-- one stop, no connections
example validRoutesTest2 is { not validRoutes } for {
    Stop = Stop0
    connections = none
    Route = Route0
    path = Route0->Stop0->Stop0
}

-- two stops, empty route
example validRoutesTest3 is { validRoutes } for {
    Stop = Stop0 + Stop1
    connections = Stop0->Stop1->sing[1] + Stop1->Stop0->sing[2]
    Route = Route0
    path = none
}

-- Route0 is valid, Route1 is not
example validRoutesTest4 is { not validRoutes } for {
    Stop = Stop0 + Stop1 + Stop2
    connections = Stop0->Stop1->sing[1] + Stop1->Stop0->sing[1] + Stop0->Stop2->sing[3]
    Route = Route0 + Route1
    path = Route0->Stop0->Stop1 + Route0->Stop1->Stop0 + Route1->Stop2->Stop1
}





-- test isLine

-- empty path (not a line, since lines must have at least two stops)
example isLineTest1 is { not isLine[Route.path] } for {
    Route = Route0
    path = none
}

-- single-stop path (not a line, since lines must have at least two stops)
example isLineTest2 is { not isLine[Route.path] } for {
    Stop = Stop0
    Route = Route0
    path = Route0->Stop0->Stop0
}

-- two-stop line
example isLineTest3 is { isLine[Route.path] } for {
    Stop = Stop0 + Stop1
    Route = Route0
    path = Route0->Stop0->Stop1 + Route0->Stop1->Stop0
}

-- many-stop line, doesn't span all the stops which is fine
example isLineTest4 is { isLine[Route.path] } for {
    Stop = Stop0 + Stop1 + Stop2 + Stop3 + Stop4
    Route = Route0
    path = Route0->Stop0->Stop1 + Route0->Stop1->Stop0 +
           Route0->Stop1->Stop2 + Route0->Stop2->Stop1 +
           Route0->Stop2->Stop3 + Route0->Stop3->Stop2
}

-- non-line (asymmetric)
example isLineTest5 is { not isLine[Route.path] } for {
    Stop = Stop0 + Stop1
    Route = Route0
    path = Route0->Stop0->Stop1
}

-- non-line (branching)
example isLineTest6 is { not isLine[Route.path] } for {
    Stop = Stop0 + Stop1 + Stop2 + Stop3
    Route = Route0
    path = Route0->Stop0->(Stop1 + Stop2 + Stop3) + Route0->(Stop1 + Stop2 + Stop3)->Stop0
}

-- non-line (two-way circular loop, so has no endpoints)
example isLineTest7 is { not isLine[Route.path] } for {
    Stop = Stop0 + Stop1 + Stop2 + Stop3
    Route = Route0
    path = Route0->Stop0->Stop1 + Route0->Stop1->Stop0 +
           Route0->Stop1->Stop2 + Route0->Stop2->Stop1 +
           Route0->Stop2->Stop3 + Route0->Stop3->Stop2 +
           Route0->Stop3->Stop0 + Route0->Stop0->Stop3
}

-- non-line (disconnected, too many endpoints)
example isLineTest8 is { not isLine[Route.path] } for {
    Stop = Stop0 + Stop1 + Stop2 + Stop3 + Stop4
    Route = Route0
    path = Route0->Stop0->Stop1 + Route0->Stop1->Stop0 +
           Route0->Stop1->Stop2 + Route0->Stop2->Stop1 +
           Route0->Stop3->Stop4 + Route0->Stop4->Stop3
}

-- non-line (correct number of endpoints, but disconnected)
example isLineTest9 is { not isLine[Route.path] } for {
    Stop = Stop0 + Stop1 + Stop2 + Stop3
    Route = Route0
    path = Route0->(Stop0 + Stop1)->(Stop0 + Stop1) +
           Route0->Stop2->Stop3 + Route0->Stop3->Stop2
}


-- test validStopPaths

test expect {
    pathNotInSubwayRoute: {validStopPaths and isTown} for {
        Stop = Stop0 + Stop1 + Stop2
        connections = Stop0->Stop1->sing[1] + Stop1->Stop0->sing[1] + 
                      Stop1->Stop2->sing[2] + Stop2->Stop1->sing[2]

        Route = Route0
        path = Route0->Stop0->Stop1
        
        StopPath = SP0
        stop1 = SP0->Stop0
        stop2 = SP0->Stop2
        route = SP0->Stop0->Stop1 + SP0->Stop1->Stop2
    } is unsat
    stop2Unreachable: {validStopPaths and isTown} for {
        Stop = Stop0 + Stop1 + Stop2
        connections = Stop0->Stop1->sing[1] + Stop1->Stop0->sing[1] + 
                      Stop1->Stop2->sing[2] + Stop2->Stop1->sing[2]

        Route = Route0
        path = Route0->Stop0->Stop1
        
        StopPath = SP0
        stop1 = SP0->Stop0
        stop2 = SP0->Stop2
        route = SP0->Stop0->Stop1
    } is unsat
    backwardsPath: {validStopPaths and isTown} for {
        Stop = Stop0 + Stop1
        connections = Stop0->Stop1->sing[1] + Stop1->Stop0->sing[1]

        Route = Route0
        path = Route0->Stop0->Stop1
        
        StopPath = SP0
        stop1 = SP0->Stop1
        stop2 = SP0->Stop0
        route = SP0->Stop1->Stop0
    } is unsat
    wrongDistance: {validStopPaths and isTown} for {
        Stop = Stop0 + Stop1
        connections = Stop0->Stop1->sing[1] + Stop1->Stop0->sing[1]

        Route = Route0
        path = Route0->Stop0->Stop1
        
        StopPath = SP0
        stop1 = SP0->Stop0
        stop2 = SP0->Stop1
        route = SP0->Stop0->Stop1
        dist = SP0->sing[5]
    } is unsat
    countDuplicateDistances: {validStopPaths and isTown} for {
        Stop = Stop0 + Stop1 + Stop2
        connections = Stop0->Stop1->sing[1] + Stop1->Stop0->sing[1] + 
                      Stop1->Stop2->sing[1] + Stop2->Stop1->sing[1]

        Route = Route0
        path = Route0->Stop0->Stop1 + Route0->Stop1->Stop2
        
        StopPath = SP0
        stop1 = SP0->Stop0
        stop2 = SP0->Stop2
        route = SP0->Stop0->Stop1 + SP0->Stop1->Stop2
        dist = SP0->sing[1]
    } is unsat
}

example smallStopPath is {validStopPaths and isTown} for {
    Stop = Stop0 + Stop1
    connections = Stop0->Stop1->sing[1] + Stop1->Stop0->sing[1]

    Route = Route0
    path = Route0->Stop0->Stop1
    
    StopPath = SP0
    stop1 = SP0->Stop0
    stop2 = SP0->Stop1
    route = SP0->Stop0->Stop1
    dist = SP0->sing[1]
}

example extraInfoStopPath is {validStopPaths and isTown} for {
    Stop = Stop0 + Stop1 + Stop2
    connections = Stop0->Stop1->sing[1] + Stop1->Stop0->sing[1] + 
                  Stop1->Stop2->sing[2] + Stop2->Stop1->sing[2]

    Route = Route0
    path = Route0->Stop0->Stop1 + Route0->Stop1->Stop2 + Route0->Stop2->Stop1
    
    StopPath = SP0
    stop1 = SP0->Stop0
    stop2 = SP0->Stop1
    route = SP0->Stop0->Stop1 + SP0->Stop2->Stop1
    dist = SP0->sing[3]
}

example countDuplicateDistances2 is {validStopPaths and isTown} for {
    Stop = Stop0 + Stop1 + Stop2
    connections = Stop0->Stop1->sing[1] + Stop1->Stop0->sing[1] + 
                  Stop1->Stop2->sing[1] + Stop2->Stop1->sing[1]

    Route = Route0
    path = Route0->Stop0->Stop1 + Route0->Stop1->Stop2
    
    StopPath = SP0
    stop1 = SP0->Stop0
    stop2 = SP0->Stop2
    route = SP0->Stop0->Stop1 + SP0->Stop1->Stop2
    dist = SP0->sing[2]
}

-- test all together
*/