#lang forge "curiosity_modeling" "075knkr5cf0ofmn1@gmail.com"


sig Stop {
    connections: set Stop->Int
}

sig Route {
    path: set Stop->Stop
}

pred isTown {
    -- connected
    all s: Stop | Stop in s.*(connections.Int)
    
    -- undirected
    ~(connections.Int) in (connections.Int)

    -- weighted (all stops must have some distance)
    --TODO consider if the weight needs to be the same for a->b and b->a
    (some connections) implies Stop.(Stop.connections) in Int

    -- any two stops have the same distance

    -- irreflexive
    no (connections.Int) & iden
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
    
    -- line should have two endpoints, each of which will be connected to only
    -- one other stop
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

run {isTown} for exactly 2 Stop


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
    /*consistentWeight: isTown for {
        Stop = Stop0 + Stop1
        connections = Stop0->Stop1->2 + Stop1->Stop0->4
    } is unsat*/ -- ???? yes or no
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
