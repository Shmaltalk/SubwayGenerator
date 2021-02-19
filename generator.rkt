#lang forge "curiosity_modeling" "clU0kCu1da0mc0rN@gmail.com"




sig Stop {
    connections: set Stop->Int
}

sig Route {
    path: set Stop->Stop
}

pred isTown {
    -- connected

    -- undirected

    -- weighted

    -- irreflexive
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

run {isSubwaySystem} for exactly 2 Route, 4 Stop