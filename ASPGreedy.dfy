datatype Activity = Pair(actStart:int, actEnd:int)

predicate sortedByActEnd(s: seq<Activity>)
    decreases s
{
   0 < |s| ==> (forall i :: 0 < i < |s| ==> s[0].actEnd <= s[i].actEnd) &&
               sortedByActEnd(s[1..])
}

//TODO de terminat
function method ASPGreedyMb(activities:seq<Activity>) : set<Activity> //returns (takenActivities:set<Activity>)
    decreases |activities|
    requires |activities| >= 1
    requires sortedByActEnd(activities)
    ensures |ASPGreedyMb(activities)| > 0
    ensures disjointActivitiesSet(ASPGreedyMb(activities))
{
    if (|activities| == 1) 
        then if (canBeTakenRec(activities[0], activities[1..]))
            then {activities[0]}
            else {}
        else if (canBeTakenRec(activities[0], activities[1..]))
            then {activities[0]} + ASPGreedyMb(activities[1..])
            else ASPGreedyMb(activities[1..])
}

predicate method canBeTakenRec(act:Activity, activities:seq<Activity>)
{
    true // de facut!!
}
predicate method canBeTaken(takenActivities:set<Activity>, act:Activity)
{
    forall act1 :: act1 in takenActivities ==> !overlappingActivities(act, act1)
}

predicate nonOverlappingActivitiesTaken(activities:array<Activity>, taken:set<Activity>)
    reads activities;
{
    activities.Length > 0 ==> forall i :: 0 <= i < activities.Length ==>
        (forall act :: act in taken ==> overlappingActivities(activities[i], act) ==>
            activities[i] !in taken)
}

predicate method differentActivities(act1:Activity, act2:Activity)
{
    act1.actStart != act2.actStart && act1.actEnd != act2.actEnd
}

// predicat pentru overlapping intre 2 activitati
predicate method overlappingActivities(act1:Activity, act2:Activity)
{
    (act1.actStart < act2.actEnd || act2.actStart < act1.actEnd) && differentActivities(act1, act2)
}
// predicat care primeste un set si spune daca toate sunt disjuncte -- postcond si invariant de buncla
predicate method disjointActivitiesSet(activities:set<Activity>)
{
    forall act1 :: act1 in activities ==> forall act2 :: act2 in activities ==> !overlappingActivities(act1, act2)
}

// verifica daca o solutie este optima
predicate method optimalSolution(activities: seq<Activity>, takenActivities: set<Activity>)
    requires |activities| > 0
{
    forall act :: (act in activities[1..] && act !in takenActivities) ==> !disjointActivitiesSet((takenActivities - {activities[0]}) + {act})
}

// verifica daca adaugarea unui element pastreaza optimalitatea unei solutii patiale
predicate method leadsToOptimal(activities: seq<Activity>, takenActivities: set<Activity>, act: Activity)
    requires |activities| > 0
{
    optimalSolution(activities, takenActivities+{act})
}
//TODO de gasit predicate/postcond/invariant care sa determine daca solutia este optima!
method ASPGreedy(activities:array<Activity>) returns (takenActivities:set<Activity>)
    requires activities.Length > 0
    requires sortedByActEnd(activities[0..activities.Length]);
    ensures nonOverlappingActivitiesTaken(activities, takenActivities);
    ensures disjointActivitiesSet(takenActivities)
    ensures optimalSolution(activities[0..], takenActivities)
{
    takenActivities := {activities[0]};
    var lastTaken := activities[0];
    var index := 1;
    while index < activities.Length
        decreases activities.Length - index
        invariant 0 < index <= activities.Length
        invariant lastTaken in takenActivities
        invariant forall i :: 0 <= i < index ==> (activities[i] !in takenActivities ==> !canBeTaken(takenActivities, activities[i]))
        invariant nonOverlappingActivitiesTaken(activities, takenActivities)
        invariant disjointActivitiesSet(takenActivities)
        invariant optimalSolution(activities[..index], takenActivities)
    {
        if canBeTaken(takenActivities, activities[index]) && leadsToOptimal(activities[..index], takenActivities, activities[index])
        {
            takenActivities := takenActivities + {activities[index]};
            lastTaken := activities[index];
        }
        index := index + 1;
    }
}