datatype Activity = Pair(actStart:int, actEnd:int)

predicate sortedByActEnd(s: seq<Activity>)
    decreases s
{
   0 < |s| ==> (forall i :: 0 < i < |s| ==> s[0].actEnd <= s[i].actEnd) &&
               sortedByActEnd(s[1..])
}

predicate method canBeTaken(takenActivities:set<Activity>, act:Activity)
{
    |takenActivities| == 0 || forall act1 :: act1 in takenActivities ==> !overlappingActivities(act, act1)
}

predicate nonOverlappingActivitiesTaken(activities:seq<Activity>, taken:set<Activity>)
{
    |activities| > 0 ==> forall i :: 0 <= i < |activities| ==>
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
    |activities| == 0 || forall act1 :: act1 in activities ==> forall act2 :: act2 in activities ==> !overlappingActivities(act1, act2)
}

// verifica daca o solutie este optima

// predicat isSolution
predicate isSolution(activities:seq<Activity>, takenActivities:set<Activity>)
{
    disjointActivitiesSet(takenActivities) && forall act :: act in takenActivities ==> act in activities
}

// functie castig, petru o solutie intoarce cat castig din aceasta(nr. de act)
function castig(solution:set<Activity>):int
{
    |solution|
}

// o solutie e optima daca isSolution si daca orice alta sol are castig mai mic
predicate optimalSolution(activities: seq<Activity>, takenActivities: set<Activity>)
    requires |activities| >= 0
{
    isSolution(activities, takenActivities) && forall sol :: isSolution(activities, sol)  ==> castig(takenActivities) >= castig(sol)
}

//

lemma helper1(activities:seq<Activity>, takenActivities:set<Activity>, index:int)
    requires 0 <= index < |activities|;
    requires sortedByActEnd(activities);
    requires optimalSolution(activities[..index], takenActivities);
    requires canBeTaken(takenActivities, activities[index]);
    ensures optimalSolution(activities[..index+1], takenActivities+{activities[index]});
{
    //TODO de demonstrat!
}

//TODO lema helper2 cand e adevarat !canBeTaken
//TODO tutorial leme!

//TODO de gasit predicate/postcond/invariant care sa determine daca solutia este optima!
method ASPGreedy(activities:seq<Activity>) returns (takenActivities:set<Activity>)    //voi modifica <activities> sa fie de tipul <seq<Activity>>
    requires |activities| > 0
    requires sortedByActEnd(activities);
    ensures nonOverlappingActivitiesTaken(activities, takenActivities);
    ensures disjointActivitiesSet(takenActivities)
    ensures optimalSolution(activities, takenActivities)   //presupun ca nu se valideaza deoarece nu poate asigura proprietatea de substructura optima?
{
    var seqLen := |activities|;
    takenActivities := {activities[0]};
    var lastTaken := activities[0];
    var index := 1;
    var lastIndex := 1;
    // assert activities[0] in activities[..1];
    // assert forall act :: act in {activities[0]} ==> act == activities[0];
    // assert forall act :: act in {activities[0]} ==> act == activities[0] && act in activities[..1];
    // assert disjointActivitiesSet({activities[0]});
    // assert forall act :: act in {activities[0]} ==> act in activities[..1];
    // assert isSolution(activities[..1], {activities[0]});
    assert forall sol :: (disjointActivitiesSet(sol) && forall act :: act in sol ==> act in activities[..1])  ==> sol == {activities[0]} || sol == {};
    // assert forall sol :: (disjointActivitiesSet(sol) && forall act :: act in sol ==> act in activities[..1])  ==> castig({activities[0]}) >= castig(sol);
    // assert forall sol :: isSolution(activities[..1], sol)  ==> castig({activities[0]}) >= castig(sol);
    // assert optimalSolution(activities[..1], {activities[0]});
    assert optimalSolution(activities[..lastIndex], takenActivities);
    while index < seqLen
        decreases seqLen - index
        invariant index == lastIndex
        invariant 0 < index <= seqLen
        invariant 0 < lastIndex <= seqLen
        invariant lastTaken in takenActivities
        invariant forall i :: 0 <= i < index ==> (activities[i] !in takenActivities ==> !canBeTaken(takenActivities, activities[i]))
        invariant nonOverlappingActivitiesTaken(activities, takenActivities)
        invariant disjointActivitiesSet(takenActivities)
        invariant optimalSolution(activities[..lastIndex], takenActivities)   //might not be maintained by the loop
                                                                                    //-- de ce nu poate asigura proprietatea de substructura optima?
    {
        if canBeTaken(takenActivities, activities[index])
        {
            //assert optimalSolution(activities[..index], takenActivities);
            helper1(activities, takenActivities, index);
            takenActivities := takenActivities + {activities[index]};
            lastTaken := activities[index];
            assert optimalSolution(activities[..lastIndex+1], takenActivities);
        }
        lastIndex := index + 1;
        index := index + 1;
        assert optimalSolution(activities[..lastIndex], takenActivities);
    }
    assert optimalSolution(activities[..lastIndex], takenActivities);
}

//TODO de terminat, de adugat un parametru care acumuleaza activitatile deja alese(initial lista vida)
method ASPGreedyRec(activities:seq<Activity>, accumulator:set<Activity>) returns (takenActivities:set<Activity>)
    decreases |activities|
    requires |activities| >= 1
    requires sortedByActEnd(activities)
    ensures |takenActivities| > 0
    requires disjointActivitiesSet(accumulator)
    ensures disjointActivitiesSet(takenActivities)
    ensures optimalSolution(activities, takenActivities)   //verificat de ce crapa?!
    //--cum pot asigura ca la prima iteratie se intra cu <accumulator={}>?
{
    if (|activities| == 1) 
    {
        if (canBeTaken(accumulator, activities[0]))
        {
            return accumulator + {activities[0]};
        }
        else
        {
            return accumulator;
        }
    }
    else 
    {
        if (canBeTaken(accumulator, activities[0]))
        {
            assert |activities[1..]|<|activities|;
            var temp := ASPGreedyRec(activities[1..], accumulator + {activities[0]});
            return temp;
        }
        else
        {
            assert |activities[1..]|<|activities|;
            var temp := ASPGreedyRec(activities[1..], accumulator);
            return temp;
        }
    }
}