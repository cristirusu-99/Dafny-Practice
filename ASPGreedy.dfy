datatype Activity = Pair(actStart:int, actEnd:int)

predicate sortedByActEnd(s: seq<Activity>)
    decreases s
{
   0 < |s| ==> (forall i :: 0 < i < |s| ==> s[0].actEnd <= s[i].actEnd) &&
               sortedByActEnd(s[1..])
}

predicate distinctActivitiesSeq(s: seq<Activity>)
    decreases s
{
    forall i :: 0 <= i < |s| - 1 ==> forall j :: i < j < |s| ==> differentActivities(s[i], s[j])
}

predicate method canBeTaken(takenActivities:set<Activity>, act:Activity)
{
    act !in takenActivities && (|takenActivities| == 0 || forall act1 :: act1 in takenActivities ==> !overlappingActivities(act, act1))// && differentActivities(act, act1)
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

// review later?
// function maxCastig(solutions:seq<set<Activity>>):int
//     decreases solutions
//     requires |solutions| > 0
// {
//     if |solutions| == 1
//     then |solutions[0]|
//     else
//         if |solutions[0]| > maxCastig(solutions[1..])
//         then |solutions[0]|
//         else maxCastig(solutions[1..])
// }

// lemma testMaxCastig(activities:seq<Activity>) 
// {
//     var sols:seq<set<Activity>> :| forall sol :: isSolution(activities, sol) ==> sol in sols;
//     assert forall sol :: isSolution(activities, sol) ==> castig(sol) <= maxCastig(sols);

// }

// o solutie e optima daca isSolution si daca orice alta sol are castig mai mic
predicate optimalSolution(activities: seq<Activity>, takenActivities: set<Activity>)
    requires |activities| >= 0
{
    isSolution(activities, takenActivities) && forall sol :: isSolution(activities, sol)  ==> castig(takenActivities) >= castig(sol)
}

//

lemma leadsToOptimal(activities:seq<Activity>, takenActivities:set<Activity>, index:int)
    requires |activities| > 0
    requires 0 <= index < |activities|;
    requires sortedByActEnd(activities);
    requires optimalSolution(activities[..index], takenActivities);
    requires canBeTaken(takenActivities, activities[index]);
    ensures optimalSolution(activities[..index+1], takenActivities+{activities[index]});
{
    //TODO de demonstrat!
    //assert forall sol :: (disjointActivitiesSet(sol) && forall act :: act in sol ==> act in activities[..2])  ==> sol == {activities[0], activities[1]} || sol == {activities[0]} || sol == {activities[1]} || sol == {};
    assert isSolution(activities[..index+1], takenActivities+{activities[index]});
    assert forall sol :: isSolution(activities[..index], sol)  ==> |takenActivities| >= |sol|;
    // assert |{activities[index]}| == 1;
    // assert activities[index] !in takenActivities;
    assert |takenActivities+{activities[index]}| == |takenActivities| + 1;
    assert optimalSolution(activities[..index], takenActivities);
    assert forall sol :: isSolution(activities[..index], sol) ==> |sol| <= |takenActivities|;
    assert forall sol :: isSolution(activities[..index+1], sol) && activities[index] in sol ==> isSolution(activities[..index], sol - {activities[index]});
    assert forall sol :: isSolution(activities[..index+1], sol) ==> activities[index] in sol || activities[index] !in sol;
    assert forall sol :: isSolution(activities[..index+1], sol) ==> |sol| <= |takenActivities| + 1;
    assert forall sol :: isSolution(activities[..index+1], sol) ==> |takenActivities+{activities[index]}| >= |sol|;
}

lemma notLeadingToOptimal(activities:seq<Activity>, takenActivities:set<Activity>, index:int)
    requires |activities| > 1
    requires 0 <= index < |activities|;
    requires sortedByActEnd(activities);
    requires optimalSolution(activities[..index], takenActivities);
    requires activities[index] !in takenActivities;
    requires !canBeTaken(takenActivities, activities[index]);
    ensures optimalSolution(activities[..index+1], takenActivities);
{
    //TODO de demonstrat!
    assert isSolution(activities[..index+1], takenActivities);
    assert forall sol :: isSolution(activities[..index], sol)  ==> |takenActivities| >= |sol|;
    assert activities[index] !in takenActivities;
    assert !(forall act :: act in takenActivities ==> !overlappingActivities(act, activities[index]));
    assert !disjointActivitiesSet(takenActivities+{activities[index]});
    assert !isSolution(activities[..index+1], takenActivities+{activities[index]});
    assert forall solp :: optimalSolution(activities[..index], solp) ==> |takenActivities| == |solp|;
    // as fi luat o sol' opt pt activities[..index+1] care cont activities[index] ==> ar fi fost la fel de buna ca o sol ca o sol opt pt activities[..index]
    assert forall solp :: optimalSolution(activities[..index+1], solp) && activities[index] in solp ==> forall sol :: optimalSolution(activities[..index], sol) ==> |sol| >= |solp|;
    assert forall solp :: optimalSolution(activities[..index+1], solp) && activities[index] in solp && forall sol :: optimalSolution(activities[..index], sol) ==> |sol| >= |solp|;
    assert forall sol :: (optimalSolution(activities[..index+1], sol) && activities[index] in sol) ==> |takenActivities| >= |sol|;
}

//TODO lema helper2 cand e adevarat !canBeTaken
//TODO tutorial leme!

//TODO de gasit predicate/postcond/invariant care sa determine daca solutia este optima!
method ASPGreedy(activities:seq<Activity>) returns (takenActivities:set<Activity>)    //voi modifica <activities> sa fie de tipul <seq<Activity>>
    requires |activities| > 0
    requires sortedByActEnd(activities);
    requires distinctActivitiesSeq(activities);
    ensures nonOverlappingActivitiesTaken(activities, takenActivities);
    ensures disjointActivitiesSet(takenActivities);
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
            // assert optimalSolution(activities[..index], takenActivities);
            leadsToOptimal(activities, takenActivities, index);
            takenActivities := takenActivities + {activities[index]};
            lastTaken := activities[index];
            lastIndex := index + 1;
            index := index + 1;
            assert optimalSolution(activities[..lastIndex], takenActivities);
        }
        else
        {
            notLeadingToOptimal(activities, takenActivities, index);
            lastIndex := index + 1;
            index := index + 1;
            assert optimalSolution(activities[..lastIndex], takenActivities);
        }
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

method ASPGreedyRecp(activities:seq<Activity>, accumulator:set<Activity>, index:int) returns (takenActivities:set<Activity>)
    decreases |activities| - index
    requires |activities| >= 1
    requires 0 <= index < |activities|
    requires sortedByActEnd(activities)
    requires distinctActivitiesSeq(activities)
    ensures |takenActivities| > 0
    requires disjointActivitiesSet(accumulator)
    requires optimalSolution(activities[..index], accumulator)
    ensures disjointActivitiesSet(takenActivities)
    ensures optimalSolution(activities, takenActivities)   //verificat de ce crapa?!
    //--cum pot asigura ca la prima iteratie se intra cu <accumulator={}>?
{
    if (index == |activities| - 1) 
    {
        if (canBeTaken(accumulator, activities[index]))
        {
            leadsToOptimal(activities, accumulator, index);
            return accumulator + {activities[index]};
        }
        else
        {
            notLeadingToOptimal(activities, accumulator, index);
            return accumulator;
        }
    }
    else 
        // if (index < |activities| - 1)
        {
            if (canBeTaken(accumulator, activities[index]))
            {
                leadsToOptimal(activities, accumulator, index);
                var temp := ASPGreedyRecp(activities, accumulator + {activities[index]}, index + 1);
                return temp;
            }
            else
            {
                notLeadingToOptimal(activities, accumulator, index);
                var temp := ASPGreedyRecp(activities, accumulator, index + 1);
                return temp;
            }
        }
}