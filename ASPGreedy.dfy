datatype Activity = Pair(actStart:int, actEnd:int)

predicate sortedByActEnd(s: seq<Activity>)
    decreases s
{
   0 < |s| ==> (forall i :: 0 < i < |s| ==> s[0].actEnd <= s[i].actEnd) &&
               sortedByActEnd(s[1..])
}

// TODO de terminat + varianta iterativa
// method ASPGreedyMb(activities:seq<Activity>) returns (takenActivities:set<Activity>)
//     decreases |activities|
//     requires |activities| >= 1
//     requires sortedByActEnd(activities)
//     ensures |takenActivities| > 0
//     ensures |takenActivities| > 0 ==> disjointActivitiesSet(takenActivities)
// {
//     if (|activities| <= 1) 
//     {
//         if (|takenActivities| == 0 )
//         {
//             takenActivities := {activities[0]};
//         }
//         else if (canBeTaken(takenActivities, activities[0]))
//             {
//                 takenActivities := takenActivities + {activities[0]};
//             }
//     }
//     else 
//     {
//         takenActivities := takenActivities + {activities[0]};
//         if activities[1].actStart >= activities[0].actEnd
//         {
//             var nextActivities := ASPGreedyMb([activities[1]] + activities[2..]);
//             takenActivities := takenActivities + {activities[1]} + nextActivities;
//         }
//     }
// }

// predicate nonOverlappingActivities(s:set<Activity>)
// {
//     |s| > 0 ==> forall i, j :: 0 <= i < j < |s| ==> s[i].actEnd <= s[j].actStart
// }

predicate canBeTaken(takenActivities:set<Activity>, act:Activity)
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

predicate differentActivities(act1:Activity, act2:Activity)
{
    act1.actStart != act2.actStart && act1.actEnd != act2.actEnd
}

// predicat pentru overlapping intre 2 activitati
predicate overlappingActivities(act1:Activity, act2:Activity)
{
    act1.actStart < act2.actEnd && differentActivities(act1, act2)
}
// predicat care primeste un set si spune daca toate sunt disjuncte -- postcond si invariant de buncla
predicate disjointActivitiesSet(activities:set<Activity>)
{
    forall act1 :: act1 in activities ==> forall act2 :: act2 in activities ==> !overlappingActivities(act1, act2)
}

method ASPGreedy(activities:array<Activity>) returns (takenActivities:set<Activity>) // sa nu mai intoarca notTaken, intoarce o multime disjuncta de activitati
    requires activities.Length > 0
    requires sortedByActEnd(activities[0..activities.Length]);
    ensures nonOverlappingActivitiesTaken(activities, takenActivities);
    ensures disjointActivitiesSet(takenActivities)
{
    takenActivities := {activities[0]};
    var lastTaken := activities[0];
    var index := 1;
    while index < activities.Length
        decreases activities.Length - index
        invariant 0 < index <= activities.Length
        //invariant index < activities.Length ==> activities[index] !in takenActivities
        invariant lastTaken in takenActivities
        //invariant forall i :: 0 <= i < index ==> (activities[i] !in takenActivities ==> !canBeTaken(takenActivities, activities[i]))
        invariant nonOverlappingActivitiesTaken(activities, takenActivities)
        invariant disjointActivitiesSet(takenActivities)
    {
        if activities[index].actStart >= lastTaken.actEnd
        {
            takenActivities := takenActivities + {activities[index]};
            lastTaken := activities[index];
        }
        index := index + 1;
    }
}