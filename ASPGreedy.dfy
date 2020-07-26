datatype Activity = Pair(actStart:int, actEnd:int)

predicate sortedByActEnd(s: seq<Activity>)
    decreases s
{
   0 < |s| ==> (forall i :: 0 < i < |s| ==> s[0].actEnd <= s[i].actEnd) &&
               sortedByActEnd(s[1..])
}

//TODO de terminat, de adugat un parametru care acumuleaza activitatile deja alese(initial lista vida)
function method ASPGreedyRec(activities:seq<Activity>, accumulator:set<Activity>) : set<Activity>   //as avea nevoie de ajutor/lamuriri
                                                                                                //deoarece nu imi pot da seama de cu nu se
                                                                                                //valideaza postconditiile
    decreases |activities|
    requires |activities| >= 1
    requires sortedByActEnd(activities)
    ensures |ASPGreedyRec(activities, {})| > 0  //failure to decrease termination measure 
                                                //-- tind sa cred ca se intampla atunci cand |activities| = 1
    ensures disjointActivitiesSet(accumulator)  //might not hold 
                                                //-- parametrul <accumulator> functioneaza aproximativ identic cu 
                                                //<takenActivities> din varianta iterativa
    ensures disjointActivitiesSet(ASPGreedyRec(activities, {})) //might not hold 
                                                                //-- tind sa cred ca e din cauza faptului ca nu poate 
                                                                //dovedi ca parametrul <accumulator> este disjointActivitiesSet
{
    if (|activities| == 1) 
        then if (canBeTaken(accumulator, activities[0]))
            then accumulator + {activities[0]}
            else accumulator
        else if (canBeTaken(accumulator, activities[0]))
            then ASPGreedyRec(activities[1..], accumulator + {activities[0]})
            else ASPGreedyRec(activities[1..], accumulator)
}

predicate method canBeTaken(takenActivities:set<Activity>, act:Activity)    //Am adugat <|takenActivities| == 0> pentru 
                                                                            //tratarea situatie cand fac prima verificare 
                                                                            //in algoritmul recursiv
{
    |takenActivities| == 0 || forall act1 :: act1 in takenActivities ==> !overlappingActivities(act, act1)
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
predicate method disjointActivitiesSet(activities:set<Activity>)    //Am adugat <|takenActivities| == 0> pentru 
                                                                    //tratarea situatie cand fac prima verificare 
                                                                    //in algoritmul recursiv
{
    |activities| == 0 || forall act1 :: act1 in activities ==> forall act2 :: act2 in activities ==> !overlappingActivities(act1, act2)
}

// verifica daca o solutie este optima

//metoda ce genereaza toate solutiile posibile -- as avea nevoie de o functie care sa poata fi apelata intr-un predicat
                                                //dar inca nu am reusit sa fac o implementare functionala
method allSolutions(activities:seq<Activity>) returns (solutions:set<set<Activity>>)
{
    solutions := {};
    var len := |activities|;
    var i := 0;
    while (i < len)
        decreases len - i
        invariant forall solutie :: solutie in solutions ==> isSolution(activities, solutie)
    {
        var sol := {activities[i]};
        var j := i+1;
        while (j < len)
            decreases len - j
            invariant isSolution(activities, sol)
        {
            if(canBeTaken(sol, activities[j]))
            {
                sol := sol + {activities[j]};
            }
            j := j + 1;
        }
        solutions := solutions + {sol};
        i := i + 1;
    }
}

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
// TODO de gasit o metoda de a accesa toate solutiile posibile in predicat (functia pentru <allSolutions>)!!!
predicate optimalSolution(activities: seq<Activity>, takenActivities: set<Activity>)
    requires |activities| > 0
{
    isSolution(activities, takenActivities) //&& forall sol :: sol in allSolutions(activities) ==> castig(takenActivities) >= castig(sol)
}

//TODO de gasit predicate/postcond/invariant care sa determine daca solutia este optima!
method ASPGreedy(activities:array<Activity>) returns (takenActivities:set<Activity>)    //voi modifica <activities> sa fie de tipul <seq<Activity>>
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
        invariant optimalSolution(activities[..index], takenActivities) //verific daca este o solutie optima pentru subproblema
                                                                        //generata(?) de primele <index> activitati, este necesar?
    {
        if canBeTaken(takenActivities, activities[index])
        {
            takenActivities := takenActivities + {activities[index]};
            lastTaken := activities[index];
        }
        index := index + 1;
    }
}