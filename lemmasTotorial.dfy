//Searching for Zero
lemma SkippingLemma(a : array?<int>, j : int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   requires 0 <= j < a.Length
   ensures forall i :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0
{
   var i := j;
   while i < j + a[j] && i < a.Length
      decreases j + a[j] - i
      invariant i < a.Length ==> a[j] - (i-j) <= a[i]
      invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0
   {
      i := i + 1;
   }
}
method FindZero(a: array?<int>) returns (index: int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
{
   index := 0;
   while index < a.Length
      decreases a.Length - index
      invariant 0 <= index
      invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0
   {
      if a[index] == 0 { return; }
      SkippingLemma(a, index);
      index := index + a[index];
   }
   index := -1;
}

//Counting
lemma DistributiveLemma(a: seq<bool>, b: seq<bool>)
   decreases a, b
   ensures count(a + b) == count(a) + count(b)
{
   if a == []
   {
      assert a + b == b;
   }
   else
   {
      DistributiveLemma(a[1..], b);
      assert a + b == [a[0]] + (a[1..] + b);
   }
}
function count(a: seq<bool>): nat
   decreases a
{
   if |a| == 0 then 0 else
   (if a[0] then 1 else 0) + count(a[1..])
}