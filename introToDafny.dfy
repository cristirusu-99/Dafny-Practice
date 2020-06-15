// Dafny Intro:

//Ex. 1:
method Max(a: int, b:int) returns (c: int)
  ensures a > b ==> (a == c && b < c) 
  ensures a < b ==> (b == c && a < c) 
  ensures a == b ==>  a == b == c
{
  if a < b
    {
      return b;
    }
  else
    {
      return a;
    }
}

method Testing1()
{
  var m1 := Max(2, 3);
  var m2 := Max(3, 3);
  var m3 := Max(-1, -2);
  assert m1 == 3;
  assert m2 == 3;
  assert m3 == -1;
}

//Ex. 2:
method Abs2(x: int) returns (y: int)
   requires x < 0
   ensures 0 <= y
   ensures 0 <= x ==> x == y
   ensures x < 0 ==> y == -x
{
   return -x;
}

//Ex. 3:
method Abs3_1(x: int) returns (y: int)
   requires x == -1
   // Don't change the postconditions.
   ensures 0 <= y
   ensures 0 <= x ==> x == y
   ensures x < 0 ==> y == -x
{
  y:= x + 2;
}
// method Abs3_2(x: int) returns (y: int)
//    requires x == -0.5 //(mathematically speaking, but x must be int)
//    /*stdin.dfy(11,14): Error: arguments must have comparable types (got int and real)
//     1 resolution/type errors detected in stdin.dfy*/
//    // Don't change the postconditions.
//    ensures 0 <= y
//    ensures 0 <= x ==> x == y
//    ensures x < 0 ==> y == -x
// {
//   y:= x + 1;
// }

//Ex. 4:
function max4(a: int, b: int): int 
{
   if a < b then b else a
}
method Testing4() {
  assert max4(2, 3) == 3;
  assert max4(3, 3) == 3;
  assert max4(-1, -2) == -1;
}

//Ex. 5:
function method max5(a: int, b: int): int 
{
  if a < b then b else a
}
method Testing5() {
  var m1 := max5(2, 3);
  var m2 := max5(3, 3);
  var m3 := max5(-1, -2);
  assert m1 == 3;
  assert m2 == 3;
  assert m3 == -1;
}

//Ex. 6:
//a)
function abs6_a(x: int): int
{
   if x < 0 then -x else x
}
method Abs(x: int) returns (y: int)
  ensures 0 <= y //not sure this is needed anymore
  ensures abs6_a(x) == y
{
   // Then change this body to also use abs.
   if x < 0
     { return -x; }
   else
     { return x; }
}
//b)
function method abs6_b(x: int): int
{
   if x < 0 then -x else x
}
method Abs6(x: int) returns (y: int)
  ensures 0 <= y //not sure this is needed anymore
  ensures abs6_b(x) == y
{
   return abs6_b(x);
}

//Ex. 7:
// method m7(n: nat)
// {
//    var i: int := 0;
//    while i < n
//       invariant 0 <= i <= n+2  // Change this. What happens?
//    {
//       i := i + 1;
//    }
//    assert i == n; //Error: assertion violation
// }

//Ex. 8:
method m8(n: nat)
{
   var i: int := 0;
   while i != n  // Change this. What happens?
      invariant 0 <= i <= n
      decreases n - i
   {
      i := i + 1;
   }
   assert i == n; // It still holds because the invariant still holds,
                  // i starts as positive(0) and keeps being incremented
                  // until i == n. Seeing i as a linear matematical function,
                  // since its monotony doesn't change and it starts from 0, 
                  // i != n is enough for a loop guard in this case, n being
                  // a natural number impling that 0 <= n.
}

//Ex. 9:
function fib109(n: nat): nat
    decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib109(n - 1) + fib109(n - 2)
}
method ComputeFib109(n: nat) returns (b: nat)
   ensures b == fib109(n)  // Do not change this postcondition
{
   // Change the method body to instead use c as described.
   // You will need to change both the initialization and the loop.
   if n == 0 { return 0; }
   var i: int := 1;
       b := 1;
   var c := 1;
   while i < n
      invariant 0 < i <= n
      invariant b == fib109(i)
      invariant c == fib109(i + 1)
      decreases n - i
   {
      b, c := c, b + c;
      i := i + 1;
   }
}

//Ex. 10:
function fib10(n: nat): nat
    decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib10(n - 1) + fib10(n - 2)
}
method ComputeFib10(n: nat) returns (b: nat)
   ensures b == fib10(n)
{
   var i: int := 0;
   var a := 1;
       b := 0;
   while i < n
      // Fill in the invariants here.
      invariant 0 <= i <= n
      invariant i == 0 ==> a == 1 && b == fib10(i)
      invariant i > 0 ==> a == fib10(i - 1) && b == fib10(i)
      decreases n - i
   {
      a, b := b, a + b;
      i := i + 1;
   }
}

// Ex. 11:
// method m11()
// {
//    var i, n := 0, 20;
//    while i != n
//    //Error: cannot prove termination; try supplying a decreases clause for the loop
//    {
//       i := i + 1;
//    }
// }


//Ex. 12:
method FindMax(a: array<int>) returns (i: int)
   // Annotate this method with pre- and postconditions
   // that ensure it behaves as described.
   requires 0 < a.Length
   ensures 0 <= i < a.Length
   ensures forall k: int :: 0 <= k < a.Length ==> a[k] <= a[i]
{
    i := 0;
    var max := a[0];
    var index := 0;
    while index < a.Length
        decreases a.Length - index
        invariant 0 <= index <= a.Length
        invariant index == 0 ==> i == index
        invariant index > 0 ==> 0 <= i < index
        invariant max == a[i]
        invariant forall k :: 0 <= k < index ==> a[k] <= a[i]
    {
        if max < a[index] 
        {
          max := a[index];
          i := index;
        }
        index := index + 1;
    }
    assert index == a.Length;
}

//Ex. 13:
predicate sorted13(a: array?<int>)
   requires a != null
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}

//Ex. 14:
predicate sorted14(a: array?<int>)
   reads a
{
    a != null && (forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k])
}

//Ex. 15:
method BinarySearch(a: array<int>, value: int) returns (index: int)
   requires 0 <= a.Length && sorted14(a)
   ensures 0 <= index ==> index < a.Length && a[index] == value
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
   var low, high := 0, a.Length;
   while low < high
        decreases high - low
      invariant 0 <= low <= high <= a.Length
      invariant forall i ::
         0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
   {
      var mid := (low + high) / 2;
      if a[mid] < value
      {
         low := mid + 1; //setting low to mid might stop the loop from progressing -> infinite loop
      }
      else if value < a[mid]
      {
         high := mid;    // setting high to (mid - 1) leads to the loop invariants not being respected 
                            // 1. might set high to -1 in the case if arrays of Length = 2
                            // 2. might cause the missing of some elements in the array.
      }
      else
      {
         return mid;
      }
   }
   return -1;
}