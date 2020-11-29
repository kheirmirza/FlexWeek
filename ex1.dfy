// 1.Given an array of integers, it returns the sum. [1,3,3,2]->9
// Could not assert for exact value in this case
function SumR(a:seq<int>):int{
    if |a| == 0 then 0
    else a[0] + SumR(a[1..])
}

function sumTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else sumTo(a, n-1) + a[n-1]
}



method Sum(a:array<int>) returns(s:int)
ensures s == sumTo(a,a.Length)
{

    s := 0;
    var i := 0;

    while(i < a.Length)
    invariant 0 <= i <= a.Length
    invariant s == sumTo(a,i)
    // invariant s == SumR(a[..i-1]) // On entry it holds
    {
        s := s + a[i];
        i := i + 1;
    }

}

// method Checker(){
//     var a:= new int[][1,3,3,2];
//     var s := Sum(a);
//     assert s == 9;
// }

method Main() {
  var a: array<int> := new int[4];
  a[0] := 1;
  a[1] := 3;
  a[2] := 3;
  a[3] := 2;
  assert a[..] == [1,3,3,2];

  var s:= Sum(a);
  assert a[0] == 1 && a[1] == 3 && a[2] == 3 && a[3] == 2;
  assert s == sumTo(a, a.Length);
  print "\nThe sum of all elements in [1,3,3,2] is ";
  print s;
//   assert s == 9;
}