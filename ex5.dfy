// 5.Given an array of characters, it returns the index of the first ‘e’. [‘c’,’h’,’e’,’e’,’s’,’e’] -> 2


method E(a:array<char>) returns(p:int)
ensures -1 <= p < a.Length
ensures 
if 'e' in a[..] then
    0 <= p < a.Length && a[p] == 'e' && forall x :: 0<=x<p ==> a[x] != 'e' // ordering matters
    else
    p == -1 

{
    p := -1;
    var i := 0;

    while(i < a.Length) 
    invariant 0<= i <= a.Length
    invariant forall x :: 0<=x<i ==> a[x] != 'e';
    {
        if(a[i] == 'e'){
            p := i;
            break;
        }
        i := i + 1;
    }

    // assert 
    // if 'e' in a[..] then
    // p == i && a[p] == 'e' && a[i] == 'e'
    // else
    // p == -1 && i == a.Length;

}

method Main(){
    var a := new char[6]['c','h','e','e','s','e'];

    var p := E(a);
    print p;
    assert p == 2;

}

