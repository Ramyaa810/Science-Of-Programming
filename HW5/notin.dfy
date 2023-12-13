method notin(a: seq<int>) returns (r: int)
requires |a| >= 1
ensures (forall i : int :: (i >= 0) && (i < |a|) ==> a[i] != r)
{
    r := 0;
    var i := 0;
    var max := a[0];
    while (i < |a|)
    invariant 0 <= i && i <= |a|
    invariant forall j: int :: (j >= 0) && (j < i) ==> max <= a[j]
    {
        if(a[i] < max) {
           max := a[i];
        }
        i := i + 1;
    }
    r := max - 1;
}