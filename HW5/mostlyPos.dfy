function numPos(a: seq<int>, i: int, j: int) : int
requires i >= 0 && j <= |a|
{
    if i >= j then 0
    else if a[j - 1] > 0 then 1 + numPos(a, i, j - 1) else numPos(a, i, j - 1)
}
method mostlyPos(a: seq<int>) returns (b: bool)
ensures (b <==> numPos(a, 0, |a|) > |a| / 2)
{
    var i, pos := 0, 0;
    while (i < |a|)
    invariant 0 <= i && i <= |a| 
    invariant pos == numPos(a, 0, i) 
    invariant pos <= i     
    {
        pos := if a[i] > 0 then pos + 1 else pos;
        i := i + 1;
    }
    b := pos > |a| / 2;
}