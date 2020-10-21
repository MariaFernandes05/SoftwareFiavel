//5b,c
method IndexOf (b: array<int>, x: nat) returns ( i : nat)
    requires exists j :: 0 <= j < b.Length &&  b[j] == x 
    ensures 0 <= i < b.Length
    ensures b[i] == x
    ensures forall k :: 0<= k < b.Length && b[k] == x ==> i<=k

{
    i:=0;
    while i<b.Length && b[i] !=x
    invariant forall k :: 0<= k < b.Length && b[k] == x ==> i<=k
    {
        i:=i+1;
    }
}

//5d
method IndexOf5D (b: array<int>, x: nat) returns ( i : nat)
    ensures i < b.Length ==> b[i] ==x 
    ensures i>= b.Length ==>  forall j::0 <= j<b.Length ==> b[j] !=x
{
    i := 0;
    while i<b.Length && b[i] !=x 
        invariant forall j :: 0 <= j <b.Length && x == b[j] ==> i<=j
    {
        if b[i] ==x 
        {
            return i;
        }
        i := i+1;
    }
}

//11
method Power ( n: nat ) returns ( j : nat )
    ensures j == potencias(n)
{
    var k := 0;
    j := 1;
    while k < n 
        decreases n-k
        invariant j == potencias(k) && k <= n 
    {
        k := k + 1;
        j := 2 ∗ j ;
    }
}

function potencias (a:nat) : nat{
    if a <= 0 then 1 else 2 * potencias(a-1)
}

//17
method Find ( a: array <int > , key: int ) returns ( index : int )
ensures 0 <= index <= a.Length ;
ensures index < a.Length ==> a[index] == key;
ensures index == a.Length ==> forall k :: 0 <= k < index ==> a[k] != key
{
    index := 0;
    while index < a.Length && a[index] != key 
        invariant 0<=index<=a.Length
        invariant forall k :: 0 <= k < index ==> a[k] != key
        //invariant index <= a.Length
        //invariant forall k :: 0 <= k < a.Length && a[k] == key ==> index<=k //a[k] != key
    {
        index := index + 1;
    }
}

//12
method IsPrime ( n: nat ) returns ( b: bool )
    ensures b<==> noFactors(n,n)
{
    b := true ;
    if n >= 2
    {
        var divisor := 2;
        while b && divisor < n
            invariant divisor<=n
            invariant b<==> noFactors(n,divisor)
        {
            if n % divisor== 0 { b := false; }
            divisor := divisor + 1;
        }
    }
}

predicate noFactors(n:nat, limit:nat)
{
    forall i::2<=i<limit ==> n%i!=0
}