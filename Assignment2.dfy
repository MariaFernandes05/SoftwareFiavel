//Downwards Sum

method Product ( a: int , b: nat ) returns ( z: int )
    ensures z == a ∗ b
{
    z := 0;
    var x , y: nat := a , b ;
    while y != 0
        invariant z == a*b - x*y
    {
        if y % 2 == 1 { z := z + x ; }
        y := y / 2;
        x := x + x ;
    }
}

//Binary Representation of Natural Numbers
method Main ( ) {
    var a := new nat [ 5 ] ;
    a[0]:=1; a[1]:=0;a[2]:=1;a[3]:=1;a[4]:=0;
    var n := BinaryToNat(a);
    print a[..]; print " \t\t " ; print n ; print "\n" ;
}

method BinaryToNat ( a: array <nat > ) returns ( n: nat )
    requires a.Length > 0
    requires OnlyBinary(a)
    requires a[0] == 1
    //ensures n == natural(a[0..])

{
    var i :nat :=0;
    var aux:=0;
    var power:=0;
    while i <a.Length
        //invariant 
    {  
        power:= Power(a.Length-1-i);
        aux := a[i] % 10;
        n := n + aux * power;
        i := i+1;
    }
}

/*function natural(a: array <nat>) : nat{
    if i==a.Length-1 then a[i] % 10 + power else natural(a,i+1)
}*/


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
predicate OnlyBinary(a: array<nat >)
    reads a
    requires a.Length>0
{
    forall i :nat :: i<a.Length && (a[i]==1 || a[i] ==0)
}
