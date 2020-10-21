//Downwards Sum

method Product ( a: int , b: nat ) returns ( z: int )
    ensures z == a ∗ b
{
    z := 0;
    var x , y: nat := a , b ;
    while y != 0
        invariant z == y ∗ x
    {
        if y % 2 == 1 { z := z + x ; }
        y := y / 2;
        x := x + x ;
    }
}

//Binary Representation of Natural Numbers
method Main ( ) {
    var a := new nat [ 5 ] ;
    a [ 0 ] := 1; a [ 1 ] := 0; a [ 2 ] := 1; a [ 3 ] := 1; a [ 4 ] := 0;
    var n := BinaryToNat ( a ) ;
    print a[..]; print " \t\t " ; print n ; print "\n" ;
}

method BinaryToNat ( a: array <nat > ) returns ( n: nat ){

}
