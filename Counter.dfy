class {: autocontracts} Counter {
    var inc: int
    var dec: int
    ghost var val: int
    predicate Valid(){
        val == inc-dec
    }
    constructor ()
        ensures val ==0
	{
		inc, dec := 0, 0;
        val:=0;
	}
	method Inc()
        ensures val ==old(val)+1
	{
		inc := inc + 1;
        val:= inc-dec;
	}
	method Dec()
        ensures val == old(val)-1
	{
		dec := dec + 1;
        val:=inc-dec;
	}
	method Clear()
        ensures val ==0
	{
    	inc, dec := 0, 0;
        val:=inc-dec;
}
	method Get() returns (n: int)
        ensures val ==n
	{
		n := inc - dec;
	}
	method Set(n: int)
        ensures val ==n
	{
        inc, dec := n, 0;
        val := inc-dec;
	}
}




