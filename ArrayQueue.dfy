/**
 * https://algs4.cs.princeton.edu/code/edu/princeton/cs/algs4/ResizingArrayQueue.java
 */
 class {:autocontracts} ArrayBoundedQueue<T(0)> {
    var q: array<T>;    // queue elements
    var n : nat;    // number of elements in the queue
    var first: nat; // index of first element of queue
    var last: nat;  // index of next available slot
    ghost var contents: seq<T>;
   
    predicate Valid(){
        first <= q.Length && 
        last < q.Length &&
        n <= q.Length &&
        last == first <==> (n==0 || n == q.Length) &&
        (first < last ==> n == last-first) &&
        (first >= last && n>0 ==> n == q.Length + last-first) &&
        contents == if n==0
                    then []
                    else if first<last 
                    then q[first..last] 
                    else q[first..] + q[..last]
    }
    constructor ()
        ensures contents == []
    {
        q := new T[10];
        n := 0;
        first := 0;
        last := 0;
    }
    predicate method IsEmpty()
        ensures IsEmpty() <==> contents == []
    {
        n == 0
    }
    predicate method IsFull()
        ensures IsFull() <==> |contents| == q.Length
    {
        n == q.Length
    }
    method Peek() returns (item: T)
        requires !IsEmpty()
        ensures contents == old(contents)
        ensures item == contents[0]
    {
        item := q[first];
    }
    method Enqueue(item: T)
        requires !IsFull()
        ensures contents == old(contents) + [item]
    {
        q[last] := item;
        n := n + 1;
        last := last + 1;
        if last == q.Length { last := 0; }
    }
    method Dequeue() returns (item: T)
        requires !IsEmpty()
        ensures item == old(contents[0])
        ensures contents == old(contents[1..])
    {
        item := q[first];
        n := n - 1;
        first := first + 1;
        if first == q.Length { first := 0; }
   }
}