// GCD function
function gcd(a: nat, b: nat): nat
   requires a > 0 && b > 0
{   
   if a == b then a else
   if b > a then gcd(a,b - a) else
    gcd(a - b,b) 
}

// Helper predicates
predicate divides(a: nat, b: nat)
    requires a > 0
{
    exists c :: b == c * a
}

predicate quotientRemainderPredicate(a: nat, b: nat, q: nat, r: nat)
{
    a == (q * b) + r && 0 <= r < b
}

lemma quotientRemainder(a: nat, b: nat)
    requires b > 0
    ensures exists q, r :: quotientRemainderPredicate(a, b, q, r)
{
    if a == 0 
    {
        assert quotientRemainderPredicate(a, b, 0, 0);
    }
    else
    {
        assert a > 0;
        quotientRemainder(a - 1, b);

    }
}

// Bezout identity lemma
lemma bezout(p: nat, q: nat, x: int, y: int)
    requires p != 0 && q != 0 
    ensures p*x + q*y == gcd(p,q)
{
    // Proof of lemma
}

lemma corectness(a: nat, b: nat, c: nat)
    requires a > 0 && b > 0
    requires gcd(a,b) == 1
    requires divides(a, c*b)
    ensures divides(a,c)
{
    var x: int;
    var y: int;
    bezout(a,b,x,y);

    var k4 :| b*c == k4*a;
    var k5 := x*c + k4*y;
    
    calc == {
        a*x + b*y;
        gcd(a,b);
        1;
    }
    // Multiply both sides by c
    calc == {
        a*x*c + b*y*c;
        c;
        calc == {
            b*y*c;
            b*c*y;
        }
        a*x*c + k4*a*y;
        a*(x*c + k4*y);
        k5 * a;
    }
}