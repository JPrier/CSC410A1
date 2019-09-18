include "gcd.dfy"

predicate divides(a: nat, b:nat)
    requires a > 0
{
    exists k: nat :: b == k * a
}

// Bezout identity lemma
lemma bezout(p: nat, q: nat, x: int, y: int)
    requires p != 0 && q != 0 
    ensures p*x + q*y == gcd(p,q)
{
    // Proof of lemma
    
}

lemma correctness(a: nat, b: nat, k: nat)
    requires a > 0 && b > 0 && k > 0
    requires divides(k, a) && divides(k, b)
    ensures divides(k, gcd(a,b))
{
    var c0 :| a == k * c0;
    var c1 :| b == k * c1;

    bezout(a,b,c0,c1);

    var c2, c3 :| gcd(a,b) == c2*a + c3*b;
    var c4 == (c2*c0 + c3*c1)
    calc == {
        gcd(a,b);
        c2*a + c3*b;
        c2*(k * c0) + c3*(k * c1);
        (c2*c0 + c3*c1) * k;
        c4 * k;
    }
}

