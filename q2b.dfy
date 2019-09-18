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

lemma gcdDivides(a: nat, b: nat, k: nat)
    requires a > 0 && b > 0 && k > 0
    requires divides(k, a) && divides(k, b)
    ensures divides(k, gcd(a,b))
{
    var c0 :| a == k * c0;
    var c1 :| b == k * c1;

    var c2, c3 :| gcd(a,b) == c2*a + c3*b;
    bezout(a,b,c2,c3);
    
    var c4 :| (c2*c0 + c3*c1) * k == c4 * k;
    calc == {
        gcd(a,b);
        c2*a + c3*b;
        c2*(k * c0) + c3*(k * c1);
        (c2*c0 + c3*c1) * k;
        c4 * k;
    }
}

lemma associative(a: nat, b: nat, c: nat)
    requires a > 0 && b > 0 && c > 0
    ensures gcd(a, gcd(b,c)) == gcd(gcd(a,b), c)
{
    var x :| x == gcd(a, gcd(b,c));
    var y :| y == gcd(gcd(a,b), c);
    
    gcdDivides(a, gcd(b,c), x);
    gcdDivides(b, c, x);

    // x divides y
    assert divides(x, a);
    assert divides(x, gcd(b,c));
    assert divides(x, b);
    assert divides(x, c);
    assert divides(x, gcd(a,b));
    assert divides(x, gcd(gcd(a,b),c));
    assert divides(x, y);

    gcdDivides(gcd(a,b), c, y);
    gcdDivides(a, b, y);

    // y divides x
    assert divides(y, gcd(a,b));
    assert divides(y, c);
    assert divides(y, a);
    assert divides(y, b);
    assert divides(y, gcd(b,c));
    assert divides(y, gcd(a, gcd(b,c)));
    assert divides(y, x);
}
