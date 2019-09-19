include "gcd.dfy"

predicate divides(a: nat, b:nat)
    requires a > 0
{
    exists k: nat :: b == k * a
}

predicate quotientRemainderPredicate(a: nat, b: nat, q: nat, r: nat)
    requires b > 0
{
    a == (q * b) + r && 0 <= r < b
}

lemma quotientRemainder(a: nat, b: nat)
    requires b > 1 && a >= 0
    ensures exists q, r :: quotientRemainderPredicate(a, b, q, r)
{
    if a == 0 {
        var q := 0;
        var r := 0;
        assert a == b*q + r;
        assert quotientRemainderPredicate(a,b,q,r);

    } else {
        quotientRemainder(a-1, b);
        var q: nat, r: nat :| r >= 0 && a-1 == b*q + r;

        if r == b - 1 {
            assert quotientRemainderPredicate(a, b, (q+1), 0);
        } else if r < b - 1 {
          assert quotientRemainderPredicate(a, b, q, r+1);
        } 
    }
    
    //Uniqueness
    
    var q0: nat, r0: nat :| 0 <= r0 < b && b*q0 + r0 == a;
    var q1: nat, r1: nat :| 0 <= r1 < b && b*q1 + r1 == a;
        
    calc == {
      b*(q0-q1);
      r1-r0;
    }
    assert 0 <= b*(q0-q1) < b;
    assert 0 <= q0-q1 < 1;
    assert q0-q1==0;
    assert q0 == q1;
    calc == {
      r1-r0;
      b*(q0-q1);
      b*0;
      0;
    }
    assert r1-r0 == 0;
    assert r1 == r0;
}


// Bezout identity lemma
lemma bezout(a: nat, b: nat, x: int, y: int)
    requires a > 0 && b > 0 
    ensures a*x + b*y == gcd(a,b)
{
    var k :| 0 < k;
    if b == 0 // BASE CASE
    {
        assert forall x :: x >= 1 ==> gcd(x, 0) == x;
        assert a >= 1;
        calc == {
            gcd(a, 0);
            gcd(a, b);
        }
        assert gcd(a, b) == a;
        calc == {
            gcd(a, b);
            a;
            (a*1) + (b*0);
        }
        var x, y :| a*x + b*y == a;
        assert a*x + b*y == gcd(a, b);
    }
    else // INDUCTION STEP
    {
        // ASSUME FOR b, NOW PROVE FOR b + 1
        bezout(a, b-1, x, y);
        //var b' := b + 1;
        quotientRemainder(a, b);
        var q, r :| a == (q * b) + r;
        assert r == a - (q * b);
        var p := q*x + y;
        calc == {
            gcd(a, b);
            a*x + (b)*y;
            (q*b + r)*x + (b)*y;
            q*b*x + r*x + b*y;
            q*b*x + b*y + r*x;
            b*((q*x) + y) + r*x;
            r*x + b*((q*x) + y);
            gcd(b, r);
        }
        var m, n :| b*m + r*n == gcd(b, r);
        var x0 := n;
        var y0 := (m - q*n);
        calc == {
            gcd(b, r);
            b*m + r*n;
            b*m + (a - (q * b))*n;
            b*m + a*n - q*b*n;
            a*n + b*(m - q*n);
            a*x0 + b*y0;
            gcd(a, b);
        }
        assert b > b-1;
    }
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
