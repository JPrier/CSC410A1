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
    requires b > 0
{
    a == (q * b) + r && 0 <= r < b
}

lemma quotientRemainder(a: nat, b: nat)
    requires b > 1
    ensures exists q, r :: quotientRemainderPredicate(a, b, q, r)
{
    if a == 0 {
        var q := 0;
        var r := 0;
        assert a == b*q + r;

    } else {

        var q1, r1 :| a == b*q1 + r1;
        var q0 := q1 + 1;
        var r0 := r1 + 1;
        var r2 := 0;
        var a1 := a + 1;

        if r1 + 1 == b {
            calc == {
                a + 1;
                b*q1 + r1 + 1;
                b*q1 + b;
                b*(q1+1);
                b*(q0);
                b*(q0) + r2;
                a1;
            }
            assert quotientRemainderPredicate(a, b, q1, r1);
            assert a1 > a;
            assert quotientRemainderPredicate(a1, b, q0, r2);

        } else if r1 + 1 < b {
            calc == {
                a + 1;
                a1;
                b*q1 + r1 + 1;
                b*q1 + r0;
            }
            assert a1 > a;
            assert a1 == b*q1 + r0;
            assert quotientRemainderPredicate(a1, b, q1, r0);
        }
    }
}



// Bezout identity lemma
lemma bezout(a: nat, b: nat, x: int, y: int)
    requires a > 0 && b > 0 
    ensures a*x + b*y == gcd(a,b)
{
    var k :| 0 < k;
    if b == 0
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
    else
    {
        var b' := b + 1;
        bezout(a, b, x, y);
        quotientRemainder(a, b');
        var q, r :| a == (q * b') + r;
        assert r == a - (q * b);
        var p := q*x + y;
        calc == {
            gcd(a, b');
            a*x + (b')*y;
            (q*b' + r)*x + (b')*y;
            q*b'*x + r*x + b'*y;
            q*b'*x + b'*y + r*x;
            b'*((q*x) + y) + r*x;
            r*x + b'*((q*x) + y);
            gcd(b', r);
        }
        var m, n :| b'*m + r*n == gcd(b', r);
        calc == {
            
        }

    }
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