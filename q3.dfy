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
    requires a > 0 && b > 0 
{
    exists c :: b == c * a
}

// Bezout identity lemma
lemma bezout(p: nat, q: nat, x: int, y: int)
    requires p != 0 && q != 0 
    ensures p*x + q*y == gcd(p,q)
{
    // Proof of lemma
    
}

lemma corectness(a: nat, b: nat, c: nat)
    requires a > 0 && b > 0 && c > 0
    requires gcd(a,b) == 1
    requires divides(a,b*c)
    ensures divides(a,c)
{
    var x: int;
    var y: int;
    bezout(a,b,x,y);

    var k4 :| b*c == k4*a;
    
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
    }
    assert divides((x*c + k4*y), c)
}