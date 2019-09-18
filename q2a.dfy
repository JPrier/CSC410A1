include "gcd.dfy"

predicate divides(a: nat, b:nat)
    requires a > 0
{
    exists k: nat :: b == k * a
}

lemma correctness(a: nat, b: nat, k: nat)
    requires a > 0 && b > 0 && k > 0
    requires divides(k, a) && divides(k, b)
    ensures divides(k, gcd(a,b))
{
    
}

