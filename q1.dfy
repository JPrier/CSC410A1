lemma SubCancelation(a: nat, b: nat, m: nat)
    requires a > 0 && b > 0
    ensures m * b > a ==> gcd(m * b - a, b) == gcd(a,b)
    ensures m * b < a ==> gcd(a - m * b, b) == gcd(a,b)
{
    
}