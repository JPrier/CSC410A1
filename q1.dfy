include "./gcd.dfy"

lemma SubCancelation(a: nat, b: nat, m: nat)
    requires a > 0 && b > 0
    ensures m * b > a ==> gcd(m * b - a, b) == gcd(a,b)
    ensures m * b < a ==> gcd(a - m * b, b) == gcd(a,b)
{   
    // if m == 1 (subractive) else it is subtractive again
    // TODO: need to figure out how to repeat subtractive recursively
    // 
    if m == 1 {
        if a > b {
            subtractive(a, b);
        }
        else {
            assert gcd(a,b) == gcd(a-b, b);
        }
    }
}

lemma additive(a: nat, b: nat)
   requires a > 0 && b > 0
   ensures gcd(a ,b) == gcd(a, a + b)
   

lemma subtractive(a: nat, b: nat)
    requires a > 0 && b > 0
    ensures a > b ==> gcd(a,b) == gcd(a, a - b)
    ensures a < b ==> gcd(a,b) == gcd(b - a, b)

