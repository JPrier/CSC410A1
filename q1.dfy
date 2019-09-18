include "./gcd.dfy"

lemma SubCancelation(a: nat, b: nat, m: nat)
    requires a > 0 && b > 0
    ensures m * b > a ==> gcd(m * b - a, b) == gcd(a,b)
    ensures m * b < a ==> gcd(a - m * b, b) == gcd(a,b)
{  
    if m == 1 {
        if a < b {
            subtractive(a, b);
            calc == {
                gcd(a,b);
                gcd(b-a, b);
            }
        }
        if b < a {
            calc == {
                gcd(a,b);
                gcd(a-b,b);
            }
        }
    } if m > 1 {
        if m*b > a {
            assert m > 1;
            SubCancelation(a,b,m-1);
            assert gcd(a,b) == gcd((m-1)*b - a, b); //How do i put this as an assumption for induction hypoth
            additive1(a, b, m);
            calc == {
                gcd(a,b);
                gcd((m-1)*b - a, b);
                gcd(m*b-b-a+b, b);
                gcd(m*b-a, b);
            }
        } else {
            additive2(a,b,m);
            calc == {
                gcd(a,b);
                gcd(a - (m-1)*b, b);
                gcd(a-m*b-b, b);
                gcd(a-m*b-b+b, b);
                gcd(a-m*b,b);
            }
        }
    }
}

lemma additive1(a: nat, b: nat, m: nat)
   requires a > 0 && b > 0
   ensures gcd(m*b-b-a ,b) == gcd(m*b-a, b)
{

}

lemma additive2(a: nat, b: nat, m: nat)
    requires a > 0 && b > 0
    ensures gcd(a-m*b-b, b) == gcd(a-m*b, b)
{

}
   

lemma subtractive(a: nat, b: nat)
    requires a > 0 && b > 0
    ensures a > b ==> gcd(a,b) == gcd(a, a - b)
    ensures a < b ==> gcd(a,b) == gcd(b - a, b)
{

}

