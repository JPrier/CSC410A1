function gcd(a: nat, b: nat): nat
   requires a > 0 && b > 0
{   
   if a == b then a else
   if b > a then gcd(a,b - a) else
    gcd(a - b,b) 
}

// The exampels below demonstrate that we don't need to know precisely what gcd does 
//  to prove certain properties of the gcd function. Your assignment proofs are 
//  all instances of this. You don't need to use any of the correctness lemmas. 
//  You just prove the statements as they are like the ones below.

// EX 1
// lemma additive(a: nat, b: nat)
//    requires a > 0 && b > 0
//    ensures gcd(a ,b) == gcd(a, a + b)
   

// lemma subtractive(a: nat, b: nat)
//     requires a > 0 && b > 0
//     ensures a > b ==> gcd(a,b) == gcd(a, a - b)
//     ensures a < b ==> gcd(a,b) == gcd(b - a, b)


// EX 2
lemma commutativity(a: nat, b: nat)
   requires a > 0 && b > 0
   ensures gcd(a,b) == gcd(b,a)



// EX3

lemma AddCancelation(a: nat, b: nat, m: nat)
   requires a > 0 && b > 0
   ensures gcd(a +  m * b, b) == gcd(a,b)


// EX 4

lemma distributivity(a: nat, b: nat, m: nat)
   requires a > 0 && b > 0
   requires m > 0
   ensures gcd(m * a, m * b) == m * gcd(a,b)
