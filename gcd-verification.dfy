function gcd(a: nat, b: nat): nat
   requires a > 0 && b > 0
{   
   if a == b then a else
   if b > a then gcd(a,b - a) else
    gcd(a - b,b) 
}


// -----------------  Helper Predicates -------------------------

predicate divides(a: nat, b: nat)
    requires a > 0 && b > 0 
{
    exists c :: b == c * a
}

// --------------------- Helper Lemmas -----------------------

lemma DividesDifference(a: nat, b: nat, k: nat)
    requires a > 0 && b > 0 && k > 0 && b > a
    requires divides(k,a) && divides(k,b)
    ensures divides(k, b - a)
{

    // The proof of this lemma can be inlined as well.

    var i :| a == i * k;
    var j :| b == j * k;

    calc == {
        b - a;
        j * k - i * k;
        (j - i) * k;
    }
}

// Proof

lemma gcdDivides(a: nat, b:nat)
   requires a > 0 && b > 0
   ensures gcd(a,b) > 0
   ensures divides(gcd(a,b),b)
   ensures divides(gcd(a,b),a)   
{
   if a == b {
      assert a == 1 * gcd(a,b);
      assert b == 1 * gcd(a,b);
   }
   else if a > b {
      if b == 0 {}
      else {
         gcdDivides(a - b, b);
         
         var j :| a - b == j * gcd(a - b, b);
         var i :| b == i * gcd(a - b,b);

         calc == {
            a;
            b + j * gcd(a - b, b);
            i * gcd(a-b, b) + j * gcd(a - b, b);
            (i + j) * gcd (a - b, b);
            (i + j) * gcd (a,b); 
         }
      }
   }
   else {

      if a == 0 {}
      else {
         gcdDivides(a, b-a);
         var j :| b - a == j * gcd(a, b - a);
         var i :| a == i * gcd(a , b - a);

        // All calculation steps below are not strictly required.
        // Try commenting out random lines to see which ones are 
        // absolutely needed as hints by Dafny.  

         calc == {
            b;
            a + j * gcd(a, b - a);
            i * gcd(a, b - a) + j * gcd(a, b - a);
            (i + j) * gcd (a, b - a);
            (i + j) * gcd (a,b); 
         }
         assert divides(gcd(a,b),b);
         assert divides(gcd(a,b),a);
      }
      
   }
}

lemma largestDivisor(a: nat, b: nat, k: nat)
    requires a > 0 && b > 0
    requires gcd(a,b) > 0
    requires k > 0 && divides(k,a) && divides(k,b) 
    ensures k <= gcd(a,b)
{
    if a == b {

    } else if b > a {
        DividesDifference(a, b, k);
    } else {
        DividesDifference(b, a, k);
    }
}


lemma Correctness(a: nat, b: nat) 
    requires a > 0 && b > 0
    ensures gcd(a,b) > 0
    ensures divides(gcd(a,b),a) && divides(gcd(a,b), b)
    ensures forall k :: (k > 0 && divides(k,a) && divides(k,b)) ==> k <= gcd(a,b)
{
    gcdDivides(a,b);

    forall n | n > 0 && divides(n, a) && divides(n, b)
        ensures n <= gcd(a,b)
    {
         largestDivisor(a, b, n);
    }        
}