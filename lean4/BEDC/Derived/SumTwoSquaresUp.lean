import BEDC.Algebra.Rel.GaussianUp
import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.SumTwoSquaresUp

abbrev Z := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq := BEDC.Algebra.Rel.IntEq
abbrev Zadd := BEDC.Algebra.Rel.IntAdd
abbrev Zmul := BEDC.Algebra.Rel.IntMul
abbrev Zneg := BEDC.Algebra.Rel.IntNeg

abbrev GaussInt := BEDC.Derived.GaussianUp.GaussInt
abbrev GaussEq := BEDC.Derived.GaussianUp.GaussEq
abbrev gaussMul := BEDC.Derived.GaussianUp.gaussMul
abbrev gaussNorm := BEDC.Derived.GaussianUp.gaussNorm

private def R : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def zsub (a b : Z) : Z :=
  Zadd a (Zneg b)

def zsq (a : Z) : Z :=
  Zmul a a

def squareSum (a b : Z) : Z :=
  Zadd (zsq a) (zsq b)

def IsSumTwoSquares (n : Z) : Prop :=
  ∃ a b : Z, Zeq n (squareSum a b)

def gaussianPair (a b : Z) : GaussInt :=
  { re := a, im := b }

theorem gaussianPair_norm (a b : Z) :
    Zeq (gaussNorm (gaussianPair a b)) (squareSum a b) :=
  R.refl _

theorem gaussianPair_mul (a b c d : Z) :
    GaussEq (gaussMul (gaussianPair a b) (gaussianPair c d))
      (gaussianPair
        (zsub (Zmul a c) (Zmul b d))
        (Zadd (Zmul a d) (Zmul b c))) := by
  constructor
  · exact R.refl _
  · exact R.refl _

theorem brahmagupta_fibonacci_identity (a b c d : Z) :
    Zeq
      (Zmul (squareSum a b) (squareSum c d))
      (squareSum
        (zsub (Zmul a c) (Zmul b d))
        (Zadd (Zmul a d) (Zmul b c))) := by
  let z := gaussianPair a b
  let w := gaussianPair c d
  let productWitness :=
    gaussianPair
      (zsub (Zmul a c) (Zmul b d))
      (Zadd (Zmul a d) (Zmul b c))
  have normMul :
      Zeq (gaussNorm (gaussMul z w))
        (Zmul (gaussNorm z) (gaussNorm w)) :=
    BEDC.Derived.GaussianUp.gaussNorm_mul z w
  have productShape :
      GaussEq (gaussMul z w) productWitness :=
    gaussianPair_mul a b c d
  have productNormShape :
      Zeq (gaussNorm (gaussMul z w)) (gaussNorm productWitness) :=
    BEDC.Derived.GaussianUp.gaussNorm_respects productShape
  have factorsShape :
      Zeq (Zmul (gaussNorm z) (gaussNorm w))
        (Zmul (squareSum a b) (squareSum c d)) :=
    R.mul_congr (gaussianPair_norm a b) (gaussianPair_norm c d)
  have witnessShape :
      Zeq (gaussNorm productWitness)
        (squareSum
          (zsub (Zmul a c) (Zmul b d))
          (Zadd (Zmul a d) (Zmul b c))) :=
    gaussianPair_norm
      (zsub (Zmul a c) (Zmul b d))
      (Zadd (Zmul a d) (Zmul b c))
  exact R.trans (R.symm factorsShape)
    (R.trans (R.symm normMul)
      (R.trans productNormShape witnessShape))

theorem brahmagupta_fibonacci_identity_symm (a b c d : Z) :
    Zeq
      (squareSum
        (zsub (Zmul a c) (Zmul b d))
        (Zadd (Zmul a d) (Zmul b c)))
      (Zmul (squareSum a b) (squareSum c d)) :=
  R.symm (brahmagupta_fibonacci_identity a b c d)

theorem IsSumTwoSquares_respects {m n : Z} :
    Zeq m n -> IsSumTwoSquares m -> IsSumTwoSquares n := by
  intro same represented
  cases represented with
  | intro a rest =>
      cases rest with
      | intro b witness =>
          exact ⟨a, b, R.trans (R.symm same) witness⟩

theorem IsSumTwoSquares_mul_closed {m n : Z} :
    IsSumTwoSquares m -> IsSumTwoSquares n ->
      IsSumTwoSquares (Zmul m n) := by
  intro hm hn
  cases hm with
  | intro a hma =>
      cases hma with
      | intro b mWitness =>
          cases hn with
          | intro c hnc =>
              cases hnc with
              | intro d nWitness =>
                  exact
                    ⟨zsub (Zmul a c) (Zmul b d),
                      Zadd (Zmul a d) (Zmul b c),
                      R.trans
                        (R.mul_congr mWitness nWitness)
                        (brahmagupta_fibonacci_identity a b c d)⟩

end BEDC.Derived.SumTwoSquaresUp
