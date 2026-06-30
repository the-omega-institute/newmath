import BEDC.Derived.QuaternionUp
import BEDC.Derived.SumTwoSquaresUp

namespace BEDC.Derived.SumOfSquaresUp

abbrev Z := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq := BEDC.Algebra.Rel.IntEq
abbrev Zadd := BEDC.Algebra.Rel.IntAdd
abbrev Zmul := BEDC.Algebra.Rel.IntMul
abbrev Zneg := BEDC.Algebra.Rel.IntNeg
abbrev Zzero := BEDC.Algebra.Rel.intZero
abbrev Zone := BEDC.Algebra.Rel.intOne

abbrev GaussInt := BEDC.Derived.GaussianUp.GaussInt
abbrev gaussNorm := BEDC.Derived.GaussianUp.gaussNorm
abbrev gaussianPair := BEDC.Derived.SumTwoSquaresUp.gaussianPair

abbrev Quat := BEDC.Derived.QuaternionUp.Quat
abbrev QuatEq := BEDC.Derived.QuaternionUp.QuatEq
abbrev quatZero := BEDC.Derived.QuaternionUp.quatZero
abbrev quatAdd := BEDC.Derived.QuaternionUp.quatAdd
abbrev quatNeg := BEDC.Derived.QuaternionUp.quatNeg
abbrev quatMul := BEDC.Derived.QuaternionUp.quatMul
abbrev quatConj := BEDC.Derived.QuaternionUp.quatConj
abbrev quatNorm := BEDC.Derived.QuaternionUp.quatNorm

private def ZR : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def zsub (a b : Z) : Z :=
  Zadd a (Zneg b)

def zsq (a : Z) : Z :=
  Zmul a a

def twoSquareSum (a b : Z) : Z :=
  BEDC.Derived.SumTwoSquaresUp.squareSum a b

def IsSumTwoSquares (n : Z) : Prop :=
  BEDC.Derived.SumTwoSquaresUp.IsSumTwoSquares n

def IsGaussianNorm (n : Z) : Prop :=
  exists z : GaussInt, Zeq n (gaussNorm z)

theorem gaussianPair_norm_squareSum (a b : Z) :
    Zeq (gaussNorm (gaussianPair a b)) (twoSquareSum a b) :=
  BEDC.Derived.SumTwoSquaresUp.gaussianPair_norm a b

theorem isSumTwoSquares_to_gaussianNorm {n : Z} :
    IsSumTwoSquares n -> IsGaussianNorm n := by
  intro represented
  cases represented with
  | intro a rest =>
      cases rest with
      | intro b witness =>
          exact
            ⟨gaussianPair a b,
              ZR.trans witness (ZR.symm (gaussianPair_norm_squareSum a b))⟩

theorem gaussianNorm_to_isSumTwoSquares {n : Z} :
    IsGaussianNorm n -> IsSumTwoSquares n := by
  intro represented
  cases represented with
  | intro z witness =>
      exact ⟨z.re, z.im, ZR.trans witness (ZR.refl _)⟩

theorem gaussianNorm_is_sum_two_squares (z : GaussInt) :
    IsSumTwoSquares (gaussNorm z) :=
  ⟨z.re, z.im, ZR.refl _⟩

def twoSquareProductRe (a b c d : Z) : Z :=
  zsub (Zmul a c) (Zmul b d)

def twoSquareProductIm (a b c d : Z) : Z :=
  Zadd (Zmul a d) (Zmul b c)

theorem brahmagupta_fibonacci_identity (a b c d : Z) :
    Zeq
      (Zmul (twoSquareSum a b) (twoSquareSum c d))
      (twoSquareSum (twoSquareProductRe a b c d) (twoSquareProductIm a b c d)) :=
  BEDC.Derived.SumTwoSquaresUp.brahmagupta_fibonacci_identity a b c d

theorem IsSumTwoSquares_mul_closed {m n : Z} :
    IsSumTwoSquares m -> IsSumTwoSquares n ->
      IsSumTwoSquares (Zmul m n) :=
  BEDC.Derived.SumTwoSquaresUp.IsSumTwoSquares_mul_closed

def fourSquareSum (a b c d : Z) : Z :=
  Zadd (Zadd (zsq a) (zsq b)) (Zadd (zsq c) (zsq d))

def IsSumFourSquares (n : Z) : Prop :=
  exists a b c d : Z, Zeq n (fourSquareSum a b c d)

def fourSquareQuaternion (a b c d : Z) : Quat :=
  { re := a, imI := b, imJ := c, imK := d }

def eulerFourRe (a b c d e f g h : Z) : Z :=
  zsub (zsub (zsub (Zmul a e) (Zmul b f)) (Zmul c g)) (Zmul d h)

def eulerFourI (a b c d e f g h : Z) : Z :=
  Zadd (Zadd (Zmul a f) (Zmul b e)) (zsub (Zmul c h) (Zmul d g))

def eulerFourJ (a b c d e f g h : Z) : Z :=
  Zadd (zsub (Zmul a g) (Zmul b h)) (Zadd (Zmul c e) (Zmul d f))

def eulerFourK (a b c d e f g h : Z) : Z :=
  Zadd (Zadd (Zmul a h) (Zmul b g)) (zsub (Zmul d e) (Zmul c f))

theorem fourSquareQuaternion_norm (a b c d : Z) :
    Zeq (quatNorm (fourSquareQuaternion a b c d)) (fourSquareSum a b c d) :=
  ZR.refl _

theorem fourSquareQuaternion_mul_shape (a b c d e f g h : Z) :
    QuatEq
      (quatMul (fourSquareQuaternion a b c d) (fourSquareQuaternion e f g h))
      (fourSquareQuaternion
        (eulerFourRe a b c d e f g h)
        (eulerFourI a b c d e f g h)
        (eulerFourJ a b c d e f g h)
        (eulerFourK a b c d e f g h)) :=
  BEDC.Derived.QuaternionUp.QuatEq_refl _

theorem twoSquareSum_zero :
    Zeq (twoSquareSum Zzero Zzero) Zzero := by
  exact ZR.trans
    (ZR.add_congr (ZR.mul_zero Zzero) (ZR.mul_zero Zzero))
    (ZR.add_zero Zzero)

theorem twoSquareSum_one_zero :
    Zeq (twoSquareSum Zone Zzero) Zone := by
  exact ZR.trans
    (ZR.add_congr (ZR.mul_one Zone) (ZR.mul_zero Zzero))
    (ZR.add_zero Zone)

def intTwo : Z :=
  Zadd Zone Zone

theorem twoSquareSum_one_one :
    Zeq (twoSquareSum Zone Zone) intTwo :=
  ZR.add_congr (ZR.mul_one Zone) (ZR.mul_one Zone)

theorem fourSquareSum_zero :
    Zeq (fourSquareSum Zzero Zzero Zzero Zzero) Zzero := by
  have pairZero : Zeq (Zadd Zzero Zzero) Zzero :=
    ZR.add_zero Zzero
  exact ZR.trans
    (ZR.add_congr
      (ZR.add_congr (ZR.mul_zero Zzero) (ZR.mul_zero Zzero))
      (ZR.add_congr (ZR.mul_zero Zzero) (ZR.mul_zero Zzero)))
    (ZR.trans (ZR.add_congr pairZero pairZero) (ZR.add_zero Zzero))

theorem fourSquareSum_one_zero_zero_zero :
    Zeq (fourSquareSum Zone Zzero Zzero Zzero) Zone := by
  exact ZR.trans
    (ZR.add_congr twoSquareSum_one_zero twoSquareSum_zero)
    (ZR.add_zero Zone)

theorem fourSquareSum_one_one_zero_zero :
    Zeq (fourSquareSum Zone Zone Zzero Zzero) intTwo := by
  exact ZR.trans
    (ZR.add_congr twoSquareSum_one_one twoSquareSum_zero)
    (ZR.add_zero intTwo)

theorem IsSumTwoSquares_zero :
    IsSumTwoSquares Zzero :=
  ⟨Zzero, Zzero, ZR.symm twoSquareSum_zero⟩

theorem IsSumTwoSquares_one :
    IsSumTwoSquares Zone :=
  ⟨Zone, Zzero, ZR.symm twoSquareSum_one_zero⟩

theorem IsSumTwoSquares_two :
    IsSumTwoSquares intTwo :=
  ⟨Zone, Zone, ZR.symm twoSquareSum_one_one⟩

theorem IsSumFourSquares_zero :
    IsSumFourSquares Zzero :=
  ⟨Zzero, Zzero, Zzero, Zzero, ZR.symm fourSquareSum_zero⟩

theorem IsSumFourSquares_one :
    IsSumFourSquares Zone :=
  ⟨Zone, Zzero, Zzero, Zzero, ZR.symm fourSquareSum_one_zero_zero_zero⟩

theorem IsSumFourSquares_two :
    IsSumFourSquares intTwo :=
  ⟨Zone, Zone, Zzero, Zzero, ZR.symm fourSquareSum_one_one_zero_zero⟩

theorem quaternion_norm_mul (q r : Quat) :
    Zeq (quatNorm (quatMul q r)) (Zmul (quatNorm q) (quatNorm r)) :=
  BEDC.Derived.QuaternionUp.quatNorm_mul q r

theorem euler_four_square_identity (a b c d e f g h : Z) :
    Zeq
      (Zmul (fourSquareSum a b c d) (fourSquareSum e f g h))
      (fourSquareSum
        (eulerFourRe a b c d e f g h)
        (eulerFourI a b c d e f g h)
        (eulerFourJ a b c d e f g h)
        (eulerFourK a b c d e f g h)) := by
  let q := fourSquareQuaternion a b c d
  let r := fourSquareQuaternion e f g h
  have normMul :
      Zeq (quatNorm (quatMul q r)) (Zmul (quatNorm q) (quatNorm r)) :=
    quaternion_norm_mul q r
  have factorShape :
      Zeq (Zmul (quatNorm q) (quatNorm r))
        (Zmul (fourSquareSum a b c d) (fourSquareSum e f g h)) :=
    ZR.mul_congr
      (fourSquareQuaternion_norm a b c d)
      (fourSquareQuaternion_norm e f g h)
  have productShape :
      Zeq (quatNorm (quatMul q r))
        (quatNorm
          (fourSquareQuaternion
            (eulerFourRe a b c d e f g h)
            (eulerFourI a b c d e f g h)
            (eulerFourJ a b c d e f g h)
            (eulerFourK a b c d e f g h))) :=
    BEDC.Derived.QuaternionUp.quatNorm_respects
      (fourSquareQuaternion_mul_shape a b c d e f g h)
  exact ZR.trans (ZR.symm factorShape)
    (ZR.trans (ZR.symm normMul)
      (ZR.trans productShape
        (fourSquareQuaternion_norm
          (eulerFourRe a b c d e f g h)
          (eulerFourI a b c d e f g h)
          (eulerFourJ a b c d e f g h)
          (eulerFourK a b c d e f g h))))

theorem IsSumFourSquares_respects {m n : Z} :
    Zeq m n -> IsSumFourSquares m -> IsSumFourSquares n := by
  intro same represented
  cases represented with
  | intro a rest =>
      cases rest with
      | intro b rest =>
          cases rest with
          | intro c rest =>
              cases rest with
              | intro d witness =>
                  exact ⟨a, b, c, d, ZR.trans (ZR.symm same) witness⟩

theorem IsSumFourSquares_mul_closed {m n : Z} :
    IsSumFourSquares m -> IsSumFourSquares n ->
      IsSumFourSquares (Zmul m n) := by
  intro hm hn
  cases hm with
  | intro a hma =>
      cases hma with
      | intro b hmb =>
          cases hmb with
          | intro c hmc =>
              cases hmc with
              | intro d hmd =>
                  cases hn with
                  | intro e hne =>
                      cases hne with
                      | intro f hnf =>
                          cases hnf with
                          | intro g hng =>
                              cases hng with
                              | intro h witnessN =>
                                  exact
                                    ⟨eulerFourRe a b c d e f g h,
                                      eulerFourI a b c d e f g h,
                                      eulerFourJ a b c d e f g h,
                                      eulerFourK a b c d e f g h,
                                      ZR.trans
                                        (ZR.mul_congr hmd witnessN)
                                        (euler_four_square_identity
                                          a b c d e f g h)⟩

end BEDC.Derived.SumOfSquaresUp
