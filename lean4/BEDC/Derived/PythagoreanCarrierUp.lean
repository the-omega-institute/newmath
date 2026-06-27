import BEDC.Derived.PythagoreanUp

namespace BEDC.Derived.PythagoreanCarrierUp

abbrev Z := BEDC.Derived.PythagoreanUp.Z
abbrev Zeq := BEDC.Derived.PythagoreanUp.Zeq
abbrev Zadd := BEDC.Derived.PythagoreanUp.Zadd
abbrev Zmul := BEDC.Derived.PythagoreanUp.Zmul

private def R : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

structure CommonCarrier where
  a : Z
  b : Z
  c : Z
  equation : BEDC.Derived.PythagoreanUp.IsPythagorean a b c

def CarrierRel (x y : CommonCarrier) : Prop :=
  Zeq x.a y.a ∧ Zeq x.b y.b ∧ Zeq x.c y.c

def euclidCommonCarrier (m n : Z) : CommonCarrier :=
  { a := BEDC.Derived.PythagoreanUp.euclidA m n,
    b := BEDC.Derived.PythagoreanUp.euclidB m n,
    c := BEDC.Derived.PythagoreanUp.euclidC m n,
    equation := BEDC.Derived.PythagoreanUp.euclidTriple_isPythagorean m n }

def gaussianParameter (m n : Z) : BEDC.Derived.GaussianUp.GaussInt :=
  { re := m, im := n }

def gaussianSquareParameter (m n : Z) : BEDC.Derived.GaussianUp.GaussInt :=
  BEDC.Derived.GaussianUp.gaussMul
    (gaussianParameter m n) (gaussianParameter m n)

def gaussianNormParameter (m n : Z) : Z :=
  BEDC.Derived.GaussianUp.gaussNorm (gaussianParameter m n)

theorem commonCarrier_euclid_isPythagorean (m n : Z) :
    BEDC.Derived.PythagoreanUp.IsPythagorean (euclidCommonCarrier m n).a
      (euclidCommonCarrier m n).b (euclidCommonCarrier m n).c :=
  (euclidCommonCarrier m n).equation

theorem gaussian_square_re_euclidA (m n : Z) :
    Zeq (gaussianSquareParameter m n).re
      (BEDC.Derived.PythagoreanUp.euclidA m n) :=
  R.refl (BEDC.Derived.PythagoreanUp.euclidA m n)

theorem gaussian_square_im_euclidB (m n : Z) :
    Zeq (gaussianSquareParameter m n).im
      (BEDC.Derived.PythagoreanUp.euclidB m n) :=
  R.add_congr (R.refl (Zmul m n)) (R.mul_comm n m)

theorem gaussian_norm_euclidC (m n : Z) :
    Zeq (gaussianNormParameter m n)
      (BEDC.Derived.PythagoreanUp.euclidC m n) :=
  R.refl (BEDC.Derived.PythagoreanUp.euclidC m n)

theorem euclidC_is_gaussian_norm (m n : Z) :
    Zeq (BEDC.Derived.PythagoreanUp.euclidC m n)
      (gaussianNormParameter m n) :=
  R.refl (BEDC.Derived.PythagoreanUp.euclidC m n)

theorem IsPythagorean_congr {a a' b b' c c' : Z} :
    Zeq a a' -> Zeq b b' -> Zeq c c' ->
      BEDC.Derived.PythagoreanUp.IsPythagorean a b c ->
        BEDC.Derived.PythagoreanUp.IsPythagorean a' b' c' := by
  intro ha hb hc h
  exact R.trans
    (R.add_congr
      (R.mul_congr (R.symm ha) (R.symm ha))
      (R.mul_congr (R.symm hb) (R.symm hb)))
    (R.trans h (R.mul_congr hc hc))

theorem gaussian_parameter_isPythagorean (m n : Z) :
    BEDC.Derived.PythagoreanUp.IsPythagorean
      (gaussianSquareParameter m n).re
      (gaussianSquareParameter m n).im (gaussianNormParameter m n) := by
  exact IsPythagorean_congr
    (R.symm (gaussian_square_re_euclidA m n))
    (R.symm (gaussian_square_im_euclidB m n))
    (R.symm (gaussian_norm_euclidC m n))
    (BEDC.Derived.PythagoreanUp.euclidTriple_isPythagorean m n)

def gaussianCommonCarrier (m n : Z) : CommonCarrier :=
  { a := (gaussianSquareParameter m n).re,
    b := (gaussianSquareParameter m n).im,
    c := gaussianNormParameter m n,
    equation := gaussian_parameter_isPythagorean m n }

theorem gaussianCommonCarrier_matches_euclid (m n : Z) :
    CarrierRel (gaussianCommonCarrier m n) (euclidCommonCarrier m n) := by
  constructor
  · exact gaussian_square_re_euclidA m n
  · constructor
    · exact gaussian_square_im_euclidB m n
    · exact gaussian_norm_euclidC m n

structure EuclidParameterShape where
  m : Z
  n : Z
  carrier : CommonCarrier
  euclid_shape : CarrierRel carrier (euclidCommonCarrier m n)

def euclidParameterShape (m n : Z) : EuclidParameterShape :=
  { m := m,
    n := n,
    carrier := euclidCommonCarrier m n,
    euclid_shape :=
      ⟨R.refl (BEDC.Derived.PythagoreanUp.euclidA m n),
        R.refl (BEDC.Derived.PythagoreanUp.euclidB m n),
        R.refl (BEDC.Derived.PythagoreanUp.euclidC m n)⟩ }

theorem euclidParameterShape_equation (m n : Z) :
    BEDC.Derived.PythagoreanUp.IsPythagorean
      (euclidParameterShape m n).carrier.a
      (euclidParameterShape m n).carrier.b
      (euclidParameterShape m n).carrier.c :=
  (euclidParameterShape m n).carrier.equation

end BEDC.Derived.PythagoreanCarrierUp
