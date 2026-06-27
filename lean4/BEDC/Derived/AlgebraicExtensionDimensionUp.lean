import BEDC.Algebra.Rel.GaussianUp
import BEDC.Algebra.Rel.EisensteinUp
import BEDC.Algebra.Rel.QuadIntUp

namespace BEDC.Derived.AlgebraicExtensionDimensionUp

open BEDC.Algebra.Rel

universe u v

/-- 从第 `start` 个幂开始列出有限个幂。 -/
def firstPowersFrom {A : Type u} (power : Nat -> A) (start : Nat) :
    Nat -> List A
  | 0 => []
  | fuel + 1 => power start :: firstPowersFrom power (start + 1) fuel

def firstPowers {A : Type u} (power : Nat -> A) (degree : Nat) :
    List A :=
  firstPowersFrom power 0 degree

/--
有限代数元扩张的 power-basis 数据包。

这里的 `informationDimension` 是坐标层面的严格自然数，不是几何隐喻。
域性、极小多项式构造和线性无关性由具体数据包给出；本文件只导出
这些字段在 kernel 中可核验的后果。
-/
structure FiniteAlgebraicElementExtension
    (Base : Type u) (Ext : Type v) where
  baseRel : Base -> Base -> Prop
  extRel : Ext -> Ext -> Prop
  baseRing : RelCommRing Base baseRel
  extensionRing : RelCommRing Ext extRel
  scalarEmbedding : Base -> Ext
  scalarEmbedding_respects :
    ∀ {a b : Base}, baseRel a b ->
      extRel (scalarEmbedding a) (scalarEmbedding b)
  alpha : Ext
  minimalPolynomialDegree : Nat
  extensionDegree : Nat
  informationDimension : Nat
  linearCombination : List Base -> Ext
  zeroCoefficients : List Base -> Prop
  extensionDegree_eq_minimalPolynomialDegree :
    extensionDegree = minimalPolynomialDegree
  informationDimension_eq_extensionDegree :
    informationDimension = extensionDegree
  powerBasis_linearIndependent :
    ∀ coeffs : List Base, coeffs.length = minimalPolynomialDegree ->
      extRel (linearCombination coeffs) extensionRing.zero ->
        zeroCoefficients coeffs

namespace FiniteAlgebraicElementExtension

variable {Base : Type u} {Ext : Type v}

def elementPower (E : FiniteAlgebraicElementExtension Base Ext) :
    Nat -> Ext
  | 0 => E.extensionRing.one
  | n + 1 => E.extensionRing.mul (elementPower E n) E.alpha

def powerBasis (E : FiniteAlgebraicElementExtension Base Ext) :
    List Ext :=
  firstPowers (elementPower E) E.minimalPolynomialDegree

def PowerBasisLinearIndependent
    (E : FiniteAlgebraicElementExtension Base Ext) : Prop :=
  ∀ coeffs : List Base, coeffs.length = E.minimalPolynomialDegree ->
    E.extRel (E.linearCombination coeffs) E.extensionRing.zero ->
      E.zeroCoefficients coeffs

theorem powerBasisLinearIndependent_holds
    (E : FiniteAlgebraicElementExtension Base Ext) :
    E.PowerBasisLinearIndependent :=
  E.powerBasis_linearIndependent

theorem extensionDegreeMatchesMinimalPolynomialDegree
    (E : FiniteAlgebraicElementExtension Base Ext) :
    E.extensionDegree = E.minimalPolynomialDegree :=
  E.extensionDegree_eq_minimalPolynomialDegree

theorem extensionDegree_eq_informationDimension
    (E : FiniteAlgebraicElementExtension Base Ext) :
    E.extensionDegree = E.informationDimension :=
  Eq.symm E.informationDimension_eq_extensionDegree

theorem degree_eq_informationDimension
    (E : FiniteAlgebraicElementExtension Base Ext) :
    E.extensionDegree = E.informationDimension :=
  E.extensionDegree_eq_informationDimension

theorem minimalPolynomialDegree_eq_informationDimension
    (E : FiniteAlgebraicElementExtension Base Ext) :
    E.minimalPolynomialDegree = E.informationDimension :=
  Eq.trans (Eq.symm E.extensionDegree_eq_minimalPolynomialDegree)
    E.extensionDegree_eq_informationDimension

end FiniteAlgebraicElementExtension

theorem powerBasis_linearIndependent
    {Base : Type u} {Ext : Type v}
    (E : FiniteAlgebraicElementExtension Base Ext) :
    E.PowerBasisLinearIndependent :=
  E.powerBasis_linearIndependent

theorem extensionDegree_eq_minimalPolynomialDegree
    {Base : Type u} {Ext : Type v}
    (E : FiniteAlgebraicElementExtension Base Ext) :
    E.extensionDegree = E.minimalPolynomialDegree :=
  E.extensionDegree_eq_minimalPolynomialDegree

theorem degree_eq_informationDimension
    {Base : Type u} {Ext : Type v}
    (E : FiniteAlgebraicElementExtension Base Ext) :
    E.extensionDegree = E.informationDimension :=
  E.degree_eq_informationDimension

/--
二次坐标证书。它表达的基是 `{1, alpha}`，系数为显式二元组。
这里不把系数组装成商空间或有限集，也不把坐标环直接冒充域扩张。
-/
structure QuadraticCoordinateExtension
    (Base : Type u) (Ext : Type v) where
  baseRel : Base -> Base -> Prop
  extRel : Ext -> Ext -> Prop
  baseRing : RelCommRing Base baseRel
  extensionRing : RelCommRing Ext extRel
  scalarEmbedding : Base -> Ext
  scalarEmbedding_respects :
    ∀ {a b : Base}, baseRel a b ->
      extRel (scalarEmbedding a) (scalarEmbedding b)
  alpha : Ext
  coordinateCombination : Base -> Base -> Ext
  coeffPairZero : Base -> Base -> Prop
  basisCardinality : Nat
  coordinateDimension : Nat
  informationDimension : Nat
  coordinateDimension_eq_basisCardinality :
    coordinateDimension = basisCardinality
  informationDimension_eq_coordinateDimension :
    informationDimension = coordinateDimension
  coordinateBasis_linearIndependent :
    ∀ a b : Base, extRel (coordinateCombination a b) extensionRing.zero ->
      coeffPairZero a b

namespace QuadraticCoordinateExtension

variable {Base : Type u} {Ext : Type v}

def powerBasis (E : QuadraticCoordinateExtension Base Ext) :
    List Ext :=
  [E.extensionRing.one, E.alpha]

def CoordinateBasisLinearIndependent
    (E : QuadraticCoordinateExtension Base Ext) : Prop :=
  ∀ a b : Base, E.extRel (E.coordinateCombination a b) E.extensionRing.zero ->
    E.coeffPairZero a b

theorem coordinateBasisLinearIndependent_holds
    (E : QuadraticCoordinateExtension Base Ext) :
    E.CoordinateBasisLinearIndependent :=
  E.coordinateBasis_linearIndependent

theorem coordinateDimension_eq_informationDimension
    (E : QuadraticCoordinateExtension Base Ext) :
    E.coordinateDimension = E.informationDimension :=
  Eq.symm E.informationDimension_eq_coordinateDimension

theorem basisCardinality_eq_informationDimension
    (E : QuadraticCoordinateExtension Base Ext) :
    E.basisCardinality = E.informationDimension :=
  Eq.trans (Eq.symm E.coordinateDimension_eq_basisCardinality)
    E.coordinateDimension_eq_informationDimension

theorem powerBasis_length
    (E : QuadraticCoordinateExtension Base Ext) :
    E.powerBasis.length = 2 :=
  rfl

end QuadraticCoordinateExtension

theorem quadratic_coordinateDimension_eq_informationDimension
    {Base : Type u} {Ext : Type v}
    (E : QuadraticCoordinateExtension Base Ext) :
    E.coordinateDimension = E.informationDimension :=
  E.coordinateDimension_eq_informationDimension

theorem quadratic_basis_linearIndependent
    {Base : Type u} {Ext : Type v}
    (E : QuadraticCoordinateExtension Base Ext) :
    E.CoordinateBasisLinearIndependent :=
  E.coordinateBasis_linearIndependent

abbrev Z := IntegerUp
abbrev Zeq := IntEq
abbrev Zzero := intZero
abbrev Zone := intOne
abbrev Zadd := IntAdd
abbrev Zmul := IntMul
abbrev Zneg := IntNeg

private def zring : RelCommRing Z Zeq :=
  IntegerUp_RelCommRing

inductive TwoCoeffZero : List Z -> Prop where
  | pair {a b : Z} : Zeq a Zzero -> Zeq b Zzero -> TwoCoeffZero [a, b]

abbrev GaussInt := BEDC.Derived.GaussianUp.GaussInt
abbrev GaussEq := BEDC.Derived.GaussianUp.GaussEq
abbrev gaussZero := BEDC.Derived.GaussianUp.gaussZero
abbrev gaussOne := BEDC.Derived.GaussianUp.gaussOne
abbrev gaussAdd := BEDC.Derived.GaussianUp.gaussAdd
abbrev gaussMul := BEDC.Derived.GaussianUp.gaussMul
abbrev gaussNeg := BEDC.Derived.GaussianUp.gaussNeg
abbrev gaussOfInt := BEDC.Derived.GaussianUp.gaussOfInt

def gaussianAlpha : GaussInt :=
  { re := Zzero, im := Zone }

def gaussianCoordinateCombination (a b : Z) : GaussInt :=
  { re := a, im := b }

theorem gaussian_scalarEmbedding_respects {a b : Z} :
    Zeq a b -> GaussEq (gaussOfInt a) (gaussOfInt b) := by
  intro h
  constructor
  · exact h
  · exact zring.refl Zzero

theorem gaussian_alpha_square_eq_neg_one :
    GaussEq (gaussMul gaussianAlpha gaussianAlpha) (gaussNeg gaussOne) := by
  constructor
  · exact zring.trans
      (zring.add_congr
        (zring.zero_mul Zzero)
        (zring.neg_congr (zring.mul_one Zone)))
      (zring.zero_add (Zneg Zone))
  · exact zring.trans
      (zring.add_congr (zring.zero_mul Zone) (zring.mul_zero Zone))
      (zring.trans (zring.add_zero Zzero) (zring.symm zring.neg_zero))

theorem gaussian_coordinate_linearIndependent (a b : Z) :
    GaussEq (gaussianCoordinateCombination a b) gaussZero ->
      TwoCoeffZero [a, b] := by
  intro hzero
  exact TwoCoeffZero.pair hzero.left hzero.right

def gaussianCoordinateExtension :
    QuadraticCoordinateExtension Z GaussInt where
  baseRel := Zeq
  extRel := GaussEq
  baseRing := IntegerUp_RelCommRing
  extensionRing := GaussianUp_RelCommRing
  scalarEmbedding := gaussOfInt
  scalarEmbedding_respects := gaussian_scalarEmbedding_respects
  alpha := gaussianAlpha
  coordinateCombination := gaussianCoordinateCombination
  coeffPairZero := fun a b => TwoCoeffZero [a, b]
  basisCardinality := 2
  coordinateDimension := 2
  informationDimension := 2
  coordinateDimension_eq_basisCardinality := rfl
  informationDimension_eq_coordinateDimension := rfl
  coordinateBasis_linearIndependent := gaussian_coordinate_linearIndependent

theorem gaussian_informationDimension_eq_two :
    gaussianCoordinateExtension.informationDimension = 2 :=
  rfl

theorem gaussian_coordinateDimension_eq_informationDimension :
    gaussianCoordinateExtension.coordinateDimension =
      gaussianCoordinateExtension.informationDimension :=
  rfl

theorem gaussian_powerBasis_length :
    gaussianCoordinateExtension.powerBasis.length = 2 :=
  rfl

theorem gaussian_power_one_eq_alpha :
    GaussEq
      (gaussMul gaussianCoordinateExtension.extensionRing.one
        gaussianCoordinateExtension.alpha)
      gaussianAlpha :=
  GaussianUp_RelCommRing.one_mul gaussianAlpha

abbrev EisInt := BEDC.Derived.EisensteinUp.EisInt
abbrev EisEq := BEDC.Derived.EisensteinUp.EisEq
abbrev eisZero := BEDC.Derived.EisensteinUp.eisZero
abbrev eisOne := BEDC.Derived.EisensteinUp.eisOne
abbrev eisOmega := BEDC.Derived.EisensteinUp.eisOmega
abbrev eisOfInt := BEDC.Derived.EisensteinUp.eisOfInt

def eisensteinCoordinateCombination (a b : Z) : EisInt :=
  { re := a, om := b }

theorem eisenstein_scalarEmbedding_respects {a b : Z} :
    Zeq a b -> EisEq (eisOfInt a) (eisOfInt b) := by
  intro h
  constructor
  · exact h
  · exact zring.refl Zzero

theorem eisenstein_alpha_square_relation :
    EisEq
      (BEDC.Derived.EisensteinUp.eisMul eisOmega eisOmega)
      (BEDC.Derived.EisensteinUp.eisNeg
        (BEDC.Derived.EisensteinUp.eisAdd eisOmega eisOne)) :=
  BEDC.Derived.EisensteinUp.eisOmega_square

theorem eisenstein_coordinate_linearIndependent (a b : Z) :
    EisEq (eisensteinCoordinateCombination a b) eisZero ->
      TwoCoeffZero [a, b] := by
  intro hzero
  exact TwoCoeffZero.pair hzero.left hzero.right

def eisensteinCoordinateExtension :
    QuadraticCoordinateExtension Z EisInt where
  baseRel := Zeq
  extRel := EisEq
  baseRing := IntegerUp_RelCommRing
  extensionRing := EisensteinUp_RelCommRing
  scalarEmbedding := eisOfInt
  scalarEmbedding_respects := eisenstein_scalarEmbedding_respects
  alpha := eisOmega
  coordinateCombination := eisensteinCoordinateCombination
  coeffPairZero := fun a b => TwoCoeffZero [a, b]
  basisCardinality := 2
  coordinateDimension := 2
  informationDimension := 2
  coordinateDimension_eq_basisCardinality := rfl
  informationDimension_eq_coordinateDimension := rfl
  coordinateBasis_linearIndependent := eisenstein_coordinate_linearIndependent

theorem eisenstein_informationDimension_eq_two :
    eisensteinCoordinateExtension.informationDimension = 2 :=
  rfl

theorem eisenstein_coordinateDimension_eq_informationDimension :
    eisensteinCoordinateExtension.coordinateDimension =
      eisensteinCoordinateExtension.informationDimension :=
  rfl

theorem eisenstein_powerBasis_length :
    eisensteinCoordinateExtension.powerBasis.length = 2 :=
  rfl

theorem eisenstein_power_one_eq_alpha :
    EisEq
      (BEDC.Derived.EisensteinUp.eisMul
        eisensteinCoordinateExtension.extensionRing.one
        eisensteinCoordinateExtension.alpha)
      eisOmega :=
  EisensteinUp_RelCommRing.one_mul eisOmega

abbrev QuadInt := BEDC.Derived.QuadIntUp.QuadInt
abbrev QuadEq {d : Z} := BEDC.Derived.QuadIntUp.QuadEq (d := d)
abbrev quadZero {d : Z} := BEDC.Derived.QuadIntUp.quadZero (d := d)
abbrev quadOne {d : Z} := BEDC.Derived.QuadIntUp.quadOne (d := d)
abbrev quadSqrt {d : Z} := BEDC.Derived.QuadIntUp.quadSqrt (d := d)
abbrev quadOfInt {d : Z} := BEDC.Derived.QuadIntUp.quadOfInt (d := d)

def quadCoordinateCombination {d : Z} (a b : Z) : QuadInt d :=
  BEDC.Derived.QuadIntUp.quadMk (d := d) a b

theorem quad_scalarEmbedding_respects {d : Z} {a b : Z} :
    Zeq a b -> QuadEq (d := d) (quadOfInt a) (quadOfInt b) := by
  intro h
  constructor
  · exact h
  · exact zring.refl Zzero

theorem quad_alpha_square_relation (d : Z) :
    QuadEq (d := d)
      (BEDC.Derived.QuadIntUp.quadMul (quadSqrt (d := d)) quadSqrt)
      (quadOfInt d) :=
  BEDC.Derived.QuadIntUp.quadSqrt_mul_self

theorem quad_coordinate_linearIndependent (d a b : Z) :
    QuadEq (d := d) (quadCoordinateCombination (d := d) a b) quadZero ->
      TwoCoeffZero [a, b] := by
  intro hzero
  exact TwoCoeffZero.pair hzero.left hzero.right

def quadCoordinateExtension (d : Z) :
    QuadraticCoordinateExtension Z (QuadInt d) where
  baseRel := Zeq
  extRel := QuadEq (d := d)
  baseRing := IntegerUp_RelCommRing
  extensionRing := QuadIntUp_RelCommRing d
  scalarEmbedding := quadOfInt
  scalarEmbedding_respects := quad_scalarEmbedding_respects
  alpha := quadSqrt
  coordinateCombination := quadCoordinateCombination
  coeffPairZero := fun a b => TwoCoeffZero [a, b]
  basisCardinality := 2
  coordinateDimension := 2
  informationDimension := 2
  coordinateDimension_eq_basisCardinality := rfl
  informationDimension_eq_coordinateDimension := rfl
  coordinateBasis_linearIndependent := quad_coordinate_linearIndependent d

theorem quad_informationDimension_eq_two (d : Z) :
    (quadCoordinateExtension d).informationDimension = 2 :=
  rfl

theorem quad_coordinateDimension_eq_informationDimension (d : Z) :
    (quadCoordinateExtension d).coordinateDimension =
      (quadCoordinateExtension d).informationDimension :=
  rfl

theorem quad_powerBasis_length (d : Z) :
    (quadCoordinateExtension d).powerBasis.length = 2 :=
  rfl

theorem quad_power_one_eq_alpha (d : Z) :
    QuadEq (d := d)
      (BEDC.Derived.QuadIntUp.quadMul
        (quadCoordinateExtension d).extensionRing.one
        (quadCoordinateExtension d).alpha)
      quadSqrt :=
  (QuadIntUp_RelCommRing d).one_mul quadSqrt

end BEDC.Derived.AlgebraicExtensionDimensionUp
