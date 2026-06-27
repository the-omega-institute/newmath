import BEDC.Derived.AlgebraicExtensionDimensionUp
import BEDC.Derived.PolynomialUp.IntegerRing

/-!
不可约信息谱因子的有限 BEDC 表面。

这里的 `spectral` 只指公开分解 ledger 的行名，不引入解析谱理论、几何维度
或商结构。一般存在性与外部多项式不可约判定不在本文件中伪造；具体实例必须
提供 `IrreduciblePolynomialRow` 字段。
-/

namespace BEDC.Derived.RHRoute.IrreducibleInformationSpectralFactor

universe u v

abbrev Poly := BEDC.Derived.PolynomialUp.Poly
abbrev PolyEq := BEDC.Derived.PolynomialUp.PolyEq
abbrev polyOne := BEDC.Derived.PolynomialUp.polyOne
abbrev polyMul := BEDC.Derived.PolynomialUp.polyMul
abbrev FiniteAlgebraicElementExtension :=
  BEDC.Derived.AlgebraicExtensionDimensionUp.FiniteAlgebraicElementExtension

/-- BEDC 行级单位谓词；不声称外部多项式环的全部单位分类。 -/
def PolynomialUnitRow (p : Poly) : Prop :=
  PolyEq p polyOne

def PolynomialNonUnitRow (p : Poly) : Prop :=
  PolynomialUnitRow p -> False

def PolynomialProductRow (left right product : Poly) : Prop :=
  PolyEq (polyMul left right) product

def PolynomialDividesRow (factor product : Poly) : Prop :=
  exists cofactor : Poly, PolynomialProductRow factor cofactor product

/--
不可约谓词：一个非单位行的任意公开乘积分解，都有一个单位行。
这是有限 ledger 谓词，不是外部 UFD 或解析因子分解定理。
-/
def IrreduciblePolynomialRow (p : Poly) : Prop :=
  PolynomialNonUnitRow p ∧
    forall left right : Poly,
      PolynomialProductRow left right p ->
        PolynomialUnitRow left ∨ PolynomialUnitRow right

def IsIrreducibleInformationFactor
    {Base : Type u} {Ext : Type v}
    (E : FiniteAlgebraicElementExtension Base Ext)
    (carrierPolynomial factorPolynomial : Poly)
    (atomDimension : Nat) : Prop :=
  atomDimension = E.informationDimension ∧
    PolynomialDividesRow factorPolynomial carrierPolynomial ∧
      IrreduciblePolynomialRow factorPolynomial

/--
一个不可约信息因子绑定到指定扩张与公开 carrier 多项式。
字段只记录可被实例提供的数据，不制造一般因子存在性。
-/
structure IrreducibleInformationFactor
    {Base : Type u} {Ext : Type v}
    (E : FiniteAlgebraicElementExtension Base Ext)
    (carrierPolynomial : Poly) where
  factorPolynomial : Poly
  atomDimension : Nat
  dimension_eq_information :
    atomDimension = E.informationDimension
  divides_carrier :
    PolynomialDividesRow factorPolynomial carrierPolynomial
  irreducible :
    IrreduciblePolynomialRow factorPolynomial

namespace IrreducibleInformationFactor

variable {Base : Type u} {Ext : Type v}
variable {E : FiniteAlgebraicElementExtension Base Ext}
variable {carrierPolynomial : Poly}

theorem is_factor
    (factor : IrreducibleInformationFactor E carrierPolynomial) :
    IsIrreducibleInformationFactor E carrierPolynomial
      factor.factorPolynomial factor.atomDimension := by
  exact And.intro factor.dimension_eq_information
    (And.intro factor.divides_carrier factor.irreducible)

theorem factor_irreducible
    (factor : IrreducibleInformationFactor E carrierPolynomial) :
    IrreduciblePolynomialRow factor.factorPolynomial := by
  exact factor.irreducible

theorem factor_divides_carrier
    (factor : IrreducibleInformationFactor E carrierPolynomial) :
    PolynomialDividesRow factor.factorPolynomial carrierPolynomial := by
  exact factor.divides_carrier

def InformationAtom
    (factor : IrreducibleInformationFactor E carrierPolynomial) : Prop :=
  IrreduciblePolynomialRow factor.factorPolynomial ∧
    factor.atomDimension = E.informationDimension

theorem factor_is_information_atom
    (factor : IrreducibleInformationFactor E carrierPolynomial) :
    factor.InformationAtom := by
  exact And.intro factor.irreducible factor.dimension_eq_information

def SameInformationAtom
    (left right : IrreducibleInformationFactor E carrierPolynomial) : Prop :=
  PolyEq left.factorPolynomial right.factorPolynomial ∧
    left.atomDimension = right.atomDimension

theorem same_atom_refl
    (factor : IrreducibleInformationFactor E carrierPolynomial) :
    SameInformationAtom factor factor := by
  exact And.intro
    (BEDC.Derived.PolynomialUp.PolyEq_refl factor.factorPolynomial)
    rfl

theorem same_atom_symm
    {left right : IrreducibleInformationFactor E carrierPolynomial} :
    SameInformationAtom left right -> SameInformationAtom right left := by
  intro same
  exact And.intro
    (BEDC.Derived.PolynomialUp.PolyEq_symm same.left)
    (Eq.symm same.right)

theorem same_atom_trans
    {left middle right : IrreducibleInformationFactor E carrierPolynomial} :
    SameInformationAtom left middle ->
      SameInformationAtom middle right ->
        SameInformationAtom left right := by
  intro leftMiddle middleRight
  exact And.intro
    (BEDC.Derived.PolynomialUp.PolyEq_trans leftMiddle.left middleRight.left)
    (Eq.trans leftMiddle.right middleRight.right)

end IrreducibleInformationFactor

def CoversSameAtoms
    {Base : Type u} {Ext : Type v}
    {E : FiniteAlgebraicElementExtension Base Ext}
    {carrierPolynomial : Poly}
    (source target : List (IrreducibleInformationFactor E carrierPolynomial)) :
    Prop :=
  forall factor : IrreducibleInformationFactor E carrierPolynomial,
    factor ∈ source ->
      exists listed : IrreducibleInformationFactor E carrierPolynomial,
        listed ∈ target ∧
          IrreducibleInformationFactor.SameInformationAtom factor listed

def SameAtomsUpToOrder
    {Base : Type u} {Ext : Type v}
    {E : FiniteAlgebraicElementExtension Base Ext}
    {carrierPolynomial : Poly}
    (left right : List (IrreducibleInformationFactor E carrierPolynomial)) :
    Prop :=
  CoversSameAtoms left right ∧ CoversSameAtoms right left

inductive AtomAbsent
    {Base : Type u} {Ext : Type v}
    {E : FiniteAlgebraicElementExtension Base Ext}
    {carrierPolynomial : Poly}
    (factor : IrreducibleInformationFactor E carrierPolynomial) :
    List (IrreducibleInformationFactor E carrierPolynomial) -> Prop where
  | nil : AtomAbsent factor []
  | cons {head : IrreducibleInformationFactor E carrierPolynomial}
      {tail : List (IrreducibleInformationFactor E carrierPolynomial)} :
      (IrreducibleInformationFactor.SameInformationAtom factor head -> False) ->
        AtomAbsent factor tail ->
          AtomAbsent factor (head :: tail)

inductive AtomNoDup
    {Base : Type u} {Ext : Type v}
    {E : FiniteAlgebraicElementExtension Base Ext}
    {carrierPolynomial : Poly} :
    List (IrreducibleInformationFactor E carrierPolynomial) -> Prop where
  | nil : AtomNoDup []
  | cons {head : IrreducibleInformationFactor E carrierPolynomial}
      {tail : List (IrreducibleInformationFactor E carrierPolynomial)} :
      AtomAbsent head tail ->
        AtomNoDup tail ->
          AtomNoDup (head :: tail)

/--
公开谱分解 ledger：`complete` 给出该公开候选类型的全覆盖。
因此两个 ledger 的因子表在 `SameInformationAtom` 意义下只差顺序。
-/
structure IrreducibleInformationSpectralFactorization
    {Base : Type u} {Ext : Type v}
    (E : FiniteAlgebraicElementExtension Base Ext)
    (carrierPolynomial : Poly) where
  factors : List (IrreducibleInformationFactor E carrierPolynomial)
  separated : AtomNoDup factors
  sound :
    forall factor : IrreducibleInformationFactor E carrierPolynomial,
      factor ∈ factors ->
        IsIrreducibleInformationFactor E carrierPolynomial
          factor.factorPolynomial factor.atomDimension
  complete :
    forall candidate : IrreducibleInformationFactor E carrierPolynomial,
      exists listed : IrreducibleInformationFactor E carrierPolynomial,
        listed ∈ factors ∧
          IrreducibleInformationFactor.SameInformationAtom candidate listed

namespace IrreducibleInformationSpectralFactorization

variable {Base : Type u} {Ext : Type v}
variable {E : FiniteAlgebraicElementExtension Base Ext}
variable {carrierPolynomial : Poly}

theorem factor_sound
    (ledger : IrreducibleInformationSpectralFactorization E carrierPolynomial)
    {factor : IrreducibleInformationFactor E carrierPolynomial} :
    factor ∈ ledger.factors ->
      IsIrreducibleInformationFactor E carrierPolynomial
        factor.factorPolynomial factor.atomDimension := by
  intro member
  exact ledger.sound factor member

theorem factor_list_nodup
    (ledger : IrreducibleInformationSpectralFactorization E carrierPolynomial) :
    AtomNoDup ledger.factors := by
  exact ledger.separated

theorem covers_any_other_complete_ledger
    (left right :
      IrreducibleInformationSpectralFactorization E carrierPolynomial) :
    CoversSameAtoms left.factors right.factors := by
  intro factor _member
  exact right.complete factor

theorem factor_unique_up_to_order
    (left right :
      IrreducibleInformationSpectralFactorization E carrierPolynomial) :
    SameAtomsUpToOrder left.factors right.factors := by
  exact And.intro
    (covers_any_other_complete_ledger left right)
    (covers_any_other_complete_ledger right left)

end IrreducibleInformationSpectralFactorization

theorem factor_irreducible
    {Base : Type u} {Ext : Type v}
    {E : FiniteAlgebraicElementExtension Base Ext}
    {carrierPolynomial : Poly}
    (factor : IrreducibleInformationFactor E carrierPolynomial) :
    IrreduciblePolynomialRow factor.factorPolynomial := by
  exact factor.factor_irreducible

theorem factor_is_information_atom
    {Base : Type u} {Ext : Type v}
    {E : FiniteAlgebraicElementExtension Base Ext}
    {carrierPolynomial : Poly}
    (factor : IrreducibleInformationFactor E carrierPolynomial) :
    factor.InformationAtom := by
  exact factor.factor_is_information_atom

theorem factor_unique_up_to_order
    {Base : Type u} {Ext : Type v}
    {E : FiniteAlgebraicElementExtension Base Ext}
    {carrierPolynomial : Poly}
    (left right :
      IrreducibleInformationSpectralFactorization E carrierPolynomial) :
    SameAtomsUpToOrder left.factors right.factors := by
  exact
    IrreducibleInformationSpectralFactorization.factor_unique_up_to_order
      left right

end BEDC.Derived.RHRoute.IrreducibleInformationSpectralFactor
