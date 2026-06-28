import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.PrimeSkewDefect

namespace BEDC.Derived.RHRoute.OddZeroDefect

open BEDC.Derived.RHRoute.PrimeSkewDefect
open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RationalUp

universe u v

abbrev RatNum := BEDC.Derived.RationalUp.RatNum
abbrev RatComplex := BEDC.Derived.RHRoute.ConstructiveRHStatement.RatComplex

/-!
奇宇称只读有限层号。它不声称几何、能量或谱结论。
-/
inductive NatParity where
  | even
  | odd

namespace NatParity

def flip : NatParity -> NatParity
  | NatParity.even => NatParity.odd
  | NatParity.odd => NatParity.even

theorem flip_even : flip NatParity.even = NatParity.odd := by
  rfl

theorem flip_odd : flip NatParity.odd = NatParity.even := by
  rfl

end NatParity

def natParity : Nat -> NatParity
  | 0 => NatParity.even
  | Nat.succ n => NatParity.flip (natParity n)

def IsEvenParity (n : Nat) : Prop :=
  natParity n = NatParity.even

def IsOddParity (n : Nat) : Prop :=
  natParity n = NatParity.odd

theorem zero_evenParity : IsEvenParity 0 := by
  rfl

theorem one_oddParity : IsOddParity 1 := by
  rfl

theorem succ_evenParity_to_oddParity {n : Nat} :
    IsEvenParity n -> IsOddParity (Nat.succ n) := by
  intro even
  unfold IsEvenParity at even
  unfold IsOddParity natParity
  rw [even]
  rfl

theorem succ_oddParity_to_evenParity {n : Nat} :
    IsOddParity n -> IsEvenParity (Nat.succ n) := by
  intro odd
  unfold IsOddParity at odd
  unfold IsEvenParity natParity
  rw [odd]
  rfl

theorem oddParity_not_evenParity {n : Nat} :
    IsOddParity n -> IsEvenParity n -> False := by
  intro odd even
  unfold IsOddParity at odd
  unfold IsEvenParity at even
  rw [even] at odd
  cases odd

theorem evenParity_not_oddParity {n : Nat} :
    IsEvenParity n -> IsOddParity n -> False := by
  intro even odd
  exact oddParity_not_evenParity odd even

/-!
奇缺陷是已有 `PrimeDefect` 的有限 selected row 加一条奇层号读回。
-/
structure OddPrimeDefect (Bulk : Type u) (x : Bulk) where
  defect : PrimeDefect Bulk x
  selected_layer_odd : IsOddParity defect.selected.layer

namespace OddPrimeDefect

def selectedRow {Bulk : Type u} {x : Bulk}
    (defect : OddPrimeDefect Bulk x) : PrimeDefectRow :=
  defect.defect.selected

def defectQuantum {Bulk : Type u} {x : Bulk}
    (defect : OddPrimeDefect Bulk x) : RatNum :=
  defect.selectedRow.defect_quantum

theorem selected_mem {Bulk : Type u} {x : Bulk}
    (defect : OddPrimeDefect Bulk x) :
    defect.selectedRow ∈ defect.defect.rows := by
  exact defect.defect.selected_mem

theorem selected_layer_is_odd {Bulk : Type u} {x : Bulk}
    (defect : OddPrimeDefect Bulk x) :
    IsOddParity defect.selectedRow.layer := by
  exact defect.selected_layer_odd

theorem defectQuantum_apart_zero {Bulk : Type u} {x : Bulk}
    (defect : OddPrimeDefect Bulk x) :
    ratApart0 defect.defectQuantum := by
  exact defect.selectedRow.defect_apart_zero

end OddPrimeDefect

def OddDefectZeroIncompatibility
    (I : PrimeSkewDefectInterface.{u, v}) : Prop :=
  (x : I.bulk) ->
    I.zero_atom x ->
      OddPrimeDefect I.bulk x ->
        False

def NoOddZeroDefect (I : PrimeSkewDefectInterface.{u, v}) : Prop :=
  OddDefectZeroIncompatibility I

def PrimeSieveOddExactness
    (I : PrimeSkewDefectInterface.{u, v}) : Prop :=
  OddDefectZeroIncompatibility I

theorem noOddZeroDefect_to_primeSieveOddExactness
    {I : PrimeSkewDefectInterface.{u, v}} :
    NoOddZeroDefect I -> PrimeSieveOddExactness I := by
  intro h
  exact h

theorem primeSieveOddExactness_to_noOddZeroDefect
    {I : PrimeSkewDefectInterface.{u, v}} :
    PrimeSieveOddExactness I -> NoOddZeroDefect I := by
  intro h
  exact h

theorem primeDefectZeroIncompatibility_to_odd
    {I : PrimeSkewDefectInterface.{u, v}}
    (incompatible : PrimeDefectZeroIncompatibility I) :
    OddDefectZeroIncompatibility I := by
  intro x zero oddDefect
  exact incompatible x zero oddDefect.defect

structure LocatedOddPrimeSkewDefect
    (I : PrimeSkewDefectInterface.{u, v}) where
  point : I.bulk
  zero : I.zero_atom point
  skew : PrimeSkewCertificate (I.channels point)
  odd_defect : OddPrimeDefect I.bulk point

structure OddZeroDefect
    (I : PrimeSkewDefectInterface.{u, v}) where
  point : I.bulk
  zero : I.zero_atom point
  skew : PrimeSkewCertificate (I.channels point)
  odd_defect : OddPrimeDefect I.bulk point

def locatedOddPrimeSkewDefect_to_formula
    {I : PrimeSkewDefectInterface.{u, v}}
    (w : LocatedOddPrimeSkewDefect I) :
    OddZeroDefect I where
  point := w.point
  zero := w.zero
  skew := w.skew
  odd_defect := w.odd_defect

def locatedOddPrimeSkewDefect_of_formula
    {I : PrimeSkewDefectInterface.{u, v}}
    (h : OddZeroDefect I) :
    LocatedOddPrimeSkewDefect I where
  point := h.point
  zero := h.zero
  skew := h.skew
  odd_defect := h.odd_defect

def oddZeroDefect_refutes_noOddZeroDefect
    {I : PrimeSkewDefectInterface.{u, v}}
    (h : OddZeroDefect I)
    (exactness : NoOddZeroDefect I) :
    False :=
  exactness h.point h.zero h.odd_defect

structure OddBoundaryFaithfulness
    (I : PrimeSkewDefectInterface.{u, v}) where
  detects :
    (x : I.bulk) ->
      I.zero_atom x ->
        PrimeSkewCertificate (I.channels x) ->
          OddPrimeDefect I.bulk x

theorem located_skew_refutes_odd_faithfulness
    {I : PrimeSkewDefectInterface.{u, v}}
    (cert : LocatedPrimeSkewCertificate I)
    (incompatible : OddDefectZeroIncompatibility I) :
    OddBoundaryFaithfulness I -> False := by
  intro faithful
  exact incompatible cert.point cert.zero
    (faithful.detects cert.point cert.zero cert.skew)

structure OffLineOddZeroDefect
    {I : PrimeSkewDefectInterface.{u, v}}
    (obligation : OffLineZeroBoundaryObligation I) where
  zero : obligation.off_line_zero
  odd_defect : OddPrimeDefect I.bulk (obligation.locate zero)

namespace OffLineOddZeroDefect

def zeroAtom {I : PrimeSkewDefectInterface.{u, v}}
    {obligation : OffLineZeroBoundaryObligation I}
    (w : OffLineOddZeroDefect obligation) :
    I.zero_atom (obligation.locate w.zero) :=
  obligation.zero_atom_at w.zero

def skewCertificate {I : PrimeSkewDefectInterface.{u, v}}
    {obligation : OffLineZeroBoundaryObligation I}
    (w : OffLineOddZeroDefect obligation) :
    PrimeSkewCertificate (I.channels (obligation.locate w.zero)) :=
  obligation.off_line_to_prime_skew_boundary_obligation w.zero

def selectedQuantum {I : PrimeSkewDefectInterface.{u, v}}
    {obligation : OffLineZeroBoundaryObligation I}
    (w : OffLineOddZeroDefect obligation) : RatNum :=
  w.odd_defect.defectQuantum

theorem selected_layer_odd {I : PrimeSkewDefectInterface.{u, v}}
    {obligation : OffLineZeroBoundaryObligation I}
    (w : OffLineOddZeroDefect obligation) :
    IsOddParity w.odd_defect.selectedRow.layer := by
  exact w.odd_defect.selected_layer_is_odd

theorem selectedQuantum_apart_zero
    {I : PrimeSkewDefectInterface.{u, v}}
    {obligation : OffLineZeroBoundaryObligation I}
    (w : OffLineOddZeroDefect obligation) :
    ratApart0 w.selectedQuantum := by
  exact w.odd_defect.defectQuantum_apart_zero

end OffLineOddZeroDefect

structure OffLineOddZeroDefectFormula
    {I : PrimeSkewDefectInterface.{u, v}}
    (obligation : OffLineZeroBoundaryObligation I) where
  zero : obligation.off_line_zero
  odd_defect : OddPrimeDefect I.bulk (obligation.locate zero)

def offLineOddZeroDefect_to_formula
    {I : PrimeSkewDefectInterface.{u, v}}
    {obligation : OffLineZeroBoundaryObligation I}
    (w : OffLineOddZeroDefect obligation) :
    OffLineOddZeroDefectFormula obligation where
  zero := w.zero
  odd_defect := w.odd_defect

def offLineOddZeroDefect_of_formula
    {I : PrimeSkewDefectInterface.{u, v}}
    {obligation : OffLineZeroBoundaryObligation I}
    (h : OffLineOddZeroDefectFormula obligation) :
    OffLineOddZeroDefect obligation where
  zero := h.zero
  odd_defect := h.odd_defect

def oddBoundaryFaithfulness_to_offLineOddZeroDefect
    {I : PrimeSkewDefectInterface.{u, v}}
    (obligation : OffLineZeroBoundaryObligation I)
    (faithful : OddBoundaryFaithfulness I)
    (z : obligation.off_line_zero) :
    OffLineOddZeroDefect obligation where
  zero := z
  odd_defect :=
    faithful.detects (obligation.locate z)
      (obligation.zero_atom_at z)
      (obligation.off_line_to_prime_skew_boundary_obligation z)

theorem offLineOddBoundary_obligation_refutes_faithfulness
    {I : PrimeSkewDefectInterface.{u, v}}
    (obligation : OffLineZeroBoundaryObligation I)
    (incompatible : OddDefectZeroIncompatibility I)
    (z : obligation.off_line_zero) :
    OddBoundaryFaithfulness I -> False := by
  intro faithful
  exact incompatible (obligation.locate z)
    (obligation.zero_atom_at z)
    (faithful.detects (obligation.locate z)
      (obligation.zero_atom_at z)
      (obligation.off_line_to_prime_skew_boundary_obligation z))

def offCriticalLineZero (s : RatComplex) : Prop :=
  NontrivialZetaZero s ∧ (OnCriticalLine s -> False)

structure OffCriticalLineOddDefect
    (I : PrimeSkewDefectInterface.{u, v})
    (read : I.bulk -> RatComplex) where
  point : I.bulk
  zero : I.zero_atom point
  off_line : offCriticalLineZero (read point)
  odd_defect : OddPrimeDefect I.bulk point

def offCriticalLineOddDefect_to_oddZeroDefect
    {I : PrimeSkewDefectInterface.{u, v}}
    {read : I.bulk -> RatComplex}
    (skew_at :
      (point : I.bulk) ->
        I.zero_atom point ->
          PrimeSkewCertificate (I.channels point))
    (h : OffCriticalLineOddDefect I read) :
    OddZeroDefect I where
  point := h.point
  zero := h.zero
  skew := skew_at h.point h.zero
  odd_defect := h.odd_defect

end BEDC.Derived.RHRoute.OddZeroDefect
