import BEDC.Derived.RHRoute.OCLSDPhaseAlgebra
import BEDC.Derived.RHRoute.ConstructiveRHStatement

namespace BEDC.Derived.RHRoute.PZGProjectionZeroLedger

open BEDC.Derived.RHRoute.OCLSDPhaseAlgebra

universe u

abbrev PZGRow :=
  BEDC.Derived.RHRoute.OCLSDPhaseAlgebra.PZGRow

theorem pzg_nil_ne_cons (p k : Nat) (rest : PZGRow) :
    PZGRow.nil = PZGRow.cons p k rest -> False := by
  intro h
  cases h

theorem pzg_cons_ne_nil (p k : Nat) (rest : PZGRow) :
    PZGRow.cons p k rest = PZGRow.nil -> False := by
  intro h
  cases h

theorem pzg_cons_injective
    {p q k l : Nat} {left right : PZGRow} :
    PZGRow.cons p k left = PZGRow.cons q l right ->
      p = q /\ k = l /\ left = right := by
  intro h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/--
A forget-label row records the distinction between the tagged PZG basis and the
projected scalar surface.  Every basis tag has the same projected basis readout;
the tag itself is retained only in the source layer.
-/
structure ForgetLabelBasisReadout (Scalar : Type u) where
  one : Scalar
  basisReadout : PZGRow -> Scalar
  basisReadout_forgets_label :
    (row : PZGRow) -> basisReadout row = one

theorem forgetLabel_basis_same
    {Scalar : Type u} (R : ForgetLabelBasisReadout Scalar)
    (left right : PZGRow) :
    R.basisReadout left = R.basisReadout right := by
  rw [R.basisReadout_forgets_label left,
    R.basisReadout_forgets_label right]

/--
The projected value is deliberately abstract: it may be a finite readout, a
regularized value row, or a located evaluator row.  The only built-in fact is
that the empty PZG coefficient is nonzero, so the tagged vector itself is not
the zero vector.
-/
structure PZGProjectionReadout (Scalar : Type u) extends
    ForgetLabelBasisReadout Scalar where
  coefficient : PZGRow -> Scalar
  projectionValue : Scalar
  zero : Scalar -> Prop
  nonzero : Scalar -> Prop
  zero_refutes_nonzero :
    {x : Scalar} -> zero x -> nonzero x -> False
  empty_coeff_nonzero : nonzero (coefficient PZGRow.nil)

def TaggedVectorNonzero
    {Scalar : Type u} (R : PZGProjectionReadout Scalar) : Prop :=
  Exists (fun row : PZGRow => R.nonzero (R.coefficient row))

theorem taggedVectorNonzero_empty
    {Scalar : Type u} (R : PZGProjectionReadout Scalar) :
    TaggedVectorNonzero R := by
  exact Exists.intro PZGRow.nil R.empty_coeff_nonzero

theorem taggedVectorNotAllZero
    {Scalar : Type u} (R : PZGProjectionReadout Scalar) :
    ((row : PZGRow) -> R.zero (R.coefficient row)) -> False := by
  intro allZero
  exact R.zero_refutes_nonzero (allZero PZGRow.nil)
    R.empty_coeff_nonzero

def ForgetLabelProjectionZero
    {Scalar : Type u} (R : PZGProjectionReadout Scalar) : Prop :=
  R.zero R.projectionValue

structure PZGProjectionKernelEvent
    {Scalar : Type u} (R : PZGProjectionReadout Scalar) where
  projection_zero : ForgetLabelProjectionZero R
  tagged_nonzero : TaggedVectorNonzero R

def projectionKernelEvent_of_projection_zero
    {Scalar : Type u} {R : PZGProjectionReadout Scalar}
    (projection_zero : ForgetLabelProjectionZero R) :
    PZGProjectionKernelEvent R where
  projection_zero := projection_zero
  tagged_nonzero := taggedVectorNonzero_empty R

theorem projectionKernelEvent_tagged_not_all_zero
    {Scalar : Type u} {R : PZGProjectionReadout Scalar}
    (_event : PZGProjectionKernelEvent R) :
    ((row : PZGRow) -> R.zero (R.coefficient row)) -> False :=
  taggedVectorNotAllZero R

structure PZGNoResidualObligations
    {Scalar : Type u} (R : PZGProjectionReadout Scalar) where
  localLedgerClosed : Prop
  noHiddenRegister : Prop
  analyticContinuationPreservesGerm : Prop
  noItemScaleInverseRegister : Prop
  archimedeanLedgerSeparate : Prop

structure PZGNoResidualLedger
    {Scalar : Type u} (R : PZGProjectionReadout Scalar) where
  obligations : PZGNoResidualObligations R
  localLedgerClosed : obligations.localLedgerClosed
  noHiddenRegister : obligations.noHiddenRegister
  analyticContinuationPreservesGerm :
    obligations.analyticContinuationPreservesGerm
  noItemScaleInverseRegister : obligations.noItemScaleInverseRegister
  archimedeanLedgerSeparate : obligations.archimedeanLedgerSeparate

structure PZGOntologicalZero
    {Scalar : Type u} (R : PZGProjectionReadout Scalar) where
  projection_event : PZGProjectionKernelEvent R
  no_residual : PZGNoResidualLedger R

def ontologicalZero_of_projection_zero
    {Scalar : Type u} {R : PZGProjectionReadout Scalar}
    (projection_zero : ForgetLabelProjectionZero R)
    (no_residual : PZGNoResidualLedger R) :
    PZGOntologicalZero R where
  projection_event := projectionKernelEvent_of_projection_zero projection_zero
  no_residual := no_residual

theorem ontologicalZero_projection_zero
    {Scalar : Type u} {R : PZGProjectionReadout Scalar}
    (zero : PZGOntologicalZero R) :
    ForgetLabelProjectionZero R :=
  zero.projection_event.projection_zero

theorem ontologicalZero_tagged_nonzero
    {Scalar : Type u} {R : PZGProjectionReadout Scalar}
    (zero : PZGOntologicalZero R) :
    TaggedVectorNonzero R :=
  zero.projection_event.tagged_nonzero

theorem ontologicalZero_tagged_not_all_zero
    {Scalar : Type u} {R : PZGProjectionReadout Scalar}
    (_zero : PZGOntologicalZero R) :
    ((row : PZGRow) -> R.zero (R.coefficient row)) -> False :=
  taggedVectorNotAllZero R

theorem ontologicalZero_no_hidden_register
    {Scalar : Type u} {R : PZGProjectionReadout Scalar}
    (zero : PZGOntologicalZero R) :
    zero.no_residual.obligations.noHiddenRegister :=
  zero.no_residual.noHiddenRegister

theorem ontologicalZero_preserves_germ
    {Scalar : Type u} {R : PZGProjectionReadout Scalar}
    (zero : PZGOntologicalZero R) :
    zero.no_residual.obligations.analyticContinuationPreservesGerm :=
  zero.no_residual.analyticContinuationPreservesGerm

theorem ontologicalZero_no_item_scale_inverse
    {Scalar : Type u} {R : PZGProjectionReadout Scalar}
    (zero : PZGOntologicalZero R) :
    zero.no_residual.obligations.noItemScaleInverseRegister :=
  zero.no_residual.noItemScaleInverseRegister

theorem ontologicalZero_archimedean_separate
    {Scalar : Type u} {R : PZGProjectionReadout Scalar}
    (zero : PZGOntologicalZero R) :
    zero.no_residual.obligations.archimedeanLedgerSeparate :=
  zero.no_residual.archimedeanLedgerSeparate

abbrev RatComplex :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.RatComplex

abbrev NontrivialZetaZero :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.NontrivialZetaZero

/--
Located zeta zero data can be related to a PZG projection-kernel event only by
supplying the projection and no-residual ledgers.  This carrier does not assert
that every zeta zero has such a witness.
-/
structure ZetaPZGOntologicalZero
    (s : RatComplex) {Scalar : Type u}
    (R : PZGProjectionReadout Scalar) where
  zeta_zero : NontrivialZetaZero s
  pzg_zero : PZGOntologicalZero R

theorem zetaPZGOntologicalZero_projection_zero
    {s : RatComplex} {Scalar : Type u}
    {R : PZGProjectionReadout Scalar}
    (zero : ZetaPZGOntologicalZero s R) :
    ForgetLabelProjectionZero R :=
  ontologicalZero_projection_zero zero.pzg_zero

theorem zetaPZGOntologicalZero_tagged_not_all_zero
    {s : RatComplex} {Scalar : Type u}
    {R : PZGProjectionReadout Scalar}
    (_zero : ZetaPZGOntologicalZero s R) :
    ((row : PZGRow) -> R.zero (R.coefficient row)) -> False :=
  taggedVectorNotAllZero R

end BEDC.Derived.RHRoute.PZGProjectionZeroLedger
