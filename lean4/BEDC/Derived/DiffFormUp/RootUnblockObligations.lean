import BEDC.Derived.DiffFormUp.WedgeProbeConcatenation
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormRootUnblock_wedge_cont_closure
    {d e out leftLedger rightLedger tensorLedger : BHist}
    {left right : ProbeBundle BHist} :
    DiffFormWedgeProbeConcatenationLedger left right leftLedger rightLedger tensorLedger ->
      DiffFormWedgeDegreeLedger d e out leftLedger rightLedger tensorLedger ->
        DegreeProbeAligned d left -> DegreeProbeAligned e right ->
          DegreeProbeAligned out (bundleAppend left right) ∧
            bundleLength (bundleAppend left right) = bundleLength left + bundleLength right ∧
              (forall probe : BHist,
                InBundle probe (bundleAppend left right) <->
                  InBundle probe left ∨ InBundle probe right) ∧
                UnaryHistory out ∧ hsame tensorLedger (append leftLedger rightLedger) ∧
                  hsame leftLedger rightLedger := by
  intro probeLedger degreeLedger leftAligned rightAligned
  have coverage := DiffFormWedgeProbeConcatenationLedger_coverage probeLedger
  have alignedOut : DegreeProbeAligned out (bundleAppend left right) :=
    DiffFormDegreeProbeAligned_bundleAppend_cont leftAligned rightAligned
      degreeLedger.right.right.left
  exact
    ⟨alignedOut,
      coverage.left,
      coverage.right.left,
      degreeLedger.right.right.right.left,
      coverage.right.right.right,
      degreeLedger.right.right.right.right.right⟩

end BEDC.Derived.DiffFormUp
