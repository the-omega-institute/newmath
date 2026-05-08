import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ChernWeilUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ChernWeilSourceEnvelope
    (curvature derham provenance connectionFace characteristic : BHist) : Prop :=
  UnaryHistory curvature ∧ UnaryHistory derham ∧ UnaryHistory provenance ∧
    Cont curvature derham provenance ∧ Cont provenance connectionFace characteristic ∧
      hsame characteristic (append provenance connectionFace)

theorem ChernWeilSourceEnvelope_rows
    {curvature derham provenance connectionFace characteristic : BHist} :
    ChernWeilSourceEnvelope curvature derham provenance connectionFace characteristic ->
      UnaryHistory curvature ∧ UnaryHistory derham ∧ Cont curvature derham provenance ∧
        Cont provenance connectionFace characteristic ∧
          hsame characteristic (append provenance connectionFace) := by
  intro envelope
  exact
    And.intro envelope.left
      (And.intro envelope.right.left
        (And.intro envelope.right.right.right.left
          (And.intro envelope.right.right.right.right.left
            envelope.right.right.right.right.right)))

end BEDC.Derived.ChernWeilUp
