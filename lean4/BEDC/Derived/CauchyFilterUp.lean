import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyFilterPacket [AskSetup] [PackageSetup]
    (stream directed threshold endpoint compat transport consumer provenance namecert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory directed ∧ UnaryHistory threshold ∧
    UnaryHistory endpoint ∧ UnaryHistory compat ∧ UnaryHistory transport ∧
      UnaryHistory consumer ∧ UnaryHistory provenance ∧ UnaryHistory namecert ∧
        PkgSig bundle provenance pkg

theorem CauchyFilterPacket_common_refinement_classifier [AskSetup] [PackageSetup]
    {stream directed threshold endpoint compat transport consumer provenance namecert left right
      common : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterPacket stream directed threshold endpoint compat transport consumer provenance
        namecert bundle pkg →
      Cont directed threshold left →
        Cont endpoint compat right →
          Cont left right common →
            UnaryHistory stream ∧ UnaryHistory directed ∧ UnaryHistory threshold ∧
              UnaryHistory endpoint ∧ UnaryHistory compat ∧ UnaryHistory transport ∧
                UnaryHistory consumer ∧ UnaryHistory provenance ∧ UnaryHistory namecert ∧
                  Cont directed threshold left ∧ Cont endpoint compat right ∧
                    Cont left right common ∧ hsame common (append left right) ∧
                      PkgSig bundle provenance pkg := by
  intro packet leftRow rightRow commonRow
  obtain ⟨streamUnary, directedUnary, thresholdUnary, endpointUnary, compatUnary,
    transportUnary, consumerUnary, provenanceUnary, namecertUnary, pkgRow⟩ := packet
  exact
    ⟨streamUnary, directedUnary, thresholdUnary, endpointUnary, compatUnary, transportUnary,
      consumerUnary, provenanceUnary, namecertUnary, leftRow, rightRow, commonRow, commonRow,
      pkgRow⟩

end BEDC.Derived.CauchyFilterUp
