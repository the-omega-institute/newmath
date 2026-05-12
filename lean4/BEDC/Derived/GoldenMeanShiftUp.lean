import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GoldenMeanShiftUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GoldenMeanShiftCarrier [AskSetup] [PackageSetup]
    (window zeroWitness adjacencyLedger provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory window ∧ UnaryHistory zeroWitness ∧ UnaryHistory adjacencyLedger ∧
    UnaryHistory provenance ∧ UnaryHistory ledger ∧ Cont window zeroWitness adjacencyLedger ∧
      Cont adjacencyLedger provenance ledger ∧ Cont ledger zeroWitness endpoint ∧
        PkgSig bundle endpoint pkg

theorem GoldenMeanShiftCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {window zeroWitness adjacencyLedger provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GoldenMeanShiftCarrier window zeroWitness adjacencyLedger provenance ledger endpoint
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          GoldenMeanShiftCarrier window zeroWitness adjacencyLedger provenance ledger endpoint
            bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          GoldenMeanShiftCarrier window zeroWitness adjacencyLedger provenance ledger endpoint
            bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          GoldenMeanShiftCarrier window zeroWitness adjacencyLedger provenance ledger endpoint
            bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.GoldenMeanShiftUp
