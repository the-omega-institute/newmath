import BEDC.Derived.ComplexDifferentiabilityUp.ObligationSurface

namespace BEDC.Derived.ComplexDifferentiabilityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexDiffUp

theorem CplxDiffTransportLedger_obligation_surface {f z z' fp gp pattern : BHist} :
    CplxDiffAt f z fp -> hsame z z' -> hsame fp gp ->
      CplxDiffPatternSpec f z pattern ->
        CplxDiffAt f z' gp ∧
          (exists h q : BHist, CplxDiffQuot f z' h q ∧ Cont f h q ∧ hsame q gp) ∧
            CplxDiffLedgerPolicy f z fp ∧
              (exists h q : BHist,
                CplxDiffQuot f z h q ∧ Cont h q pattern ∧ CplxNonZero h ∧
                  UnaryHistory h ∧ UnaryHistory q ∧ (hsame q BHist.Empty -> False)) := by
  intro diff sameZ sameFpGp patternSpec
  have transported := CplxDiffAt_hsame_transport_witness diff sameZ sameFpGp
  have ledgerPolicy : CplxDiffLedgerPolicy f z fp :=
    CplxDiffLedgerPolicy_of_diff diff
  have patternRows :=
    CplxDiffPatternSpec_obligation_surface patternSpec
  exact And.intro transported.left
    (And.intro transported.right
      (And.intro ledgerPolicy patternRows))

end BEDC.Derived.ComplexDifferentiabilityUp
