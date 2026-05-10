import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.InterpolationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem InterpolationSampleLedger_surface [AskSetup] [PackageSetup]
    {finsetMembership polynomialEval node target polynomial sampleLedger endpoint provenance :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory finsetMembership -> UnaryHistory polynomialEval -> UnaryHistory node ->
      UnaryHistory target -> UnaryHistory polynomial ->
        Cont finsetMembership polynomialEval sampleLedger -> Cont node target endpoint ->
          Cont endpoint polynomial provenance -> SigRel bundle sampleLedger provenance ->
            PkgSig bundle provenance pkg ->
              UnaryHistory sampleLedger ∧ UnaryHistory endpoint ∧ UnaryHistory provenance ∧
                hsame sampleLedger (append finsetMembership polynomialEval) ∧
                  hsame endpoint (append node target) ∧
                    hsame provenance (append endpoint polynomial) ∧
                      SigRel bundle sampleLedger provenance ∧ PkgSig bundle provenance pkg := by
  intro finsetUnary polynomialEvalUnary nodeUnary targetUnary polynomialUnary sampleLedgerRow
  intro endpointRow provenanceRow sigRel pkgSig
  have sampleLedgerUnary : UnaryHistory sampleLedger :=
    unary_cont_closed finsetUnary polynomialEvalUnary sampleLedgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed nodeUnary targetUnary endpointRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed endpointUnary polynomialUnary provenanceRow
  exact
    ⟨sampleLedgerUnary, endpointUnary, provenanceUnary, sampleLedgerRow, endpointRow,
      provenanceRow, sigRel, pkgSig⟩

end BEDC.Derived.InterpolationUp
