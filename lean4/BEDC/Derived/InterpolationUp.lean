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

theorem InterpolationEvaluationLedger_transport [AskSetup] [PackageSetup]
    {finsetMembership polynomialEval node target polynomial sampleLedger endpoint provenance
      sampleLedger' endpoint' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory finsetMembership -> UnaryHistory polynomialEval -> UnaryHistory node ->
      UnaryHistory target -> UnaryHistory polynomial ->
        Cont finsetMembership polynomialEval sampleLedger -> Cont node target endpoint ->
          Cont endpoint polynomial provenance ->
            Cont finsetMembership polynomialEval sampleLedger' -> Cont node target endpoint' ->
              Cont endpoint' polynomial provenance' -> SigRel bundle sampleLedger provenance ->
                PkgSig bundle provenance pkg ->
                  UnaryHistory sampleLedger' ∧ UnaryHistory endpoint' ∧
                    UnaryHistory provenance' ∧ hsame sampleLedger sampleLedger' ∧
                      hsame endpoint endpoint' ∧ hsame provenance provenance' := by
  intro finsetUnary polynomialEvalUnary nodeUnary targetUnary polynomialUnary sampleLedgerRow
  intro endpointRow provenanceRow sampleLedgerRow' endpointRow' provenanceRow' _sigRel _pkgSig
  have sampleLedgerUnary' : UnaryHistory sampleLedger' :=
    unary_cont_closed finsetUnary polynomialEvalUnary sampleLedgerRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed nodeUnary targetUnary endpointRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed endpointUnary' polynomialUnary provenanceRow'
  have sameSampleLedger : hsame sampleLedger sampleLedger' :=
    cont_respects_hsame (hsame_refl finsetMembership) (hsame_refl polynomialEval)
      sampleLedgerRow sampleLedgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl node) (hsame_refl target) endpointRow endpointRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameEndpoint (hsame_refl polynomial) provenanceRow provenanceRow'
  exact
    ⟨sampleLedgerUnary', endpointUnary', provenanceUnary', sameSampleLedger, sameEndpoint,
      sameProvenance⟩

theorem InterpolationNameCert_obligation_surface [AskSetup] [PackageSetup]
    {finsetMembership polynomialEval node target polynomial sampleLedger endpoint provenance
      certificateSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory finsetMembership -> UnaryHistory polynomialEval -> UnaryHistory node ->
      UnaryHistory target -> UnaryHistory polynomial ->
        Cont finsetMembership polynomialEval sampleLedger -> Cont node target endpoint ->
          Cont endpoint polynomial provenance -> Cont sampleLedger provenance certificateSurface ->
            SigRel bundle sampleLedger provenance -> PkgSig bundle provenance pkg ->
              UnaryHistory certificateSurface ∧
                hsame certificateSurface (append sampleLedger provenance) ∧
                  SigRel bundle sampleLedger provenance ∧ PkgSig bundle provenance pkg := by
  intro finsetUnary polynomialEvalUnary nodeUnary targetUnary polynomialUnary sampleLedgerRow
  intro endpointRow provenanceRow certificateRow sigRel pkgSig
  have sampleSurface :=
    InterpolationSampleLedger_surface finsetUnary polynomialEvalUnary nodeUnary targetUnary
      polynomialUnary sampleLedgerRow endpointRow provenanceRow sigRel pkgSig
  have certificateUnary : UnaryHistory certificateSurface :=
    unary_cont_closed sampleSurface.left sampleSurface.right.right.left certificateRow
  exact ⟨certificateUnary, certificateRow, sigRel, pkgSig⟩

theorem InterpolationEvaluationLedger_sample_transport [AskSetup] [PackageSetup]
    {finsetMembership finsetMembership' polynomialEval polynomialEval' node node' target target'
      polynomial polynomial' sampleLedger sampleLedger' endpoint endpoint' provenance
      provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory finsetMembership -> UnaryHistory polynomialEval -> UnaryHistory node ->
      UnaryHistory target -> UnaryHistory polynomial ->
        Cont finsetMembership polynomialEval sampleLedger -> Cont node target endpoint ->
          Cont endpoint polynomial provenance -> SigRel bundle sampleLedger provenance ->
            PkgSig bundle provenance pkg -> hsame finsetMembership finsetMembership' ->
              hsame polynomialEval polynomialEval' -> hsame node node' -> hsame target target' ->
                hsame polynomial polynomial' ->
                  Cont finsetMembership' polynomialEval' sampleLedger' ->
                    Cont node' target' endpoint' -> Cont endpoint' polynomial' provenance' ->
                      SigRel bundle sampleLedger' provenance' ->
                        PkgSig bundle provenance' pkg ->
                          UnaryHistory sampleLedger' ∧ UnaryHistory endpoint' ∧
                            UnaryHistory provenance' ∧ hsame sampleLedger sampleLedger' ∧
                              hsame endpoint endpoint' ∧ hsame provenance provenance' ∧
                                SigRel bundle sampleLedger' provenance' ∧
                                  PkgSig bundle provenance' pkg := by
  intro finsetUnary polynomialEvalUnary nodeUnary targetUnary polynomialUnary sampleLedgerRow
  intro endpointRow provenanceRow sigRel pkgSig sameMembership sameEval sameNode sameTarget
  intro samePolynomial sampleLedgerRow' endpointRow' provenanceRow' sigRel' pkgSig'
  have finsetUnary' : UnaryHistory finsetMembership' :=
    unary_transport finsetUnary sameMembership
  have polynomialEvalUnary' : UnaryHistory polynomialEval' :=
    unary_transport polynomialEvalUnary sameEval
  have nodeUnary' : UnaryHistory node' :=
    unary_transport nodeUnary sameNode
  have targetUnary' : UnaryHistory target' :=
    unary_transport targetUnary sameTarget
  have polynomialUnary' : UnaryHistory polynomial' :=
    unary_transport polynomialUnary samePolynomial
  have sampleLedgerUnary' : UnaryHistory sampleLedger' :=
    unary_cont_closed finsetUnary' polynomialEvalUnary' sampleLedgerRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed nodeUnary' targetUnary' endpointRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed endpointUnary' polynomialUnary' provenanceRow'
  have sampleLedgerSame : hsame sampleLedger sampleLedger' :=
    cont_respects_hsame sameMembership sameEval sampleLedgerRow sampleLedgerRow'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame sameNode sameTarget endpointRow endpointRow'
  have provenanceSame : hsame provenance provenance' :=
    cont_respects_hsame endpointSame samePolynomial provenanceRow provenanceRow'
  exact
    ⟨sampleLedgerUnary', endpointUnary', provenanceUnary', sampleLedgerSame, endpointSame,
      provenanceSame, sigRel', pkgSig'⟩

theorem InterpolationEvaluationLedger_stability [AskSetup] [PackageSetup]
    {node target polynomial node' target' polynomial' sample sample' endpoint endpoint'
      provenance provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory node -> UnaryHistory target -> UnaryHistory polynomial ->
      Cont node target endpoint -> Cont endpoint polynomial provenance ->
        Cont node' target' endpoint' -> Cont endpoint' polynomial' provenance' ->
          hsame node node' -> hsame target target' -> hsame polynomial polynomial' ->
            hsame sample endpoint -> hsame sample' endpoint' ->
              SigRel bundle sample provenance -> PkgSig bundle provenance pkg ->
                UnaryHistory endpoint' ∧ UnaryHistory provenance' ∧ hsame sample sample' ∧
                  hsame provenance provenance' ∧ SigRel bundle sample provenance ∧
                    PkgSig bundle provenance pkg := by
  intro nodeUnary targetUnary polynomialUnary endpointRow provenanceRow endpointRow'
  intro provenanceRow' sameNode sameTarget samePolynomial sameSampleEndpoint
  intro sameSampleEndpoint' sigRel pkgSig
  have nodeUnary' : UnaryHistory node' := unary_transport nodeUnary sameNode
  have targetUnary' : UnaryHistory target' := unary_transport targetUnary sameTarget
  have polynomialUnary' : UnaryHistory polynomial' :=
    unary_transport polynomialUnary samePolynomial
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed nodeUnary' targetUnary' endpointRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed endpointUnary' polynomialUnary' provenanceRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameNode sameTarget endpointRow endpointRow'
  have sameSample : hsame sample sample' :=
    hsame_trans sameSampleEndpoint (hsame_trans sameEndpoint (hsame_symm sameSampleEndpoint'))
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameEndpoint samePolynomial provenanceRow provenanceRow'
  exact ⟨endpointUnary', provenanceUnary', sameSample, sameProvenance, sigRel, pkgSig⟩

end BEDC.Derived.InterpolationUp
