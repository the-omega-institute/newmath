import BEDC.Derived.RegSeqRatUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RegSeqRatUp

def CauchyFilterCarrier [AskSetup] [PackageSetup]
    (stream directed threshold endpoint regseq transport consumer provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory directed ∧ UnaryHistory threshold ∧
    UnaryHistory endpoint ∧ UnaryHistory regseq ∧ UnaryHistory transport ∧
      UnaryHistory consumer ∧ UnaryHistory provenance ∧ UnaryHistory nameRow ∧
        Cont stream directed regseq ∧ Cont regseq threshold transport ∧
          Cont transport endpoint consumer ∧ Cont consumer provenance nameRow ∧
            PkgSig bundle provenance pkg ∧
              SemanticNameCert (fun row : BHist => hsame row nameRow)
                (fun row : BHist => hsame row nameRow)
                (fun row : BHist => hsame row nameRow) hsame

theorem CauchyFilterCarrier_finite_window_coverage [AskSetup] [PackageSetup]
    {stream directed threshold endpoint regseq transport consumer provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCarrier stream directed threshold endpoint regseq transport consumer provenance
        nameRow bundle pkg ->
      exists observationWindow endpointWindow sealedWindow : BHist,
        Cont stream directed observationWindow ∧
          Cont observationWindow threshold endpointWindow ∧
            Cont endpointWindow endpoint sealedWindow ∧
              UnaryHistory observationWindow ∧
                UnaryHistory endpointWindow ∧ UnaryHistory sealedWindow := by
  intro carrier
  cases carrier with
  | intro streamUnary carrierRest =>
      cases carrierRest with
      | intro directedUnary carrierRest =>
          cases carrierRest with
          | intro thresholdUnary carrierRest =>
              cases carrierRest with
              | intro endpointUnary _carrierRest =>
                  let observationWindow := append stream directed
                  let endpointWindow := append observationWindow threshold
                  let sealedWindow := append endpointWindow endpoint
                  have observationRow : Cont stream directed observationWindow := by
                    rfl
                  have observationUnary : UnaryHistory observationWindow :=
                    unary_repetition_closed_under_continuation streamUnary directedUnary
                      observationRow
                  have endpointRow : Cont observationWindow threshold endpointWindow := by
                    rfl
                  have endpointWindowUnary : UnaryHistory endpointWindow :=
                    unary_repetition_closed_under_continuation observationUnary thresholdUnary
                      endpointRow
                  have sealedRow : Cont endpointWindow endpoint sealedWindow := by
                    rfl
                  have sealedUnary : UnaryHistory sealedWindow :=
                    unary_repetition_closed_under_continuation endpointWindowUnary endpointUnary
                      sealedRow
                  exact ⟨observationWindow, endpointWindow, sealedWindow, observationRow,
                    endpointRow, sealedRow, observationUnary, endpointWindowUnary, sealedUnary⟩

theorem CauchyFilterCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {stream directed threshold endpoint regseq transport consumer provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCarrier stream directed threshold endpoint regseq transport consumer provenance
        nameRow bundle pkg ->
      PkgSig bundle consumer pkg ->
        RegSeqRatStreamCarrier stream directed regseq threshold transport endpoint consumer
            bundle pkg ∧
          hsame consumer consumer := by
  intro carrier consumerPackage
  obtain ⟨streamUnary, directedUnary, thresholdUnary, endpointUnary, regseqUnary,
    transportUnary, consumerUnary, _provenanceUnary, _nameRowUnary, streamDirectedRegseq,
    regseqThresholdTransport, transportEndpointConsumer, _consumerProvenanceNameRow,
    _provenancePackage, _nameCert⟩ := carrier
  exact
    ⟨⟨streamUnary, directedUnary, regseqUnary, thresholdUnary, transportUnary, endpointUnary,
        consumerUnary, streamDirectedRegseq, regseqThresholdTransport, transportEndpointConsumer,
        consumerPackage⟩,
      hsame_refl consumer⟩

end BEDC.Derived.CauchyFilterUp
