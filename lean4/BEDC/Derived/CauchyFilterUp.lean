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

def CauchyFilterWindowPacket [AskSetup] [PackageSetup]
    (stream window threshold endpoint compatibility transport consumer provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory window ∧ UnaryHistory threshold ∧ UnaryHistory endpoint ∧
    UnaryHistory compatibility ∧ Cont stream window transport ∧
      Cont threshold endpoint compatibility ∧ Cont transport compatibility consumer ∧
        Cont consumer endpoint provenance ∧ PkgSig bundle provenance pkg

theorem CauchyFilterPacket_finite_window_coverage [AskSetup] [PackageSetup]
    {stream window threshold endpoint compatibility transport consumer provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterWindowPacket stream window threshold endpoint compatibility transport consumer provenance
        bundle pkg ->
      UnaryHistory stream ∧ UnaryHistory window ∧ UnaryHistory threshold ∧ UnaryHistory endpoint ∧
        UnaryHistory compatibility ∧ UnaryHistory transport ∧ UnaryHistory consumer ∧
          UnaryHistory provenance ∧ hsame transport (append stream window) ∧
            hsame compatibility (append threshold endpoint) ∧
              hsame consumer (append transport compatibility) ∧
                hsame provenance (append consumer endpoint) ∧ PkgSig bundle provenance pkg := by
  intro packet
  have streamUnary : UnaryHistory stream :=
    packet.left
  have windowUnary : UnaryHistory window :=
    packet.right.left
  have thresholdUnary : UnaryHistory threshold :=
    packet.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    packet.right.right.right.left
  have compatibilityUnary : UnaryHistory compatibility :=
    packet.right.right.right.right.left
  have transportRow : Cont stream window transport :=
    packet.right.right.right.right.right.left
  have compatibilityRow : Cont threshold endpoint compatibility :=
    packet.right.right.right.right.right.right.left
  have consumerRow : Cont transport compatibility consumer :=
    packet.right.right.right.right.right.right.right.left
  have provenanceRow : Cont consumer endpoint provenance :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.right.right.right
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed streamUnary windowUnary transportRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed transportUnary compatibilityUnary consumerRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed consumerUnary endpointUnary provenanceRow
  exact And.intro streamUnary
    (And.intro windowUnary
      (And.intro thresholdUnary
        (And.intro endpointUnary
          (And.intro compatibilityUnary
            (And.intro transportUnary
              (And.intro consumerUnary
                (And.intro provenanceUnary
                  (And.intro transportRow
                  (And.intro compatibilityRow
                    (And.intro consumerRow
                        (And.intro provenanceRow pkgSig)))))))))))


def CauchyFilterRegSeqRatWindow [AskSetup] [PackageSetup]
    (stream directed modulus endpoint regseq transport provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory directed ∧ UnaryHistory modulus ∧
    UnaryHistory endpoint ∧ UnaryHistory regseq ∧ UnaryHistory transport ∧
      UnaryHistory provenance ∧ Cont stream directed modulus ∧ Cont modulus endpoint regseq ∧
        Cont regseq transport provenance ∧ PkgSig bundle provenance pkg

def CauchyFilterPacket [AskSetup] [PackageSetup]
    (stream directed modulus endpoint regseq transport consumer provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory directed ∧ UnaryHistory modulus ∧
    UnaryHistory endpoint ∧ UnaryHistory regseq ∧ UnaryHistory transport ∧
      UnaryHistory consumer ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
        Cont stream directed modulus ∧ Cont modulus endpoint regseq ∧
          Cont regseq transport provenance ∧ Cont endpoint regseq transport ∧
            Cont transport consumer provenance ∧ Cont provenance cert consumer ∧
              PkgSig bundle provenance pkg

theorem CauchyFilterPacket_regseqrat_handoff [AskSetup] [PackageSetup]
    {stream directed modulus endpoint regseq transport consumer provenance cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterPacket stream directed modulus endpoint regseq transport consumer provenance cert
        bundle pkg ->
      CauchyFilterRegSeqRatWindow stream directed modulus endpoint regseq transport provenance
          bundle pkg ∧
        Cont endpoint regseq transport ∧ Cont transport consumer provenance ∧
          PkgSig bundle provenance pkg := by
  intro packet
  obtain ⟨streamUnary, directedUnary, modulusUnary, endpointUnary, regseqUnary,
    transportUnary, _consumerUnary, provenanceUnary, _certUnary, streamDirectedRow,
    modulusEndpointRow, regseqTransportRow, endpointRegseqRow, transportConsumerRow,
    _certConsumerRow, pkgRow⟩ := packet
  exact
    ⟨⟨streamUnary, directedUnary, modulusUnary, endpointUnary, regseqUnary, transportUnary,
        provenanceUnary, streamDirectedRow, modulusEndpointRow, regseqTransportRow, pkgRow⟩,
      endpointRegseqRow, transportConsumerRow, pkgRow⟩

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
    transportUnary, consumerUnary, provenanceUnary, namecertUnary, _streamDirectedRow,
    _thresholdEndpointRow, _compatTransportRow, _endpointCompatRow, _transportConsumerRow,
    _provenanceNamecertRow, pkgRow⟩ := packet
  exact
    ⟨streamUnary, directedUnary, thresholdUnary, endpointUnary, compatUnary, transportUnary,
      consumerUnary, provenanceUnary, namecertUnary, leftRow, rightRow, commonRow, commonRow,
      pkgRow⟩

theorem CauchyFilterPacket_refinement_transport [AskSetup] [PackageSetup]
    {stream directed threshold endpoint compat transport consumer provenance namecert left right
      common : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterPacket stream directed threshold endpoint compat transport consumer provenance
        namecert bundle pkg →
      Cont directed threshold left →
        Cont endpoint compat right →
          Cont left right common →
            hsame common (append left right) ∧ PkgSig bundle provenance pkg := by
  intro packet _leftRow _rightRow commonRow
  obtain ⟨_streamUnary, _directedUnary, _thresholdUnary, _endpointUnary, _compatUnary,
    _transportUnary, _consumerUnary, _provenanceUnary, _namecertUnary, _streamDirectedRow,
    _thresholdEndpointRow, _compatTransportRow, _endpointCompatRow, _transportConsumerRow,
    _provenanceNamecertRow, pkgRow⟩ := packet
  exact ⟨commonRow, pkgRow⟩

end BEDC.Derived.CauchyFilterUp
