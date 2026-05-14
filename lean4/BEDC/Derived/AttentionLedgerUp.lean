import BEDC.Derived.AttentionLedgerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AttentionLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AttentionLedgerPacket [AskSetup] [PackageSetup]
    (source filter selected omitted publicRow stream transport exactness routes provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory source ∧ UnaryHistory filter ∧ UnaryHistory selected ∧ UnaryHistory omitted ∧
    UnaryHistory publicRow ∧ UnaryHistory stream ∧ UnaryHistory transport ∧
      UnaryHistory exactness ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont source filter selected ∧ Cont selected omitted exactness ∧
          Cont publicRow stream routes ∧ Cont routes transport provenance ∧
            PkgSig bundle nameCert pkg

theorem AttentionLedgerPacket_non_escape [AskSetup] [PackageSetup]
    {source filter selected omitted publicRow stream transport exactness routes provenance
      nameCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AttentionLedgerPacket source filter selected omitted publicRow stream transport exactness
        routes provenance nameCert bundle pkg →
      Cont omitted exactness consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory omitted ∧ UnaryHistory exactness ∧ UnaryHistory consumer ∧
            Cont omitted exactness consumer ∧ PkgSig bundle nameCert pkg ∧
              PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro packet omittedExactnessConsumer consumerPkg
  obtain ⟨_sourceUnary, _filterUnary, _selectedUnary, omittedUnary, _publicUnary, _streamUnary,
    _transportUnary, exactnessUnary, _routesUnary, _provenanceUnary, _nameCertUnary,
    _sourceFilterSelected, _selectedOmittedExactness, _publicStreamRoutes,
    _routesTransportProvenance, nameCertPkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed omittedUnary exactnessUnary omittedExactnessConsumer
  exact
    ⟨omittedUnary, exactnessUnary, consumerUnary, omittedExactnessConsumer, nameCertPkg,
      consumerPkg⟩

end BEDC.Derived.AttentionLedgerUp
