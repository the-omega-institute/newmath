import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.MaxCausalRateUp.TasteGate

namespace BEDC.Derived.MaxCausalRateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MaxCausalRatePacket [AskSetup] [PackageSetup]
    (configuration witnesses bound comparisons hsameTransport psameStability routes provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory configuration ∧ UnaryHistory witnesses ∧ UnaryHistory bound ∧
    UnaryHistory comparisons ∧ UnaryHistory hsameTransport ∧ UnaryHistory psameStability ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        Cont witnesses bound comparisons ∧ Cont comparisons hsameTransport psameStability ∧
          Cont psameStability routes provenance ∧ Cont provenance nameCert configuration ∧
            PkgSig bundle nameCert pkg

theorem MaxCausalRatePacket_crosshist_handoff [AskSetup] [PackageSetup]
    {configuration witnesses bound comparisons hsameTransport psameStability routes provenance
      nameCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MaxCausalRatePacket configuration witnesses bound comparisons hsameTransport psameStability
        routes provenance nameCert bundle pkg ->
      Cont witnesses bound consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory configuration ∧ UnaryHistory witnesses ∧ UnaryHistory bound ∧
            UnaryHistory consumer ∧ Cont witnesses bound consumer ∧ PkgSig bundle nameCert pkg ∧
              PkgSig bundle consumer pkg := by
  intro packet consumerRoute consumerPkg
  obtain ⟨configurationUnary, witnessesUnary, boundUnary, _comparisonsUnary,
    _hsameTransportUnary, _psameStabilityUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, _witnessBoundComparison, _comparisonTransportStability,
    _stabilityRouteProvenance, _provenanceNameConfiguration, namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed witnessesUnary boundUnary consumerRoute
  exact ⟨configurationUnary, witnessesUnary, boundUnary, consumerUnary, consumerRoute, namePkg,
    consumerPkg⟩

theorem MaxCausalRatePacket_non_escape [AskSetup] [PackageSetup]
    {configuration witnesses bound comparisons hsameTransport psameStability routes provenance
      nameCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MaxCausalRatePacket configuration witnesses bound comparisons hsameTransport psameStability
        routes provenance nameCert bundle pkg ->
      Cont routes provenance consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory configuration ∧ UnaryHistory witnesses ∧ UnaryHistory bound ∧
            UnaryHistory comparisons ∧ UnaryHistory hsameTransport ∧
              UnaryHistory psameStability ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
                UnaryHistory nameCert ∧ UnaryHistory consumer ∧
                  Cont psameStability routes provenance ∧ Cont routes provenance consumer ∧
                    PkgSig bundle nameCert pkg ∧ PkgSig bundle consumer pkg := by
  intro packet consumerRoute consumerPkg
  obtain ⟨configurationUnary, witnessesUnary, boundUnary, comparisonsUnary,
    hsameTransportUnary, psameStabilityUnary, routesUnary, provenanceUnary, nameCertUnary,
    _witnessBoundComparison, _comparisonTransportStability, stabilityRouteProvenance,
    _provenanceNameConfiguration, namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routesUnary provenanceUnary consumerRoute
  exact
    ⟨configurationUnary, witnessesUnary, boundUnary, comparisonsUnary, hsameTransportUnary,
      psameStabilityUnary, routesUnary, provenanceUnary, nameCertUnary, consumerUnary,
        stabilityRouteProvenance, consumerRoute, namePkg, consumerPkg⟩

theorem MaxCausalRatePacket_bound_comparison_totality [AskSetup] [PackageSetup]
    {configuration witnesses bound comparisons hsameTransport psameStability routes provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MaxCausalRatePacket configuration witnesses bound comparisons hsameTransport psameStability
        routes provenance nameCert bundle pkg ->
      UnaryHistory witnesses /\ UnaryHistory bound /\ UnaryHistory comparisons /\
        Cont witnesses bound comparisons /\ hsame bound bound := by
  intro packet
  obtain ⟨_configurationUnary, witnessesUnary, boundUnary, comparisonsUnary,
    _hsameTransportUnary, _psameStabilityUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, witnessBoundComparison, _comparisonTransportStability,
    _stabilityRouteProvenance, _provenanceNameConfiguration, _namePkg⟩ := packet
  exact
    ⟨witnessesUnary, boundUnary, comparisonsUnary, witnessBoundComparison, hsame_refl bound⟩

theorem MaxCausalRatePacket_unary_bound_nonescape [AskSetup] [PackageSetup]
    {configuration witnesses bound comparisons hsameTransport psameStability routes provenance
      nameCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MaxCausalRatePacket configuration witnesses bound comparisons hsameTransport psameStability
        routes provenance nameCert bundle pkg ->
      hsame consumer comparisons ->
        UnaryHistory consumer ∧ Cont witnesses bound comparisons ∧ UnaryHistory bound ∧
          PkgSig bundle nameCert pkg := by
  intro packet consumerSame
  obtain ⟨_configurationUnary, _witnessesUnary, boundUnary, comparisonsUnary,
    _hsameTransportUnary, _psameStabilityUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, witnessBoundComparison, _comparisonTransportStability,
    _stabilityRouteProvenance, _provenanceNameConfiguration, namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_transport comparisonsUnary (hsame_symm consumerSame)
  exact ⟨consumerUnary, witnessBoundComparison, boundUnary, namePkg⟩

end BEDC.Derived.MaxCausalRateUp
