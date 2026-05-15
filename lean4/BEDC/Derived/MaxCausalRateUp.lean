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

theorem MaxCausalRatePacket_scoped_kernel_boundary [AskSetup] [PackageSetup]
    {configuration witnesses bound comparisons hsameTransport psameStability routes provenance
      nameCert downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MaxCausalRatePacket configuration witnesses bound comparisons hsameTransport psameStability
        routes provenance nameCert bundle pkg →
      Cont routes provenance downstream →
        PkgSig bundle downstream pkg →
          UnaryHistory configuration ∧ UnaryHistory witnesses ∧ UnaryHistory bound ∧
            UnaryHistory comparisons ∧ UnaryHistory hsameTransport ∧
              UnaryHistory psameStability ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
                UnaryHistory nameCert ∧ UnaryHistory downstream ∧
                  Cont witnesses bound comparisons ∧
                    Cont comparisons hsameTransport psameStability ∧
                      Cont psameStability routes provenance ∧
                        Cont routes provenance downstream ∧ PkgSig bundle nameCert pkg ∧
                          PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg UnaryHistory
  intro packet downstreamRoute downstreamPkg
  obtain ⟨configurationUnary, witnessesUnary, boundUnary, comparisonsUnary,
    hsameTransportUnary, psameStabilityUnary, routesUnary, provenanceUnary, nameCertUnary,
    witnessBoundComparison, comparisonTransportStability, stabilityRouteProvenance,
    _provenanceNameConfiguration, namePkg⟩ := packet
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed routesUnary provenanceUnary downstreamRoute
  exact
    ⟨configurationUnary, witnessesUnary, boundUnary, comparisonsUnary, hsameTransportUnary,
      psameStabilityUnary, routesUnary, provenanceUnary, nameCertUnary, downstreamUnary,
        witnessBoundComparison, comparisonTransportStability, stabilityRouteProvenance,
          downstreamRoute, namePkg, downstreamPkg⟩

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

theorem MaxCausalRatePacket_comparison_ledger_exactness [AskSetup] [PackageSetup]
    {configuration witnesses bound comparisons hsameTransport psameStability routes provenance
      nameCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MaxCausalRatePacket configuration witnesses bound comparisons hsameTransport psameStability
        routes provenance nameCert bundle pkg →
      hsame consumer comparisons →
        UnaryHistory consumer ∧ UnaryHistory witnesses ∧ UnaryHistory bound ∧
          Cont witnesses bound comparisons ∧ PkgSig bundle nameCert pkg := by
  intro packet consumerSame
  obtain ⟨_configurationUnary, witnessesUnary, boundUnary, comparisonsUnary,
    _hsameTransportUnary, _psameStabilityUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, witnessBoundComparison, _comparisonTransportStability,
    _stabilityRouteProvenance, _provenanceNameConfiguration, namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_transport comparisonsUnary (hsame_symm consumerSame)
  exact ⟨consumerUnary, witnessesUnary, boundUnary, witnessBoundComparison, namePkg⟩

theorem MaxCausalRatePacket_witness_family_stability [AskSetup] [PackageSetup]
    {configuration witnesses bound comparisons hsameTransport psameStability routes provenance
      nameCert witnesses' bound' comparisons' transported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MaxCausalRatePacket configuration witnesses bound comparisons hsameTransport psameStability
        routes provenance nameCert bundle pkg →
      hsame witnesses witnesses' →
        hsame bound bound' →
          hsame comparisons comparisons' →
            Cont witnesses' bound' transported →
              hsame transported comparisons' →
                UnaryHistory witnesses' ∧ UnaryHistory bound' ∧ UnaryHistory comparisons' ∧
                  UnaryHistory transported ∧ Cont witnesses' bound' transported ∧
                    PkgSig bundle nameCert pkg := by
  intro packet sameWitnesses sameBound sameComparisons transportedRoute transportedSame
  obtain ⟨_configurationUnary, witnessesUnary, boundUnary, comparisonsUnary,
    _hsameTransportUnary, _psameStabilityUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, _witnessBoundComparison, _comparisonTransportStability,
    _stabilityRouteProvenance, _provenanceNameConfiguration, namePkg⟩ := packet
  have witnessesUnary' : UnaryHistory witnesses' :=
    unary_transport witnessesUnary sameWitnesses
  have boundUnary' : UnaryHistory bound' :=
    unary_transport boundUnary sameBound
  have comparisonsUnary' : UnaryHistory comparisons' :=
    unary_transport comparisonsUnary sameComparisons
  have transportedUnary : UnaryHistory transported :=
    unary_transport comparisonsUnary' (hsame_symm transportedSame)
  exact
    ⟨witnessesUnary', boundUnary', comparisonsUnary', transportedUnary, transportedRoute,
      namePkg⟩

theorem MaxCausalRatePacket_configuration_locality_obligation [AskSetup] [PackageSetup]
    {configuration witnesses bound comparisons hsameTransport psameStability routes provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MaxCausalRatePacket configuration witnesses bound comparisons hsameTransport psameStability
        routes provenance nameCert bundle pkg ->
      UnaryHistory configuration /\ UnaryHistory witnesses /\ UnaryHistory bound /\
        Cont provenance nameCert configuration /\ PkgSig bundle nameCert pkg := by
  intro packet
  obtain ⟨configurationUnary, witnessesUnary, boundUnary, _comparisonsUnary,
    _hsameTransportUnary, _psameStabilityUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, _witnessBoundComparison, _comparisonTransportStability,
    _stabilityRouteProvenance, provenanceNameConfiguration, namePkg⟩ := packet
  exact
    ⟨configurationUnary, witnessesUnary, boundUnary, provenanceNameConfiguration, namePkg⟩

theorem MaxCausalRatePacket_public_unary_bound_export [AskSetup] [PackageSetup]
    {configuration witnesses bound comparisons hsameTransport psameStability routes provenance
      nameCert witnessRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MaxCausalRatePacket configuration witnesses bound comparisons hsameTransport psameStability
        routes provenance nameCert bundle pkg ->
      Cont witnesses bound witnessRead ->
        Cont witnessRead routes publicRead ->
          PkgSig bundle witnessRead pkg ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory bound ∧ UnaryHistory witnessRead ∧ UnaryHistory publicRead ∧
                Cont witnesses bound witnessRead ∧ Cont witnessRead routes publicRead ∧
                  PkgSig bundle nameCert pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro packet witnessRoute publicRoute _witnessPkg publicPkg
  obtain ⟨_configurationUnary, witnessesUnary, boundUnary, _comparisonsUnary,
    _hsameTransportUnary, _psameStabilityUnary, routesUnary, _provenanceUnary,
    _nameCertUnary, _witnessBoundComparison, _comparisonTransportStability,
    _stabilityRouteProvenance, _provenanceNameConfiguration, namePkg⟩ := packet
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed witnessesUnary boundUnary witnessRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed witnessReadUnary routesUnary publicRoute
  exact
    ⟨boundUnary, witnessReadUnary, publicReadUnary, witnessRoute, publicRoute, namePkg,
      publicPkg⟩

theorem MaxCausalRatePacket_unary_bound_consumer_bridge [AskSetup] [PackageSetup]
    {configuration witnesses bound comparisons hsameTransport psameStability routes provenance
      nameCert witnessRead publicRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MaxCausalRatePacket configuration witnesses bound comparisons hsameTransport psameStability
        routes provenance nameCert bundle pkg ->
      Cont witnesses bound witnessRead ->
        Cont witnessRead routes publicRead ->
          Cont publicRead bound bridgeRead ->
            PkgSig bundle publicRead pkg ->
              PkgSig bundle bridgeRead pkg ->
                UnaryHistory configuration ∧ UnaryHistory witnesses ∧ UnaryHistory bound ∧
                  UnaryHistory comparisons ∧ UnaryHistory witnessRead ∧
                    UnaryHistory publicRead ∧ UnaryHistory bridgeRead ∧
                      Cont witnesses bound witnessRead ∧ Cont witnessRead routes publicRead ∧
                        Cont publicRead bound bridgeRead ∧ PkgSig bundle nameCert pkg ∧
                          PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro packet witnessRoute publicRoute bridgeRoute _publicPkg bridgePkg
  obtain ⟨configurationUnary, witnessesUnary, boundUnary, comparisonsUnary,
    _hsameTransportUnary, _psameStabilityUnary, routesUnary, _provenanceUnary,
    _nameCertUnary, _witnessBoundComparison, _comparisonTransportStability,
    _stabilityRouteProvenance, _provenanceNameConfiguration, namePkg⟩ := packet
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed witnessesUnary boundUnary witnessRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed witnessReadUnary routesUnary publicRoute
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicReadUnary boundUnary bridgeRoute
  exact
    ⟨configurationUnary, witnessesUnary, boundUnary, comparisonsUnary, witnessReadUnary,
      publicReadUnary, bridgeReadUnary, witnessRoute, publicRoute, bridgeRoute, namePkg,
      bridgePkg⟩

end BEDC.Derived.MaxCausalRateUp
