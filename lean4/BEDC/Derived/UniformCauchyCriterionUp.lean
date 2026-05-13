import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformCauchyCriterionPacket [AskSetup] [PackageSetup]
    (index windows modulus tolerance tail sealRow transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
    UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
      UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont index windows modulus ∧ Cont modulus tolerance tail ∧
          Cont tail sealRow transports ∧ Cont transports routes provenance ∧
            PkgSig bundle name pkg

theorem UniformCauchyCriterionPacket_namecert_obligations [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
            UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
              UnaryHistory consumer ∧ Cont index windows modulus ∧
                Cont modulus tolerance tail ∧ Cont index tail consumer ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet indexTailConsumer consumerPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed indexUnary tailUnary indexTailConsumer
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      consumerUnary, indexWindowsModulus, modulusToleranceTail, indexTailConsumer, namePkg,
      consumerPkg⟩

theorem UniformCauchyCriterionPacket_shared_threshold_transport [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name index' windows'
      modulus' tolerance' tail' sealRow' transports' routes' provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      hsame index index' →
        hsame windows windows' →
          hsame modulus modulus' →
            hsame tolerance tolerance' →
              hsame sealRow sealRow' →
                hsame routes routes' →
                  hsame provenance provenance' →
                    hsame name name' →
                      Cont index' windows' modulus' →
                        Cont modulus' tolerance' tail' →
                          Cont tail' sealRow' transports' →
                            Cont transports' routes' provenance' →
                              PkgSig bundle name' pkg →
                                UniformCauchyCriterionPacket index' windows' modulus' tolerance'
                                      tail' sealRow' transports' routes' provenance' name'
                                      bundle pkg ∧
                                  hsame tail tail' ∧
                                    UnaryHistory modulus' ∧
                                      UnaryHistory tolerance' ∧ UnaryHistory tail' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet sameIndex sameWindows sameModulus sameTolerance sameSealRow sameRoutes
    sameProvenance sameName indexWindowsModulus' modulusToleranceTail'
    tailSealRowTransports' transportsRoutesProvenance' namePkg'
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, _tailUnary, sealRowUnary,
    _transportsUnary, routesUnary, provenanceUnary, nameUnary, _indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, _namePkg⟩ :=
    packet
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_transport toleranceUnary sameTolerance
  have tailSame : hsame tail tail' :=
    cont_respects_hsame sameModulus sameTolerance modulusToleranceTail modulusToleranceTail'
  have tailUnary' : UnaryHistory tail' :=
    unary_cont_closed modulusUnary' toleranceUnary' modulusToleranceTail'
  have indexUnary' : UnaryHistory index' :=
    unary_transport indexUnary sameIndex
  have windowsUnary' : UnaryHistory windows' :=
    unary_transport windowsUnary sameWindows
  have sealRowUnary' : UnaryHistory sealRow' :=
    unary_transport sealRowUnary sameSealRow
  have transportsUnary' : UnaryHistory transports' :=
    unary_cont_closed tailUnary' sealRowUnary' tailSealRowTransports'
  have routesUnary' : UnaryHistory routes' :=
    unary_transport routesUnary sameRoutes
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory name' :=
    unary_transport nameUnary sameName
  exact
    ⟨⟨indexUnary', windowsUnary', modulusUnary', toleranceUnary', tailUnary', sealRowUnary',
        transportsUnary', routesUnary', provenanceUnary', nameUnary', indexWindowsModulus',
        modulusToleranceTail', tailSealRowTransports', transportsRoutesProvenance',
        namePkg'⟩,
      tailSame, modulusUnary', toleranceUnary', tailUnary'⟩

theorem UniformCauchyCriterionPacket_real_seal_handoff [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name realRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont tail sealRow realRead ->
        PkgSig bundle realRead pkg ->
          UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
            UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
              UnaryHistory realRead ∧ Cont index windows modulus ∧
                Cont modulus tolerance tail ∧ Cont tail sealRow realRead ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet tailSealRealRead realReadPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRealRead
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      realReadUnary, indexWindowsModulus, modulusToleranceTail, tailSealRealRead, namePkg,
      realReadPkg⟩

theorem UniformCauchyCriterionPacket_root_downstream_unblock [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      realRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        Cont tail sealRow realRead ->
          Cont tail realRead consumer ->
            PkgSig bundle tailRead pkg ->
              PkgSig bundle realRead pkg ->
                PkgSig bundle consumer pkg ->
                  UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                    UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                      UnaryHistory tailRead ∧ UnaryHistory realRead ∧
                        UnaryHistory consumer ∧ Cont index windows modulus ∧
                          Cont modulus tolerance tail ∧ Cont index tail tailRead ∧
                            Cont tail sealRow realRead ∧ Cont tail realRead consumer ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle tailRead pkg ∧
                                PkgSig bundle realRead pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet indexTailRead tailSealRealRead tailRealConsumer tailReadPkg realReadPkg consumerPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRealRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed tailUnary realReadUnary tailRealConsumer
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      tailReadUnary, realReadUnary, consumerUnary, indexWindowsModulus, modulusToleranceTail,
      indexTailRead, tailSealRealRead, tailRealConsumer, namePkg, tailReadPkg, realReadPkg,
      consumerPkg⟩

theorem UniformCauchyCriterionPacket_root_tolerance_ledger_exactness [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        PkgSig bundle tailRead pkg ->
          UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
            UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory tailRead ∧
              Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                Cont index tail tailRead ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet indexTailRead tailReadPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, _sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, tailReadUnary,
      indexWindowsModulus, modulusToleranceTail, indexTailRead, namePkg, tailReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
