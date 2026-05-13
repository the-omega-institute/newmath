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

theorem UniformCauchyCriterionPacket_finite_family_regseq_real_handoff [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead sharedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail regseqRead →
        Cont tail sealRow realRead →
          Cont regseqRead realRead sharedRoute →
            PkgSig bundle regseqRead pkg →
              PkgSig bundle realRead pkg →
                PkgSig bundle sharedRoute pkg →
                  UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                    UnaryHistory sharedRoute ∧ Cont index windows modulus ∧
                      Cont modulus tolerance tail ∧ Cont index tail regseqRead ∧
                        Cont tail sealRow realRead ∧ Cont regseqRead realRead sharedRoute ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle regseqRead pkg ∧
                            PkgSig bundle realRead pkg ∧ PkgSig bundle sharedRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet indexTailRegseq tailSealReal regseqRealShared regseqPkg realPkg sharedPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have sharedUnary : UnaryHistory sharedRoute :=
    unary_cont_closed regseqUnary realUnary regseqRealShared
  exact
    ⟨regseqUnary, realUnary, sharedUnary, indexWindowsModulus, modulusToleranceTail,
      indexTailRegseq, tailSealReal, regseqRealShared, namePkg, regseqPkg, realPkg,
      sharedPkg⟩

theorem UniformCauchyCriterionPacket_shared_window_threshold_meet [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name toleranceRead
      tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont modulus tolerance toleranceRead ->
        Cont tolerance tail tailRead ->
          Cont tail sealRow sealRead ->
            PkgSig bundle toleranceRead pkg ->
              PkgSig bundle tailRead pkg ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory windows /\ UnaryHistory modulus /\ UnaryHistory tolerance /\
                    UnaryHistory toleranceRead /\ UnaryHistory tailRead /\ UnaryHistory sealRead /\
                      Cont index windows modulus /\ Cont modulus tolerance tail /\
                        Cont modulus tolerance toleranceRead /\ Cont tolerance tail tailRead /\
                          Cont tail sealRow sealRead /\ PkgSig bundle name pkg /\
                            PkgSig bundle toleranceRead pkg /\ PkgSig bundle tailRead pkg /\
                              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet modulusToleranceRead toleranceTailRead tailSealRead toleranceReadPkg tailReadPkg
    sealReadPkg
  obtain ⟨_indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed modulusUnary toleranceUnary modulusToleranceRead
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed toleranceUnary tailUnary toleranceTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  exact
    ⟨windowsUnary, modulusUnary, toleranceUnary, toleranceReadUnary, tailReadUnary,
      sealReadUnary, indexWindowsModulus, modulusToleranceTail, modulusToleranceRead,
      toleranceTailRead, tailSealRead, namePkg, toleranceReadPkg, tailReadPkg, sealReadPkg⟩

theorem UniformCauchyCriterionPacket_root_threshold_schedule_determinacy [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name thresholdRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows thresholdRead ->
        PkgSig bundle thresholdRead pkg ->
          UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
            UnaryHistory thresholdRead ∧ Cont index windows modulus ∧
              Cont index windows thresholdRead ∧ hsame modulus thresholdRead ∧
                PkgSig bundle name pkg ∧ PkgSig bundle thresholdRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexWindowsThreshold thresholdPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, _toleranceUnary, _tailUnary, _sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsThreshold
  have sameThreshold : hsame modulus thresholdRead :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsModulus
      indexWindowsThreshold
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, thresholdUnary, indexWindowsModulus,
      indexWindowsThreshold, sameThreshold, namePkg, thresholdPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
