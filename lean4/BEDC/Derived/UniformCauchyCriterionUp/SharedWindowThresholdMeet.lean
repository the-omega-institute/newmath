import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_shared_window_threshold_meet [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name
      thresholdRead toleranceRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows thresholdRead ->
        Cont modulus tolerance toleranceRead ->
          Cont tolerance tail tailRead ->
            Cont tail sealRow sealRead ->
              PkgSig bundle thresholdRead pkg ->
                PkgSig bundle toleranceRead pkg ->
                  PkgSig bundle tailRead pkg ->
                    PkgSig bundle sealRead pkg ->
                      UnaryHistory windows ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
                        UnaryHistory thresholdRead ∧ UnaryHistory toleranceRead ∧
                          UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                            hsame modulus thresholdRead ∧ Cont index windows modulus ∧
                              Cont index windows thresholdRead ∧ Cont modulus tolerance tail ∧
                                Cont modulus tolerance toleranceRead ∧
                                  Cont tolerance tail tailRead ∧ Cont tail sealRow sealRead ∧
                                    PkgSig bundle name pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexWindowsThreshold modulusToleranceRead toleranceTailRead tailSealRead
    _thresholdPkg _tolerancePkg _tailPkg sealPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsThreshold
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed modulusUnary toleranceUnary modulusToleranceRead
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed toleranceUnary tailUnary toleranceTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have thresholdSame : hsame modulus thresholdRead :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsModulus
      indexWindowsThreshold
  exact
    ⟨windowsUnary, modulusUnary, toleranceUnary, thresholdUnary, toleranceReadUnary,
      tailReadUnary, sealReadUnary, thresholdSame, indexWindowsModulus,
        indexWindowsThreshold, modulusToleranceTail, modulusToleranceRead, toleranceTailRead,
      tailSealRead, namePkg, sealPkg⟩

theorem UniformCauchyCriterionSharedWindowThresholdMeet [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name meet endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows modulus meet ->
        Cont meet tolerance endpoint ->
          PkgSig bundle endpoint pkg ->
            UnaryHistory windows ∧ UnaryHistory modulus ∧ UnaryHistory meet ∧
              UnaryHistory tolerance ∧ UnaryHistory endpoint ∧ Cont windows modulus meet ∧
                Cont meet tolerance endpoint ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowModulusMeet meetToleranceEndpoint endpointPkg
  obtain ⟨_indexUnary, windowsUnary, modulusUnary, toleranceUnary, _tailUnary, _sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have meetUnary : UnaryHistory meet :=
    unary_cont_closed windowsUnary modulusUnary windowModulusMeet
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed meetUnary toleranceUnary meetToleranceEndpoint
  exact
    ⟨windowsUnary, modulusUnary, meetUnary, toleranceUnary, endpointUnary, windowModulusMeet,
      meetToleranceEndpoint, namePkg, endpointPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
