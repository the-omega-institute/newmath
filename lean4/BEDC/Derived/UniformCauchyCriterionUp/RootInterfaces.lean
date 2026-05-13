import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_root_tail_coverage [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        PkgSig bundle tailRead pkg ->
          UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
            UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory transports ∧
              UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                UnaryHistory tailRead ∧ Cont index windows modulus ∧
                  Cont modulus tolerance tail ∧ Cont tail sealRow transports ∧
                    Cont transports routes provenance ∧ Cont index tail tailRead ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailReadPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, _sealRowUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, indexWindowsModulus,
    modulusToleranceTail, tailSealRowTransports, transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, transportsUnary,
      routesUnary, provenanceUnary, nameUnary, tailReadUnary, indexWindowsModulus,
      modulusToleranceTail, tailSealRowTransports, transportsRoutesProvenance, indexTailRead,
      namePkg, tailReadPkg⟩

theorem UniformCauchyCriterionPacket_root_downstream_seal_interface [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name
      thresholdRead toleranceRead tailRead sealRead sharedTailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows thresholdRead ->
        Cont modulus tolerance toleranceRead ->
          Cont tolerance tail tailRead ->
            Cont tail sealRow sealRead ->
              Cont sealRead tail sharedTailRead ->
                PkgSig bundle thresholdRead pkg ->
                  PkgSig bundle toleranceRead pkg ->
                    PkgSig bundle tailRead pkg ->
                      PkgSig bundle sealRead pkg ->
                        PkgSig bundle sharedTailRead pkg ->
                          UnaryHistory thresholdRead ∧ UnaryHistory toleranceRead ∧
                            UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                              UnaryHistory sharedTailRead ∧ hsame modulus thresholdRead ∧
                                Cont index windows thresholdRead ∧
                                  Cont modulus tolerance toleranceRead ∧
                                    Cont tolerance tail tailRead ∧ Cont tail sealRow sealRead ∧
                                      Cont sealRead tail sharedTailRead ∧
                                        PkgSig bundle name pkg ∧
                                          PkgSig bundle sharedTailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexWindowsThreshold modulusToleranceRead toleranceTailRead tailSealRead
    sealTailShared _thresholdPkg _tolerancePkg _tailPkg _sealPkg sharedPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsThreshold
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed modulusUnary toleranceUnary modulusToleranceRead
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed toleranceUnary tailUnary toleranceTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have sharedTailUnary : UnaryHistory sharedTailRead :=
    unary_cont_closed sealReadUnary tailUnary sealTailShared
  have sameThreshold : hsame modulus thresholdRead :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsModulus
      indexWindowsThreshold
  exact
    ⟨thresholdUnary, toleranceReadUnary, tailReadUnary, sealReadUnary, sharedTailUnary,
      sameThreshold, indexWindowsThreshold, modulusToleranceRead, toleranceTailRead,
      tailSealRead, sealTailShared, namePkg, sharedPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
