import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_root_synchronizer_tail_meet_lock [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name thresholdRead
      tailRead sealRead synchronizerRead sharedTailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows thresholdRead ->
        Cont index tail tailRead ->
          Cont tail sealRow sealRead ->
            Cont thresholdRead sealRead synchronizerRead ->
              Cont synchronizerRead tail sharedTailRead ->
                PkgSig bundle thresholdRead pkg ->
                  PkgSig bundle sealRead pkg ->
                    PkgSig bundle synchronizerRead pkg ->
                      PkgSig bundle sharedTailRead pkg ->
                        UnaryHistory thresholdRead ∧ UnaryHistory tailRead ∧
                          UnaryHistory sealRead ∧ UnaryHistory synchronizerRead ∧
                            UnaryHistory sharedTailRead ∧ hsame modulus thresholdRead ∧
                              Cont index windows thresholdRead ∧ Cont index tail tailRead ∧
                                Cont tail sealRow sealRead ∧
                                  Cont thresholdRead sealRead synchronizerRead ∧
                                    Cont synchronizerRead tail sharedTailRead ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle sharedTailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexWindowsThreshold indexTailRead tailSealRead thresholdSealSynchronizer
    synchronizerTailShared _thresholdPkg _sealPkg _synchronizerPkg sharedTailPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsThreshold
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have synchronizerUnary : UnaryHistory synchronizerRead :=
    unary_cont_closed thresholdUnary sealReadUnary thresholdSealSynchronizer
  have sharedTailUnary : UnaryHistory sharedTailRead :=
    unary_cont_closed synchronizerUnary tailUnary synchronizerTailShared
  have sameThreshold : hsame modulus thresholdRead :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsModulus
      indexWindowsThreshold
  exact
    ⟨thresholdUnary, tailReadUnary, sealReadUnary, synchronizerUnary, sharedTailUnary,
      sameThreshold, indexWindowsThreshold, indexTailRead, tailSealRead, thresholdSealSynchronizer,
      synchronizerTailShared, namePkg, sharedTailPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
