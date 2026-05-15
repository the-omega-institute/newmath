import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_root_threshold_synchronizer_readback [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name thresholdRead
      tailRead sealRead synchronizerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows thresholdRead ->
        Cont index tail tailRead ->
          Cont tail sealRow sealRead ->
            Cont thresholdRead sealRead synchronizerRead ->
              PkgSig bundle thresholdRead pkg ->
                PkgSig bundle sealRead pkg ->
                  PkgSig bundle synchronizerRead pkg ->
                    UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                      UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                        UnaryHistory thresholdRead ∧ UnaryHistory tailRead ∧
                          UnaryHistory sealRead ∧ UnaryHistory synchronizerRead ∧
                            Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                              Cont index windows thresholdRead ∧ hsame modulus thresholdRead ∧
                                Cont index tail tailRead ∧ Cont tail sealRow sealRead ∧
                                  Cont thresholdRead sealRead synchronizerRead ∧
                                    PkgSig bundle name pkg ∧
                                      PkgSig bundle thresholdRead pkg ∧
                                        PkgSig bundle sealRead pkg ∧
                                          PkgSig bundle synchronizerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexWindowsThreshold indexTailRead tailSealRead thresholdSealSynchronizer
    thresholdPkg sealPkg synchronizerPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsThreshold
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealUnary tailSealRead
  have synchronizerUnary : UnaryHistory synchronizerRead :=
    unary_cont_closed thresholdUnary sealReadUnary thresholdSealSynchronizer
  have sameThreshold : hsame modulus thresholdRead :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsModulus
      indexWindowsThreshold
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealUnary,
      thresholdUnary, tailReadUnary, sealReadUnary, synchronizerUnary, indexWindowsModulus,
      modulusToleranceTail, indexWindowsThreshold, sameThreshold, indexTailRead, tailSealRead,
      thresholdSealSynchronizer, namePkg, thresholdPkg, sealPkg, synchronizerPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
