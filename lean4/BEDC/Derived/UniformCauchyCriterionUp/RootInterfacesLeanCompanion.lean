import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_root_interfaces_lean_companion [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      thresholdRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        Cont index windows thresholdRead ->
          Cont modulus tolerance toleranceRead ->
            Cont tail sealRow sealRead ->
              PkgSig bundle tailRead pkg ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory tailRead ∧ UnaryHistory thresholdRead ∧
                    UnaryHistory toleranceRead ∧ UnaryHistory sealRead ∧
                      hsame modulus thresholdRead ∧ hsame tail toleranceRead ∧
                        hsame transports sealRead ∧ Cont index tail tailRead ∧
                          Cont index windows thresholdRead ∧
                            Cont modulus tolerance toleranceRead ∧
                              Cont tail sealRow sealRead ∧ PkgSig bundle name pkg ∧
                                PkgSig bundle tailRead pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexTailRead indexWindowsThreshold modulusToleranceRead tailSealRead
    tailReadPkg sealReadPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have thresholdReadUnary : UnaryHistory thresholdRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsThreshold
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed _modulusUnary _toleranceUnary modulusToleranceRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have sameThreshold : hsame modulus thresholdRead :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsModulus
      indexWindowsThreshold
  have sameTolerance : hsame tail toleranceRead :=
    cont_respects_hsame (hsame_refl modulus) (hsame_refl tolerance) modulusToleranceTail
      modulusToleranceRead
  have sameSeal : hsame transports sealRead :=
    cont_respects_hsame (hsame_refl tail) (hsame_refl sealRow) tailSealRowTransports
      tailSealRead
  exact
    ⟨tailReadUnary, thresholdReadUnary, toleranceReadUnary, sealReadUnary, sameThreshold,
      sameTolerance, sameSeal, indexTailRead, indexWindowsThreshold, modulusToleranceRead,
      tailSealRead, namePkg, tailReadPkg, sealReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
