import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_tail_cofinal_seal_reflector
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRequest
      sealRequest reflector : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail tailRequest →
        Cont tail sealRow sealRequest →
          Cont tailRequest sealRequest reflector →
            PkgSig bundle tailRequest pkg →
              PkgSig bundle sealRequest pkg →
                PkgSig bundle reflector pkg →
                  UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                    UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                      UnaryHistory tailRequest ∧ UnaryHistory sealRequest ∧
                        UnaryHistory reflector ∧ Cont index windows modulus ∧
                          Cont modulus tolerance tail ∧ Cont index tail tailRequest ∧
                            Cont tail sealRow sealRequest ∧
                              Cont tailRequest sealRequest reflector ∧
                                PkgSig bundle name pkg ∧
                                  PkgSig bundle tailRequest pkg ∧
                                    PkgSig bundle sealRequest pkg ∧
                                      PkgSig bundle reflector pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRequest tailSealRequest requestSealReflector tailRequestPkg
    sealRequestPkg reflectorPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailRequestUnary : UnaryHistory tailRequest :=
    unary_cont_closed indexUnary tailUnary indexTailRequest
  have sealRequestUnary : UnaryHistory sealRequest :=
    unary_cont_closed tailUnary sealRowUnary tailSealRequest
  have reflectorUnary : UnaryHistory reflector :=
    unary_cont_closed tailRequestUnary sealRequestUnary requestSealReflector
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      tailRequestUnary, sealRequestUnary, reflectorUnary, indexWindowsModulus,
      modulusToleranceTail, indexTailRequest, tailSealRequest, requestSealReflector,
      namePkg, tailRequestPkg, sealRequestPkg, reflectorPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
