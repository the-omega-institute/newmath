import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_shared_tail_gluing_determinacy
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name leftTail
      rightTail leftSeal rightSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail leftTail ->
        Cont index tail rightTail ->
          hsame leftTail rightTail ->
            Cont leftTail sealRow leftSeal ->
              Cont rightTail sealRow rightSeal ->
                PkgSig bundle leftSeal pkg ->
                  PkgSig bundle rightSeal pkg ->
                    UnaryHistory leftTail ∧ UnaryHistory rightTail ∧ UnaryHistory leftSeal ∧
                      UnaryHistory rightSeal ∧ hsame leftSeal rightSeal ∧
                        Cont index tail leftTail ∧ Cont index tail rightTail ∧
                          Cont leftTail sealRow leftSeal ∧ Cont rightTail sealRow rightSeal ∧
                            PkgSig bundle leftSeal pkg ∧
                              PkgSig bundle rightSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexTailLeft indexTailRight sameTail leftSealRoute rightSealRoute leftSealPkg
    rightSealPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, _namePkg⟩ :=
      packet
  have leftTailUnary : UnaryHistory leftTail :=
    unary_cont_closed indexUnary tailUnary indexTailLeft
  have rightTailUnary : UnaryHistory rightTail :=
    unary_cont_closed indexUnary tailUnary indexTailRight
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed leftTailUnary sealRowUnary leftSealRoute
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed rightTailUnary sealRowUnary rightSealRoute
  have sameSeal : hsame leftSeal rightSeal :=
    cont_respects_hsame sameTail (hsame_refl sealRow) leftSealRoute rightSealRoute
  exact
    ⟨leftTailUnary, rightTailUnary, leftSealUnary, rightSealUnary, sameSeal, indexTailLeft,
      indexTailRight, leftSealRoute, rightSealRoute, leftSealPkg, rightSealPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
