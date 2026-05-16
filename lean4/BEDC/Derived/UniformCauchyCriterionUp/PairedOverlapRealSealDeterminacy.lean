import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_paired_overlap_real_seal_determinacy [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name leftTail
      rightTail leftSeal rightSeal leftOverlap rightOverlap : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail leftTail ->
        Cont index tail rightTail ->
          Cont tail sealRow leftSeal ->
            Cont tail sealRow rightSeal ->
              Cont leftTail leftSeal leftOverlap ->
                Cont rightTail rightSeal rightOverlap ->
                  PkgSig bundle leftOverlap pkg ->
                    PkgSig bundle rightOverlap pkg ->
                      UnaryHistory leftOverlap ∧ UnaryHistory rightOverlap ∧
                        hsame leftTail rightTail ∧ hsame leftSeal rightSeal ∧
                          hsame leftOverlap rightOverlap ∧ Cont leftTail leftSeal leftOverlap ∧
                            Cont rightTail rightSeal rightOverlap ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle leftOverlap pkg ∧
                                PkgSig bundle rightOverlap pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet leftTailRoute rightTailRoute leftSealRoute rightSealRoute leftOverlapRoute
    rightOverlapRoute leftOverlapPkg rightOverlapPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have leftTailUnary : UnaryHistory leftTail :=
    unary_cont_closed indexUnary tailUnary leftTailRoute
  have rightTailUnary : UnaryHistory rightTail :=
    unary_cont_closed indexUnary tailUnary rightTailRoute
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed tailUnary sealRowUnary leftSealRoute
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed tailUnary sealRowUnary rightSealRoute
  have leftOverlapUnary : UnaryHistory leftOverlap :=
    unary_cont_closed leftTailUnary leftSealUnary leftOverlapRoute
  have rightOverlapUnary : UnaryHistory rightOverlap :=
    unary_cont_closed rightTailUnary rightSealUnary rightOverlapRoute
  have sameTail : hsame leftTail rightTail :=
    cont_deterministic leftTailRoute rightTailRoute
  have sameSeal : hsame leftSeal rightSeal :=
    cont_deterministic leftSealRoute rightSealRoute
  have sameOverlap : hsame leftOverlap rightOverlap :=
    cont_respects_hsame sameTail sameSeal leftOverlapRoute rightOverlapRoute
  exact
    ⟨leftOverlapUnary, rightOverlapUnary, sameTail, sameSeal, sameOverlap,
      leftOverlapRoute, rightOverlapRoute, namePkg, leftOverlapPkg, rightOverlapPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
