import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_selector_seal_synchronization
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name selectorWindow
      selectorTail selectorSeal synchronized : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index windows selectorWindow →
        Cont modulus tolerance selectorTail →
          Cont selectorTail sealRow selectorSeal →
            Cont selectorWindow selectorSeal synchronized →
              PkgSig bundle synchronized pkg →
                UnaryHistory selectorWindow ∧ UnaryHistory selectorTail ∧
                  UnaryHistory selectorSeal ∧ UnaryHistory synchronized ∧
                    hsame tail selectorTail ∧ Cont index windows selectorWindow ∧
                      Cont modulus tolerance selectorTail ∧
                        Cont selectorTail sealRow selectorSeal ∧
                          Cont selectorWindow selectorSeal synchronized ∧
                            PkgSig bundle name pkg ∧
                              PkgSig bundle synchronized pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexWindowsSelector modulusToleranceSelector selectorSealRoute
    synchronizedRoute synchronizedPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, _tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have selectorTailSame : hsame tail selectorTail :=
    cont_respects_hsame (hsame_refl modulus) (hsame_refl tolerance) modulusToleranceTail
      modulusToleranceSelector
  have selectorWindowUnary : UnaryHistory selectorWindow :=
    unary_cont_closed indexUnary windowsUnary indexWindowsSelector
  have selectorTailUnary : UnaryHistory selectorTail :=
    unary_cont_closed modulusUnary toleranceUnary modulusToleranceSelector
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed selectorTailUnary sealRowUnary selectorSealRoute
  have synchronizedUnary : UnaryHistory synchronized :=
    unary_cont_closed selectorWindowUnary selectorSealUnary synchronizedRoute
  exact
    ⟨selectorWindowUnary, selectorTailUnary, selectorSealUnary, synchronizedUnary,
      selectorTailSame, indexWindowsSelector, modulusToleranceSelector, selectorSealRoute,
      synchronizedRoute, namePkg, synchronizedPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
