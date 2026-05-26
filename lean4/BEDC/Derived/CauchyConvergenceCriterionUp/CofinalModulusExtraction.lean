import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_cofinal_modulus_extraction
    [AskSetup] [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert
      regularRead realSealRead cofinalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg ->
      Cont handoff route regularRead ->
        Cont sealRow route realSealRead ->
          Cont regularRead realSealRead cofinalRead ->
            PkgSig bundle regularRead pkg ->
              PkgSig bundle realSealRead pkg ->
                UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
                  UnaryHistory handoff ∧ UnaryHistory regularRead ∧
                    UnaryHistory realSealRead ∧ UnaryHistory cofinalRead ∧
                      Cont schedule modulus dyadic ∧ Cont dyadic handoff sealRow ∧
                        Cont handoff route regularRead ∧ Cont sealRow route realSealRead ∧
                          Cont regularRead realSealRead cofinalRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle regularRead pkg ∧
                              PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier handoffRouteRegular sealRouteReal regularRealCofinal regularPkg realPkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary,
    _transportUnary, routeUnary, _provenanceUnary, _localCertUnary, scheduleModulusDyadic,
    dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed handoffUnary routeUnary handoffRouteRegular
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed sealUnary routeUnary sealRouteReal
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed regularUnary realSealUnary regularRealCofinal
  exact
    ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, regularUnary, realSealUnary,
      cofinalUnary, scheduleModulusDyadic, dyadicHandoffSeal, handoffRouteRegular,
      sealRouteReal, regularRealCofinal, provenancePkg, regularPkg, realPkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
