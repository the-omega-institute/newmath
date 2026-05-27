import BEDC.Derived.MetaCICClosureTraceUp

namespace BEDC.Derived.MetaCICClosureTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICClosureTraceCarrier_decidability_readback_frontier
    [AskSetup] [PackageSetup] {S U V B R G K H C P N decisionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg →
      Cont K N decisionRead →
        PkgSig bundle decisionRead pkg →
          UnaryHistory S ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory B ∧
            UnaryHistory R ∧ UnaryHistory G ∧ UnaryHistory K ∧ UnaryHistory N ∧
              UnaryHistory decisionRead ∧ Cont S U V ∧ Cont V G K ∧ Cont B R C ∧
                Cont K N decisionRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle decisionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier decisionRoute decisionPkg
  obtain ⟨SUnary, UUnary, VUnary, BUnary, RUnary, GUnary, KUnary, _HUnary, _CUnary,
    _PUnary, NUnary, shiftSubstitution, generatorPackage, betaRoute, pkgSig⟩ := carrier
  have decisionUnary : UnaryHistory decisionRead :=
    unary_cont_closed KUnary NUnary decisionRoute
  exact
    ⟨SUnary, UUnary, VUnary, BUnary, RUnary, GUnary, KUnary, NUnary, decisionUnary,
      shiftSubstitution, generatorPackage, betaRoute, decisionRoute, pkgSig, decisionPkg⟩

end BEDC.Derived.MetaCICClosureTraceUp
