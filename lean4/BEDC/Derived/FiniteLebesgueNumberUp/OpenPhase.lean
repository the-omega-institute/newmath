import BEDC.Derived.FiniteLebesgueNumberUp

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberOpenPhaseRadiusWindowExhaustion [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow rootRead radiusRead
      windowRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow rootRead ->
        Cont rootRead radius radiusRead ->
          Cont radiusRead window windowRead ->
            Cont windowRead mesh terminalRead ->
              PkgSig bundle terminalRead pkg ->
                UnaryHistory rootRead ∧ UnaryHistory radiusRead ∧
                  UnaryHistory windowRead ∧ UnaryHistory terminalRead ∧
                    Cont route nameRow rootRead ∧ Cont rootRead radius radiusRead ∧
                      Cont radiusRead window windowRead ∧
                        Cont windowRead mesh terminalRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeNameRoot rootRadiusRead readRadiusWindow windowMeshTerminal terminalPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed rootUnary radiusUnary rootRadiusRead
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed radiusReadUnary windowUnary readRadiusWindow
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed windowReadUnary meshUnary windowMeshTerminal
  exact
    ⟨rootUnary, radiusReadUnary, windowReadUnary, terminalUnary, routeNameRoot,
      rootRadiusRead, readRadiusWindow, windowMeshTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
