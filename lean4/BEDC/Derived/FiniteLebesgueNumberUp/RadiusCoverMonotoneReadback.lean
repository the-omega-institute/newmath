import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRadiusCoverMonotoneReadback [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow radiusRead coverRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      hsame radiusRead radius →
        Cont radiusRead mesh coverRead →
          Cont coverRead route terminalRead →
            PkgSig bundle terminalRead pkg →
              UnaryHistory cover ∧ UnaryHistory radiusRead ∧ UnaryHistory coverRead ∧
                UnaryHistory terminalRead ∧ hsame radiusRead radius ∧
                  Cont radiusRead mesh coverRead ∧ Cont coverRead route terminalRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig UnaryHistory
  intro carrier sameRadius radiusMeshCover coverRouteTerminal terminalPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_transport_symm radiusUnary sameRadius
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed radiusReadUnary meshUnary radiusMeshCover
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed coverReadUnary routeUnary coverRouteTerminal
  exact
    ⟨coverUnary, radiusReadUnary, coverReadUnary, terminalReadUnary, sameRadius,
      radiusMeshCover, coverRouteTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
