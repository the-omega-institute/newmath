import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberLedgerTransport [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow radiusRead meshRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      hsame radiusRead radius ->
        Cont radiusRead mesh meshRead ->
          Cont meshRead route terminalRead ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
                UnaryHistory radiusRead ∧ UnaryHistory mesh ∧ UnaryHistory meshRead ∧
                  UnaryHistory terminalRead ∧ hsame radiusRead radius ∧
                    Cont radiusRead mesh meshRead ∧ Cont meshRead route terminalRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier sameRadius radiusMeshRead meshTerminal terminalPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_transport radiusUnary (hsame_symm sameRadius)
  have meshReadUnary : UnaryHistory meshRead :=
    unary_cont_closed radiusReadUnary meshUnary radiusMeshRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed meshReadUnary routeUnary meshTerminal
  exact
    ⟨coverUnary, windowUnary, radiusUnary, radiusReadUnary, meshUnary, meshReadUnary,
      terminalReadUnary, sameRadius, radiusMeshRead, meshTerminal, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
