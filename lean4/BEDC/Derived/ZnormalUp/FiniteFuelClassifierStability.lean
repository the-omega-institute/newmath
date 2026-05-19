import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_finite_fuel_classifier_stability [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name fuel' terminal'
      continuationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      hsame fuel fuel' →
        Cont typed fuel' terminal' →
          Cont terminal' normal continuationRead →
            PkgSig bundle continuationRead pkg →
              hsame terminal terminal' ∧ UnaryHistory fuel' ∧ UnaryHistory terminal' ∧
                UnaryHistory continuationRead ∧ Cont typed fuel' terminal' ∧
                  Cont terminal' normal continuationRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle continuationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet fuelSame typedFuelTerminal' terminalNormalContinuationRead continuationReadPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalSame : hsame terminal terminal' :=
    cont_respects_hsame (hsame_refl typed) fuelSame typedFuelTerminal typedFuelTerminal'
  have fuelUnary' : UnaryHistory fuel' :=
    unary_transport fuelUnary fuelSame
  have terminalUnary' : UnaryHistory terminal' :=
    unary_cont_closed typedUnary fuelUnary' typedFuelTerminal'
  have continuationReadUnary : UnaryHistory continuationRead :=
    unary_cont_closed terminalUnary' normalUnary terminalNormalContinuationRead
  exact
    ⟨terminalSame, fuelUnary', terminalUnary', continuationReadUnary,
      typedFuelTerminal', terminalNormalContinuationRead, provenancePkg,
      continuationReadPkg⟩

end BEDC.Derived.ZnormalUp
