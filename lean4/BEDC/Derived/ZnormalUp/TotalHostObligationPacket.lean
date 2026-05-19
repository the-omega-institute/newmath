import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalTotalHostObligationPacket_row_exposure [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name support : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed terminal support ->
        PkgSig bundle support pkg ->
          UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
            UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory transports ∧
              UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                UnaryHistory support ∧ Cont typed fuel terminal ∧
                  Cont terminal normal continuation ∧ Cont continuation transports routes ∧
                    Cont typed terminal support ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle support pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet supportRoute supportPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have supportUnary : UnaryHistory support :=
    unary_cont_closed typedUnary terminalUnary supportRoute
  exact
    ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
      transportsUnary, routesUnary, provenanceUnary, nameUnary, supportUnary,
      typedFuelTerminal, terminalNormalContinuation, continuationTransportsRoutes,
      supportRoute, namePkg, provenancePkg, supportPkg⟩

end BEDC.Derived.ZnormalUp
