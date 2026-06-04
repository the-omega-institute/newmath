import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRootLedgerObligations [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N windowRead _readbackRead sealRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg ->
      UnaryHistory R -> UnaryHistory V -> UnaryHistory W -> UnaryHistory Q ->
        UnaryHistory A -> Cont W Q windowRead -> Cont R V ledgerRead ->
          Cont windowRead A sealRead -> PkgSig bundle P pkg -> PkgSig bundle N pkg ->
            UnaryHistory ledgerRead ∧ UnaryHistory windowRead ∧ UnaryHistory sealRead ∧
              Cont R V ledgerRead ∧ Cont W Q windowRead ∧ Cont windowRead A sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig UnaryHistory
  intro _surface rUnary vUnary wUnary qUnary aUnary windowRoute ledgerRoute sealRoute
    provenancePkg namePkg
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed rUnary vUnary ledgerRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary aUnary sealRoute
  exact
    ⟨ledgerUnary, windowUnary, sealUnary, ledgerRoute, windowRoute, sealRoute,
      provenancePkg, namePkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
