import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryClosednessLedgerCoverage [AskSetup] [PackageSetup]
    {source value depth shift substitution sourceClosed valueClosed ledger route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value sourceClosed ->
        Cont value depth valueClosed ->
          Cont sourceClosed valueClosed ledger ->
            Cont ledger substitution route ->
              PkgSig bundle route pkg ->
                UnaryHistory sourceClosed ∧ UnaryHistory valueClosed ∧
                  UnaryHistory ledger ∧ UnaryHistory route ∧
                    Cont sourceClosed valueClosed ledger ∧ Cont ledger substitution route ∧
                      PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro classifier sourceValueClosed valueDepthClosed closednessLedger ledgerRoute routePkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, _shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sourceClosedUnary : UnaryHistory sourceClosed :=
    unary_cont_closed sourceUnary valueUnary sourceValueClosed
  have valueClosedUnary : UnaryHistory valueClosed :=
    unary_cont_closed valueUnary depthUnary valueDepthClosed
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceClosedUnary valueClosedUnary closednessLedger
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary substitutionUnary ledgerRoute
  exact
    ⟨sourceClosedUnary, valueClosedUnary, ledgerUnary, routeUnary, closednessLedger,
      ledgerRoute, routePkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
