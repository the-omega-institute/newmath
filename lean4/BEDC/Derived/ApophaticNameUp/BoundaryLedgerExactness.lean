import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_boundary_ledger_exactness [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow requestRead boundaryRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont request gate requestRead →
        Cont ledger nameRow boundaryRead →
          PkgSig bundle requestRead pkg →
            PkgSig bundle boundaryRead pkg →
              UnaryHistory requestRead ∧ UnaryHistory boundaryRead ∧
                Cont request gate requestRead ∧ Cont ledger nameRow boundaryRead ∧
                  hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle requestRead pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier requestGateRead ledgerNameBoundary requestPkg boundaryPkg
  obtain ⟨_socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed requestUnary gateUnary requestGateRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameBoundary
  exact
    ⟨requestReadUnary, boundaryReadUnary, requestGateRead, ledgerNameBoundary,
      ledgerSameRequestGate, provenancePkg, requestPkg, boundaryPkg⟩

end BEDC.Derived.ApophaticNameUp
