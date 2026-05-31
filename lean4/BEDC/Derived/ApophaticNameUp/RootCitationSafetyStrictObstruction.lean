import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_citation_safety_strict_obstruction
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow citationRead
      obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont route provenance citationRead ->
        PkgSig bundle citationRead pkg ->
          Cont citationRead ledger obstructionRead ->
            PkgSig bundle obstructionRead pkg ->
              UnaryHistory citationRead ∧ UnaryHistory obstructionRead ∧
                Cont route provenance citationRead ∧
                  Cont citationRead ledger obstructionRead ∧
                    hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle citationRead pkg ∧
                        PkgSig bundle obstructionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier routeProvenanceCitation citationPkg citationLedgerObstruction
    obstructionPkg
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have citationUnary : UnaryHistory citationRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceCitation
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed citationUnary ledgerUnary citationLedgerObstruction
  exact
    ⟨citationUnary, obstructionUnary, routeProvenanceCitation, citationLedgerObstruction,
      ledgerSameRequestGate, provenancePkg, citationPkg, obstructionPkg⟩

end BEDC.Derived.ApophaticNameUp
