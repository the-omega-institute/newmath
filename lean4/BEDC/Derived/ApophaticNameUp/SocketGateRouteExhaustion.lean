import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_socket_gate_route_exhaustion [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request gate →
        Cont gate ledger route →
          Cont route provenance socketRead →
            PkgSig bundle socketRead pkg →
              SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg ∧ hsame row socket)
                (fun row : BHist => hsame row socket ∧ UnaryHistory row)
                (fun _row : BHist =>
                  Cont socket request gate ∧ Cont gate ledger route ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory socketRead ∧
              Cont socket request gate ∧
              Cont gate ledger route ∧
              Cont route provenance socketRead ∧
              hsame ledger (append request gate) ∧
              PkgSig bundle socketRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestGate gateLedgerRoute routeProvenanceSocketRead socketReadPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, _requestUnary, _gateUnary, _ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceSocketRead
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ApophaticNameCarrier socket request gate ledger transport route provenance
            nameRow bundle pkg ∧ hsame row socket)
        (fun row : BHist => hsame row socket ∧ UnaryHistory row)
        (fun _row : BHist =>
          Cont socket request gate ∧ Cont gate ledger route ∧
            PkgSig bundle provenance pkg)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro socket ⟨carrierPacket, hsame_refl socket⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      exact ⟨source.right, unary_transport_symm socketUnary source.right⟩
    · intro _row _source
      exact ⟨socketRequestGate, gateLedgerRoute, provenancePkg⟩
  exact
    ⟨cert, socketReadUnary, socketRequestGate, gateLedgerRoute, routeProvenanceSocketRead,
      ledgerSameRequestGate, socketReadPkg⟩

end BEDC.Derived.ApophaticNameUp
