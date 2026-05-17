import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_socket_refusal_correspondence [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ->
      Cont socket request socketRead ->
        PkgSig bundle socketRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                bundle pkg ∧ hsame row socket)
            (fun row : BHist => hsame row socket ∧ UnaryHistory row ∧
              Cont socket request socketRead)
            (fun row : BHist =>
              PkgSig bundle provenance pkg ∧ PkgSig bundle socketRead pkg ∧
                hsame row socket ∧ Cont gate ledger route)
            hsame ∧ UnaryHistory socket ∧ UnaryHistory gate ∧ UnaryHistory ledger ∧
              UnaryHistory socketRead ∧ Cont socket request socketRead ∧
                Cont gate ledger route ∧ hsame ledger (append request gate) ∧
                  PkgSig bundle socketRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestRead socketReadPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed socketUnary requestUnary socketRequestRead
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
            bundle pkg ∧ hsame row socket)
        (fun row : BHist => hsame row socket ∧ UnaryHistory row ∧
          Cont socket request socketRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle socketRead pkg ∧
            hsame row socket ∧ Cont gate ledger route)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro socket ⟨carrierPacket, hsame_refl socket⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport socketUnary (hsame_symm source.right),
            socketRequestRead⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, socketReadPkg, source.right, gateLedgerRoute⟩
    }
  exact
    ⟨cert, socketUnary, gateUnary, ledgerUnary, socketReadUnary, socketRequestRead,
      gateLedgerRoute, ledgerSameRequestGate, socketReadPkg⟩

end BEDC.Derived.ApophaticNameUp
