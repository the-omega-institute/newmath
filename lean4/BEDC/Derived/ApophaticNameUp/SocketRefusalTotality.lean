import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_socket_refusal_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead gateRead
      citationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request socketRead →
        Cont socketRead gate gateRead →
          Cont gateRead ledger citationRead →
            PkgSig bundle citationRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧ hsame row socket)
                  (fun row : BHist =>
                    hsame row socket ∧ UnaryHistory row ∧ Cont socket request socketRead)
                  (fun _row : BHist =>
                    Cont socketRead gate gateRead ∧ Cont gateRead ledger citationRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle citationRead pkg)
                  hsame ∧
                UnaryHistory socketRead ∧ UnaryHistory gateRead ∧
                  UnaryHistory citationRead ∧ Cont socket request socketRead ∧
                    Cont socketRead gate gateRead ∧ Cont gateRead ledger citationRead ∧
                      hsame ledger (append request gate) ∧ PkgSig bundle citationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketCont gateCont citationCont citationPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed socketUnary requestUnary socketCont
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed socketReadUnary gateUnary gateCont
  have citationReadUnary : UnaryHistory citationRead :=
    unary_cont_closed gateReadUnary ledgerUnary citationCont
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row socket)
          (fun row : BHist =>
            hsame row socket ∧ UnaryHistory row ∧ Cont socket request socketRead)
          (fun _row : BHist =>
            Cont socketRead gate gateRead ∧ Cont gateRead ledger citationRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle citationRead pkg)
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
          ⟨source.right, unary_transport_symm socketUnary source.right, socketCont⟩
      ledger_sound := by
        intro _row _source
        exact ⟨gateCont, citationCont, provenancePkg, citationPkg⟩
    }
  exact
    ⟨cert, socketReadUnary, gateReadUnary, citationReadUnary, socketCont, gateCont,
      citationCont, ledgerSameRequestGate, citationPkg⟩

end BEDC.Derived.ApophaticNameUp
