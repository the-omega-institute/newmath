import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_request_classifier_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow requestRead gateRead
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request requestRead →
        Cont request gate gateRead →
          Cont gate ledger rootRead →
            PkgSig bundle rootRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧ hsame row request)
                  (fun row : BHist =>
                    hsame row request ∧ UnaryHistory row ∧
                      Cont socket request requestRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
                      hsame row request)
                  hsame ∧
                UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
                  UnaryHistory ledger ∧ UnaryHistory requestRead ∧ UnaryHistory gateRead ∧
                    UnaryHistory rootRead ∧ Cont socket request requestRead ∧
                      Cont request gate gateRead ∧ Cont gate ledger rootRead ∧
                        hsame ledger (append request gate) ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier requestReadRoute gateReadRoute rootReadRoute rootPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketRequestGate,
    _requestGateRoute, _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate,
    provenancePkg⟩ := carrier
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed socketUnary requestUnary requestReadRoute
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed requestUnary gateUnary gateReadRoute
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed gateUnary ledgerUnary rootReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row request)
          (fun row : BHist =>
            hsame row request ∧ UnaryHistory row ∧ Cont socket request requestRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
              hsame row request)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro request ⟨carrierPacket, hsame_refl request⟩
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
          ⟨source.right, unary_transport requestUnary (hsame_symm source.right),
            requestReadRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, rootPkg, source.right⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, requestReadUnary,
      gateReadUnary, rootReadUnary, requestReadRoute, gateReadRoute, rootReadRoute,
      ledgerSameRequestGate, provenancePkg, rootPkg⟩

end BEDC.Derived.ApophaticNameUp
