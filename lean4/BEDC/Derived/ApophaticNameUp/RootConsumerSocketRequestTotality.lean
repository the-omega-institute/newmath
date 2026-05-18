import BEDC.Derived.ApophaticNameUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_consumer_socket_request_totality
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont ledger nameRow rootRead ->
        PkgSig bundle rootRead pkg ->
          UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
            UnaryHistory ledger ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory nameRow ∧ UnaryHistory rootRead ∧
                Cont socket request gate ∧ Cont request gate route ∧ Cont gate ledger route ∧
                  Cont gate ledger nameRow ∧ Cont ledger nameRow rootRead ∧
                    hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier ledgerNameRoot rootPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRoot
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, rootUnary, socketRequestGate, requestGateRoute,
      gateLedgerRoute, gateLedgerNameRow, ledgerNameRoot, ledgerSameRequestGate,
      provenancePkg, rootPkg⟩

theorem ApophaticNameRootConsumerSocketRequestTotality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow rootRead →
        PkgSig bundle rootRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row socket ∨ hsame row request ∨ hsame row gate ∨
                  hsame row ledger ∨ hsame row rootRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
                  hsame row rootRead)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory rootRead ∧ Cont socket request gate ∧
                Cont gate ledger nameRow ∧ Cont ledger nameRow rootRead ∧
                  hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameRoot rootPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRoot
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row socket ∨ hsame row request ∨ hsame row gate ∨
              hsame row ledger ∨ hsame row rootRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
              hsame row rootRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro rootRead ⟨hsame_refl rootRead, rootReadUnary⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    · intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    · intro _row source
      exact ⟨provenancePkg, rootPkg, source.left⟩
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, rootReadUnary,
      socketRequestGate, gateLedgerNameRow, ledgerNameRoot, ledgerSameRequestGate,
      provenancePkg, rootPkg⟩

end BEDC.Derived.ApophaticNameUp
