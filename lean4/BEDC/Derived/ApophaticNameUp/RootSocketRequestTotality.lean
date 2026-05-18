import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameRootSocketRequestTotality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead requestRead
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request socketRead →
        Cont request gate requestRead →
          Cont ledger nameRow ledgerRead →
            PkgSig bundle ledgerRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row nameRow ∧ Cont socket request socketRead ∧
                      Cont request gate requestRead ∧ Cont ledger nameRow ledgerRead)
                  (fun row : BHist =>
                    hsame row nameRow ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle ledgerRead pkg)
                  hsame ∧
                UnaryHistory socketRead ∧ UnaryHistory requestRead ∧
                  UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestRead requestGateRead ledgerNameRead ledgerReadPkg
  rcases carrier with
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
      _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
      _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed socketUnary requestUnary socketRequestRead
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed requestUnary gateUnary requestGateRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRead
  have sourceName : (fun row : BHist => hsame row nameRow ∧ UnaryHistory row) nameRow :=
    ⟨hsame_refl nameRow, nameRowUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row nameRow ∧ Cont socket request socketRead ∧
              Cont request gate requestRead ∧ Cont ledger nameRow ledgerRead)
          (fun row : BHist =>
            hsame row nameRow ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle ledgerRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro nameRow sourceName
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
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, socketRequestRead, requestGateRead, ledgerNameRead⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg, ledgerReadPkg⟩
    }
  exact ⟨cert, socketReadUnary, requestReadUnary, ledgerReadUnary⟩

end BEDC.Derived.ApophaticNameUp
