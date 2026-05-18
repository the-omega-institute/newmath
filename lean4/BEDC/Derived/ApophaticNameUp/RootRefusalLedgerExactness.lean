import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_refusal_ledger_exactness [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow requestRead gateRead
      ledgerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont socket request requestRead ->
        Cont request gate gateRead ->
          Cont gate ledger ledgerRead ->
            Cont ledger route publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory gateRead ∧ UnaryHistory ledgerRead ∧ UnaryHistory publicRead ∧
                  Cont request gate gateRead ∧ Cont gate ledger ledgerRead ∧
                    Cont ledger route publicRead ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row requestRead ∨ hsame row gateRead ∨
                            hsame row ledgerRead ∨ hsame row publicRead)
                        (fun row : BHist =>
                          PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                            hsame row publicRead)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestRead requestGateRead gateLedgerRead ledgerRoutePublic publicPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed socketUnary requestUnary socketRequestRead
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed requestUnary gateUnary requestGateRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed ledgerUnary routeUnary ledgerRoutePublic
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row requestRead ∨ hsame row gateRead ∨ hsame row ledgerRead ∨
            hsame row publicRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
            hsame row publicRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, publicPkg, source.left⟩
    }
  exact
    ⟨gateReadUnary, ledgerReadUnary, publicReadUnary, requestGateRead, gateLedgerRead,
      ledgerRoutePublic, cert⟩

end BEDC.Derived.ApophaticNameUp
