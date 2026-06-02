import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_source_net_exhaustion [AskSetup] [PackageSetup]
    {S K R Q E H C P N sourceNet netLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K sourceNet ->
        Cont sourceNet H netLedger ->
          PkgSig bundle netLedger pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row netLedger ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row K ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N ∨ hsame row sourceNet ∨
                      hsame row netLedger)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont S K sourceNet ∧ Cont sourceNet H netLedger ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle netLedger pkg)
                hsame ∧
              UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory sourceNet ∧
                UnaryHistory netLedger ∧ Cont S K sourceNet ∧ Cont sourceNet H netLedger := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier sourceRoute ledgerRoute ledgerPkg
  obtain ⟨SUnary, KUnary, _RUnary, _QUnary, _EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have sourceNetUnary : UnaryHistory sourceNet :=
    unary_cont_closed SUnary KUnary sourceRoute
  have netLedgerUnary : UnaryHistory netLedger :=
    unary_cont_closed sourceNetUnary HUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row netLedger ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row K ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row sourceNet ∨ hsame row netLedger)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S K sourceNet ∧ Cont sourceNet H netLedger ∧
              PkgSig bundle P pkg ∧ PkgSig bundle netLedger pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro netLedger ⟨hsame_refl netLedger, netLedgerUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, ledgerRoute, carrierPkg, ledgerPkg⟩
  }
  exact
    ⟨cert, SUnary, KUnary, sourceNetUnary, netLedgerUnary, sourceRoute, ledgerRoute⟩

end BEDC.Derived.BolzanoWeierstrassUp
