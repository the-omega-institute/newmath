import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_non_escape_certificate [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow exported →
        PkgSig bundle exported pkg →
          SemanticNameCert
              (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
              (fun row : BHist => hsame row ledger)
              (fun row : BHist => hsame row ledger ∧ PkgSig bundle exported pkg)
              hsame ∧
            UnaryHistory exported ∧
            Cont ledger nameRow exported ∧
            hsame ledger (append request gate) ∧
            PkgSig bundle provenance pkg ∧
            PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameExported exportedPkg
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameExported
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
          (fun row : BHist => hsame row ledger)
          (fun row : BHist => hsame row ledger ∧ PkgSig bundle exported pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger ⟨hsame_refl ledger, ledgerUnary⟩
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
      exact source.left
    · intro _row source
      exact ⟨source.left, exportedPkg⟩
  exact
    ⟨cert, exportedUnary, ledgerNameExported, ledgerSameRequestGate, provenancePkg,
      exportedPkg⟩

end BEDC.Derived.ApophaticNameUp
