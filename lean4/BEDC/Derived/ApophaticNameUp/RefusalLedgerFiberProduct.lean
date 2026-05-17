import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_refusal_ledger_fiber_product [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow ledgerRead →
        PkgSig bundle ledgerRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row ledger ∧ hsame ledger (append request gate))
              (fun row : BHist => hsame row (append request gate))
              (fun _row : BHist =>
                Cont request gate route ∧ Cont gate ledger route ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            hsame ledger (append request gate) ∧
            Cont request gate route ∧
            Cont gate ledger route ∧
            Cont ledger nameRow ledgerRead ∧
            PkgSig bundle provenance pkg ∧
            PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameRead ledgerReadPkg
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, _ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketRequestGate, requestGateRoute,
    gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledger ∧ hsame ledger (append request gate))
          (fun row : BHist => hsame row (append request gate))
          (fun _row : BHist =>
            Cont request gate route ∧ Cont gate ledger route ∧ PkgSig bundle provenance pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger ⟨hsame_refl ledger, ledgerSameRequestGate⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    · intro _row source
      exact hsame_trans source.left source.right
    · intro _row _source
      exact ⟨requestGateRoute, gateLedgerRoute, provenancePkg⟩
  exact
    ⟨cert, ledgerSameRequestGate, requestGateRoute, gateLedgerRoute, ledgerNameRead,
      provenancePkg, ledgerReadPkg⟩

end BEDC.Derived.ApophaticNameUp
