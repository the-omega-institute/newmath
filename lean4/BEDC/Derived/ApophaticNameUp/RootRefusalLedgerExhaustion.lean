import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_refusal_ledger_exhaustion [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow barredRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont gate ledger barredRead →
        PkgSig bundle barredRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                  nameRow bundle pkg ∧ hsame row ledger)
              (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle barredRead pkg ∧
                  hsame row (append request gate) ∧ Cont gate ledger barredRead)
              hsame ∧
            UnaryHistory ledger ∧ Cont gate ledger barredRead ∧
            hsame ledger (append request gate) ∧ PkgSig bundle barredRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier gateLedgerBarred barredPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row ledger)
          (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle barredRead pkg ∧
              hsame row (append request gate) ∧ Cont gate ledger barredRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger ⟨carrierPacket, hsame_refl ledger⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameLedger : hsame row ledger := source.right
      exact
        ⟨hsame_trans rowSameLedger ledgerSameRequestGate,
          unary_transport ledgerUnary (hsame_symm rowSameLedger)⟩
    · intro row source
      have rowSameLedger : hsame row ledger := source.right
      exact
        ⟨provenancePkg, barredPkg,
          hsame_trans rowSameLedger ledgerSameRequestGate, gateLedgerBarred⟩
  exact ⟨cert, ledgerUnary, gateLedgerBarred, ledgerSameRequestGate, barredPkg⟩

end BEDC.Derived.ApophaticNameUp
