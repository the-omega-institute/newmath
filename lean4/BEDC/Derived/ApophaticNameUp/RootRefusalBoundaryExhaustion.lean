import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_refusal_boundary_exhaustion [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow rootRead →
        PkgSig bundle rootRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                  nameRow bundle pkg ∧ hsame row ledger)
              (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
                  hsame row (append request gate) ∧ Cont ledger nameRow rootRead)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory rootRead ∧ Cont socket request gate ∧
                Cont ledger nameRow rootRead ∧ hsame ledger (append request gate) ∧
                  PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameRoot rootPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRoot
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row ledger)
          (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
              hsame row (append request gate) ∧ Cont ledger nameRow rootRead)
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
        ⟨provenancePkg, rootPkg, hsame_trans rowSameLedger ledgerSameRequestGate,
          ledgerNameRoot⟩
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, rootUnary,
      socketRequestGate, ledgerNameRoot, ledgerSameRequestGate, rootPkg⟩

end BEDC.Derived.ApophaticNameUp
