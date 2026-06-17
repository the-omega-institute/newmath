import BEDC.Derived.ApophaticNameUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_refusal_ledger_induction_surface [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow publicRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg →
      Cont route provenance publicRead →
        Cont ledger nameRow auditRead →
          PkgSig bundle publicRead pkg →
            PkgSig bundle auditRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row socket ∨ hsame row request ∨ hsame row gate ∨
                      hsame row ledger ∨ hsame row nameRow)
                  (fun row : BHist =>
                    UnaryHistory row ∧ hsame ledger (append request gate) ∧
                      Cont gate ledger nameRow ∧ PkgSig bundle publicRead pkg ∧
                        PkgSig bundle auditRead pkg)
                  hsame ∧
                UnaryHistory publicRead ∧ UnaryHistory auditRead ∧
                  hsame ledger (append request gate) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg
  intro carrier routeProvenancePublic ledgerNameAudit publicPkg auditPkg
  obtain ⟨_socketUnary, _requestUnary, gateUnary, ledgerUnary, _transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute, _gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, _provenancePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenancePublic
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameAudit
  have sourceAtLedger : hsame ledger ledger ∧ UnaryHistory ledger :=
    ⟨hsame_refl ledger, ledgerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row socket ∨ hsame row request ∨ hsame row gate ∨
              hsame row ledger ∨ hsame row nameRow)
          (fun row : BHist =>
            UnaryHistory row ∧ hsame ledger (append request gate) ∧
              Cont gate ledger nameRow ∧ PkgSig bundle publicRead pkg ∧
                PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledger sourceAtLedger
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, ledgerSameRequestGate, gateLedgerNameRow, publicPkg, auditPkg⟩
  }
  exact ⟨cert, publicUnary, auditUnary, ledgerSameRequestGate⟩

end BEDC.Derived.ApophaticNameUp
