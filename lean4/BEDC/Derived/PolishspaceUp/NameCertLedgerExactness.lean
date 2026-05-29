import BEDC.Derived.PolishspaceUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceNamecertLedgerExactness [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport _replay provenance localName
      exactRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory complete →
        UnaryHistory separable →
          UnaryHistory stream →
            UnaryHistory readback →
              UnaryHistory ledger →
                UnaryHistory transport →
                  Cont stream readback exactRead →
                    Cont exactRead ledger finalRead →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle localName pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row metric ∨ hsame row complete ∨
                                  hsame row separable ∨ hsame row stream ∨
                                    hsame row readback ∨ hsame row ledger ∨
                                      hsame row finalRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle localName pkg)
                              hsame ∧
                            UnaryHistory exactRead ∧ UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro _metricUnary _completeUnary _separableUnary streamUnary readbackUnary ledgerUnary
    _transportUnary exactReadRoute finalReadRoute provenancePkg localNamePkg
  have exactReadUnary : UnaryHistory exactRead :=
    unary_cont_closed streamUnary readbackUnary exactReadRoute
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed exactReadUnary ledgerUnary finalReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                hsame row finalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro finalRead ⟨hsame_refl finalRead, finalReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, exactReadUnary, finalReadUnary⟩

end BEDC.Derived.PolishspaceUp
