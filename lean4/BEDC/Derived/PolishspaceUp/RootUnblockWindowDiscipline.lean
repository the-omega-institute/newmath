import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceRootUnblockWindowDiscipline [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport windowRead readbackRoute
      analyticRead provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory complete →
        UnaryHistory separable →
          UnaryHistory stream →
            UnaryHistory readback →
              UnaryHistory ledger →
                UnaryHistory transport →
                  Cont stream readback windowRead →
                    Cont windowRead ledger readbackRoute →
                      Cont readbackRoute metric analyticRead →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle localName pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row analyticRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row stream ∨ hsame row readback ∨
                                    hsame row ledger ∨ hsame row metric ∨
                                      hsame row analyticRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory windowRead ∧ UnaryHistory readbackRoute ∧
                                UnaryHistory analyticRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont SemanticNameCert hsame UnaryHistory
  intro metricUnary _completeUnary _separableUnary streamUnary readbackUnary ledgerUnary
    _transportUnary streamReadbackWindow windowLedgerRoute routeMetricAnalytic provenancePkg
    localNamePkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary readbackUnary streamReadbackWindow
  have routeUnary : UnaryHistory readbackRoute :=
    unary_cont_closed windowUnary ledgerUnary windowLedgerRoute
  have analyticUnary : UnaryHistory analyticRead :=
    unary_cont_closed routeUnary metricUnary routeMetricAnalytic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row analyticRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨ hsame row metric ∨
              hsame row analyticRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro analyticRead ⟨hsame_refl analyticRead, analyticUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, windowUnary, routeUnary, analyticUnary⟩

end BEDC.Derived.PolishspaceUp
