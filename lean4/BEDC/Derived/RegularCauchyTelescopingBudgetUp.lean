import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTelescopingBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTelescopingBudgetCarrier_scoped_closure [AskSetup] [PackageSetup]
    {precision windows dyadic handoff sealRow telescopeRow transport replay provenance localName
      windowRead budgetRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory precision ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
        UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory telescopeRow ∧
          UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
            UnaryHistory localName ∧ PkgSig bundle provenance pkg →
      Cont precision windows windowRead →
        Cont windowRead dyadic budgetRead →
          Cont budgetRead handoff publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row precision ∨ hsame row windows ∨ hsame row dyadic ∨
                      hsame row telescopeRow ∨ hsame row handoff ∨ hsame row sealRow ∨
                        hsame row publicRead)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory windowRead ∧ UnaryHistory budgetRead ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier precisionWindowsRoute windowDyadicRoute budgetHandoffRoute publicPkg
  obtain ⟨precisionUnary, windowsUnary, dyadicUnary, handoffUnary, _sealRowUnary,
    _telescopeRowUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed precisionUnary windowsUnary precisionWindowsRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed budgetUnary handoffUnary budgetHandoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row precision ∨ hsame row windows ∨ hsame row dyadic ∨
              hsame row telescopeRow ∨ hsame row handoff ∨ hsame row sealRow ∨
                hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, publicPkg⟩
  }
  exact ⟨cert, windowUnary, budgetUnary, publicUnary⟩

end BEDC.Derived.RegularCauchyTelescopingBudgetUp
