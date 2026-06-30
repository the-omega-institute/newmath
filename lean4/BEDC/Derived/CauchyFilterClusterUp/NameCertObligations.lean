import BEDC.Derived.CauchyFilterClusterUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyFilterClusterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyFilterClusterCarrier [AskSetup] [PackageSetup]
    (F M U W Q S D E H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory F ∧ UnaryHistory M ∧ UnaryHistory U ∧ UnaryHistory W ∧
    UnaryHistory Q ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle N pkg

theorem CauchyFilterCluster_namecert_obligations [AskSetup] [PackageSetup]
    {F M U W Q S D E H C P N auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterClusterCarrier F M U W Q S D E H C P N bundle pkg ->
      Cont E H auditRead ->
        PkgSig bundle auditRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row F ∨ hsame row M ∨ hsame row U ∨ hsame row W ∨
                  hsame row Q ∨ hsame row S ∨ hsame row D ∨ hsame row E ∨
                    hsame row auditRead)
              (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
              hsame ∧
            UnaryHistory F ∧ UnaryHistory M ∧ UnaryHistory U ∧ UnaryHistory W ∧
              UnaryHistory Q ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory E ∧
                UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier auditRoute auditPkg
  obtain ⟨fUnary, mUnary, uUnary, wUnary, qUnary, sUnary, dUnary, eUnary, hUnary,
    _cUnary, _pUnary, _nUnary, _namePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed eUnary hUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row M ∨ hsame row U ∨ hsame row W ∨
              hsame row Q ∨ hsame row S ∨ hsame row D ∨ hsame row E ∨
                hsame row auditRead)
          (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, auditPkg⟩
  }
  exact
    ⟨cert, fUnary, mUnary, uUnary, wUnary, qUnary, sUnary, dUnary, eUnary,
      auditUnary⟩

end BEDC.Derived.CauchyFilterClusterUp
