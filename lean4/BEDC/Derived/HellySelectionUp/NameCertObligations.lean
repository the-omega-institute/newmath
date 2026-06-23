import BEDC.Derived.HellySelectionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HellySelectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HellySelectionCarrier [AskSetup] [PackageSetup]
    (B A W S R E T C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory B ∧ UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧
    UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory T ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle N pkg

theorem HellySelection_namecert_obligations [AskSetup] [PackageSetup]
    {B A W S R E T C P N auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HellySelectionCarrier B A W S R E T C P N bundle pkg ->
      Cont E T auditRead ->
        PkgSig bundle auditRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row B ∨ hsame row A ∨ hsame row W ∨ hsame row S ∨
                  hsame row R ∨ hsame row E ∨ hsame row auditRead)
              (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
              hsame ∧
            UnaryHistory B ∧ UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧
              UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier auditRoute auditPkg
  obtain ⟨bUnary, aUnary, wUnary, sUnary, rUnary, eUnary, tUnary, _cUnary, _pUnary,
    _nUnary, _namePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed eUnary tUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row W ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row auditRead)
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, auditPkg⟩
  }
  exact ⟨cert, bUnary, aUnary, wUnary, sUnary, rUnary, eUnary, auditUnary⟩

end BEDC.Derived.HellySelectionUp
