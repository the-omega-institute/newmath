import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyRepletionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyRepletionBoundaryCarrier [AskSetup] [PackageSetup]
    (S R D Q E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory Q ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont S R D ∧ Cont D Q E ∧ hsame H C ∧ hsame N E ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RegularCauchyRepletionBoundaryNamecertObligations [AskSetup] [PackageSetup]
    {S R D Q E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRepletionBoundaryCarrier S R D Q E H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row Q ∨ hsame row E)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧
            UnaryHistory Q ∧ UnaryHistory E := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨sUnary, rUnary, dUnary, qUnary, eUnary, _hUnary, _cUnary, _pUnary, nUnary,
    _streamRoute, _sealRoute, _transportSame, nameSealSame, pPkg, _nPkg⟩ := carrier
  have sourceWitness : hsame N N ∧ UnaryHistory N :=
    ⟨hsame_refl N, nUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row Q ∨ hsame row E)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceWitness
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (hsame_trans source.left nameSealSame))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pPkg⟩
  }
  exact ⟨cert, sUnary, rUnary, dUnary, qUnary, eUnary⟩

end BEDC.Derived.RegularCauchyRepletionBoundaryUp
