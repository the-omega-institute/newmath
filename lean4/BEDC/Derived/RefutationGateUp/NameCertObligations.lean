import BEDC.Derived.RefutationGateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RefutationGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RefutationGateCarrier [AskSetup] [PackageSetup]
    (Q S B A D T H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory Q ∧ UnaryHistory S ∧ UnaryHistory B ∧ UnaryHistory A ∧
    UnaryHistory D ∧ UnaryHistory T ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont Q S B ∧ Cont A D T ∧ hsame H C ∧
        hsame N T ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RefutationGateNamecertObligations [AskSetup] [PackageSetup]
    {Q S B A D T H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RefutationGateCarrier Q S B A D T H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row A ∨ hsame row D ∨ hsame row T)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame ∧ UnaryHistory Q ∧ UnaryHistory S ∧ UnaryHistory B ∧
            UnaryHistory A ∧ UnaryHistory D ∧ UnaryHistory T := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨qUnary, sUnary, bUnary, aUnary, dUnary, tUnary, _hUnary, _cUnary, _pUnary,
    nUnary, _claimRoute, _tasteRoute, _transportSame, nameTasteSame, pPkg, _nPkg⟩ :=
    carrier
  have sourceWitness : hsame N N ∧ UnaryHistory N :=
    ⟨hsame_refl N, nUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row A ∨ hsame row D ∨ hsame row T)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (hsame_trans source.left nameTasteSame))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pPkg⟩
  }
  exact ⟨cert, qUnary, sUnary, bUnary, aUnary, dUnary, tUnary⟩

end BEDC.Derived.RefutationGateUp
