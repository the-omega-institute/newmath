import BEDC.Derived.CauchyCompletionMinimalityUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionMinimalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMinimalityDenseImageCoverage [AskSetup] [PackageSetup]
    {C E denseRead P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C → UnaryHistory E → Cont C E denseRead → PkgSig bundle P pkg →
      PkgSig bundle N pkg →
        SemanticNameCert
            (fun row : BHist => hsame row denseRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row C ∨ hsame row E ∨ hsame row denseRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont C E denseRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
            hsame ∧
          UnaryHistory denseRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro cUnary eUnary denseRoute provenancePkg namePkg
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed cUnary eUnary denseRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row denseRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row C ∨ hsame row E ∨ hsame row denseRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C E denseRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro denseRead ⟨hsame_refl denseRead, denseUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, denseRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, denseUnary⟩

end BEDC.Derived.CauchyCompletionMinimalityUp
