import BEDC.Derived.MetaCICDecidableBoundaryUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetaCICDecidableBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICDecidableBoundaryClassifierStability [AskSetup] [PackageSetup]
    {checker _structural boundedNormal _finished _refusal transport replay provenance localName
      transportedChecker transportedBounded replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory checker →
      UnaryHistory boundedNormal →
        UnaryHistory transport →
          UnaryHistory replay →
            hsame transportedChecker checker →
              hsame transportedBounded boundedNormal →
                Cont transportedChecker transportedBounded replayRead →
                  PkgSig bundle provenance pkg →
                    PkgSig bundle localName pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row checker ∨ hsame row boundedNormal ∨
                              hsame row transport ∨ hsame row replay ∨ hsame row replayRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                              PkgSig bundle provenance pkg)
                          hsame ∧
                        UnaryHistory transportedChecker ∧ UnaryHistory transportedBounded ∧
                          UnaryHistory replayRead ∧
                            Cont transportedChecker transportedBounded replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro checkerUnary boundedUnary _transportUnary _replayUnary sameChecker sameBounded
  intro replayRoute provenancePkg localPkg
  have transportedCheckerUnary : UnaryHistory transportedChecker :=
    unary_transport checkerUnary (hsame_symm sameChecker)
  have transportedBoundedUnary : UnaryHistory transportedBounded :=
    unary_transport boundedUnary (hsame_symm sameBounded)
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed transportedCheckerUnary transportedBoundedUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row checker ∨ hsame row boundedNormal ∨ hsame row transport ∨
              hsame row replay ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨hsame_refl replayRead, replayReadUnary⟩
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
      exact ⟨source.right, localPkg, provenancePkg⟩
  }
  exact
    ⟨cert, transportedCheckerUnary, transportedBoundedUnary, replayReadUnary, replayRoute⟩

end BEDC.Derived.MetaCICDecidableBoundaryUp
