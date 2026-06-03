import BEDC.Derived.NormalFormConsistencySealUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealJoinabilityObligation [AskSetup] [PackageSetup]
    {typing falseRow normality theoremRow boundary transport replay provenance localName
      joinRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory typing →
      UnaryHistory falseRow →
        UnaryHistory normality →
          UnaryHistory boundary →
            UnaryHistory provenance →
              Cont typing falseRow theoremRow →
                Cont theoremRow normality transport →
                  Cont transport boundary replay →
                    Cont replay provenance joinRead →
                      PkgSig bundle localName pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row joinRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row typing ∨ hsame row falseRow ∨
                                hsame row normality ∨ hsame row theoremRow ∨
                                  hsame row boundary ∨ hsame row joinRead ∨
                                    Cont replay provenance joinRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle localName pkg)
                            hsame ∧
                          UnaryHistory theoremRow ∧ UnaryHistory joinRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro typingUnary falseUnary normalityUnary boundaryUnary provenanceUnary theoremRoute
    transportRoute replayRoute joinRoute localNamePkg
  have theoremUnary : UnaryHistory theoremRow :=
    unary_cont_closed typingUnary falseUnary theoremRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed theoremUnary normalityUnary transportRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed transportUnary boundaryUnary replayRoute
  have joinUnary : UnaryHistory joinRead :=
    unary_cont_closed replayUnary provenanceUnary joinRoute
  have joinSource :
      (fun row : BHist => hsame row joinRead ∧ UnaryHistory row) joinRead := by
    exact ⟨hsame_refl joinRead, joinUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row joinRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typing ∨ hsame row falseRow ∨ hsame row normality ∨
              hsame row theoremRow ∨ hsame row boundary ∨ hsame row joinRead ∨
                Cont replay provenance joinRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro joinRead joinSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localNamePkg⟩
  }
  exact ⟨cert, theoremUnary, joinUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
