import BEDC.Derived.FareySequenceUp.NameCertObligations

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceDenominatorRefinementInduction [AskSetup] [PackageSetup]
    {B A M L T S H C P N refinementRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B →
      UnaryHistory A →
        UnaryHistory L →
          UnaryHistory T →
            UnaryHistory N →
              Cont B A M →
                Cont M L S →
                  Cont S T refinementRead →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row refinementRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
                              hsame row T ∨ hsame row S ∨ hsame row refinementRead ∨
                                hsame row N)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont B A M ∧ Cont M L S ∧
                              Cont S T refinementRead ∧ PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory M ∧ UnaryHistory S ∧ UnaryHistory refinementRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro boundaryUnary adjacencyUnary levelUnary toleranceUnary _nameUnary boundaryRoute
    levelRoute toleranceRoute packageN
  have mediantUnary : UnaryHistory M :=
    unary_cont_closed boundaryUnary adjacencyUnary boundaryRoute
  have sternBrocotUnary : UnaryHistory S :=
    unary_cont_closed mediantUnary levelUnary levelRoute
  have refinementUnary : UnaryHistory refinementRead :=
    unary_cont_closed sternBrocotUnary toleranceUnary toleranceRoute
  have sourceRefinement :
      (fun row : BHist => hsame row refinementRead ∧ UnaryHistory row) refinementRead := by
    exact ⟨hsame_refl refinementRead, refinementUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinementRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨ hsame row T ∨
              hsame row S ∨ hsame row refinementRead ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B A M ∧ Cont M L S ∧ Cont S T refinementRead ∧
              PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refinementRead sourceRefinement
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
                  (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundaryRoute, levelRoute, toleranceRoute, packageN⟩
  }
  exact ⟨cert, mediantUnary, sternBrocotUnary, refinementUnary⟩

end BEDC.Derived.FareySequenceUp
