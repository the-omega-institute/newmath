import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.BorrowedRecursorBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem BorrowedRecursorBoundary_nonescape [AskSetup] [PackageSetup]
    {R A S F H C P N ancestryRead socketRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont R A ancestryRead →
      Cont ancestryRead S socketRead →
        Cont socketRead F refusalRead →
          PkgSig bundle P pkg →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row refusalRead ∧ Cont R A ancestryRead ∧
                      Cont ancestryRead S socketRead ∧ Cont socketRead F refusalRead)
                  (fun row : BHist =>
                    hsame row R ∨ hsame row A ∨ hsame row S ∨ hsame row F ∨
                      hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row refusalRead)
                  (fun row : BHist =>
                    hsame row refusalRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                  hsame ∧
                Cont R A ancestryRead ∧ Cont ancestryRead S socketRead ∧
                  Cont socketRead F refusalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro ancestryRoute socketRoute refusalRoute provenanceEvidence nameEvidence
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row refusalRead ∧ Cont R A ancestryRead ∧
              Cont ancestryRead S socketRead ∧ Cont socketRead F refusalRead)
          (fun row : BHist =>
            hsame row R ∨ hsame row A ∨ hsame row S ∨ hsame row F ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row refusalRead)
          (fun row : BHist =>
            hsame row refusalRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refusalRead
          ⟨hsame_refl refusalRead, ancestryRoute, socketRoute, refusalRoute⟩
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
          ⟨hsame_trans (hsame_symm sameRows) source.left, source.right.left,
            source.right.right.left, source.right.right.right⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenanceEvidence, nameEvidence⟩
  }
  exact ⟨cert, ancestryRoute, socketRoute, refusalRoute⟩

end BEDC.Derived.BorrowedRecursorBoundaryUp
