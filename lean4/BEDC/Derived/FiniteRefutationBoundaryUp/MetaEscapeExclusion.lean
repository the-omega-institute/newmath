import BEDC.Derived.FiniteRefutationBoundaryUp

namespace BEDC.Derived.FiniteRefutationBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteRefutationBoundary_meta_escape_exclusion_boundary [AskSetup] [PackageSetup]
    {A R D E H C P N botR : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory E ->
      UnaryHistory N ->
        PkgSig bundle P pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row E ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row A ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row H ∨
                  hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row botR)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
              hsame ∧
            hsame E E := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro eUnary _nUnary pkgRow
  have sourceAtE :
      (fun row : BHist => hsame row E ∧ UnaryHistory row) E := by
    exact ⟨hsame_refl E, eUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row E ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row botR)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro E sourceAtE
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgRow⟩
  }
  exact ⟨cert, hsame_refl E⟩

end BEDC.Derived.FiniteRefutationBoundaryUp
