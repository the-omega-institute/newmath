import BEDC.Derived.CauchyNullEquivalenceUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CauchyNullEquivalenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyNullEquivalenceCarrier_difference_zero_route [AskSetup] [PackageSetup]
    {X Y D Z E H _C P N _diffRead equalityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X -> UnaryHistory Y -> UnaryHistory D -> UnaryHistory Z ->
      Cont X Y D -> Cont D Z equalityRead -> hsame E equalityRead ->
        hsame H (append D Z) -> PkgSig bundle P pkg -> PkgSig bundle N pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row equalityRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row X ∨ hsame row Y ∨ hsame row D ∨ hsame row Z ∨
                hsame row E ∨ hsame row equalityRead)
            (fun row : BHist =>
              hsame row equalityRead ∧ Cont X Y D ∧ Cont D Z equalityRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
            hsame ∧
            UnaryHistory equalityRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryX unaryY _unaryD unaryZ sourceDifference differenceZero sameEquality _sameRoute
    provenancePkg namePkg
  have unaryDifference : UnaryHistory D :=
    unary_cont_closed unaryX unaryY sourceDifference
  have unaryEquality : UnaryHistory equalityRead :=
    unary_cont_closed unaryDifference unaryZ differenceZero
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row equalityRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row Y ∨ hsame row D ∨ hsame row Z ∨ hsame row E ∨
            hsame row equalityRead)
        (fun row : BHist =>
          hsame row equalityRead ∧ Cont X Y D ∧ Cont D Z equalityRead ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro equalityRead ⟨hsame_refl equalityRead, unaryEquality⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sourceDifference, differenceZero, provenancePkg, namePkg⟩
  }
  have equalityPattern : hsame E equalityRead ∨ hsame equalityRead equalityRead :=
    Or.inl sameEquality
  cases equalityPattern with
  | inl _sameE =>
      exact ⟨cert, unaryEquality⟩
  | inr _sameSelf =>
      exact ⟨cert, unaryEquality⟩

end BEDC.Derived.CauchyNullEquivalenceUp
