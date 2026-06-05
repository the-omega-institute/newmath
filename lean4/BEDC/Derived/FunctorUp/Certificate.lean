import BEDC.Derived.FunctorUp.PrefixCarrier
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.FunctorUp

open BEDC.Derived.CategoryUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FunctorPrefixConcreteCertificate {p a b c f g fg : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g ->
      Cont f g fg ->
        CategoryHomCarrier (append p a) (append p c) fg ∧
          CategoryHomCarrier a b f ∧ CategoryHomCarrier b c g := by
  -- BEDC touchpoint anchor: BHist UnaryHistory CategoryHomCarrier Cont append
  intro prefixCarrier left right comp
  exact
    ⟨FunctorPrefixHomCarrier_comp_preserves prefixCarrier left right comp, left, right⟩

theorem FunctorPrefixSemanticNameCert [AskSetup] [PackageSetup]
    {p a b c f g fg : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g ->
      Cont f g fg -> PkgSig bundle fg pkg ->
        SemanticNameCert
            (fun row : BHist => hsame row fg ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row (append p a) ∨ hsame row (append p c) ∨ hsame row f ∨
                hsame row g ∨ hsame row fg)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle fg pkg)
            hsame ∧
          CategoryHomCarrier (append p a) (append p c) fg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert Cont append
  intro prefixCarrier left right comp pkgSig
  have concrete :
      CategoryHomCarrier (append p a) (append p c) fg ∧
        CategoryHomCarrier a b f ∧ CategoryHomCarrier b c g :=
    FunctorPrefixConcreteCertificate prefixCarrier left right comp
  have baseComposite : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed left right comp
  have fgUnary : UnaryHistory fg := baseComposite.right.right.left
  have sourceFg :
      (fun row : BHist => hsame row fg ∧ UnaryHistory row) fg :=
    ⟨hsame_refl fg, fgUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row fg ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row (append p a) ∨ hsame row (append p c) ∨ hsame row f ∨
              hsame row g ∨ hsame row fg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle fg pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro fg sourceFg
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro row source
      exact ⟨source.right, pkgSig⟩
  }
  exact ⟨cert, concrete.left⟩

end BEDC.Derived.FunctorUp
