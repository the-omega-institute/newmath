import BEDC.Derived.RealInverseUp

namespace BEDC.Derived.RealInverseUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealInverseApartnessDomain [AskSetup] [PackageSetup]
    {x a p w r s h c l n reciprocalWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealInverseCarrier x a p w r s h c l n bundle pkg →
      Cont a w reciprocalWindow →
        PkgSig bundle reciprocalWindow pkg →
          SemanticNameCert
              (fun row : BHist => hsame row reciprocalWindow ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row x ∨ hsame row a ∨ hsame row w ∨ hsame row r ∨
                  hsame row reciprocalWindow)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont a w reciprocalWindow ∧
                  PkgSig bundle reciprocalWindow pkg)
              hsame ∧ UnaryHistory reciprocalWindow := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier reciprocalCont reciprocalPkg
  have aUnary : UnaryHistory a := carrier.right.left
  have wUnary : UnaryHistory w := carrier.right.right.right.left
  have reciprocalUnary : UnaryHistory reciprocalWindow :=
    unary_cont_closed aUnary wUnary reciprocalCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row reciprocalWindow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row x ∨ hsame row a ∨ hsame row w ∨ hsame row r ∨
              hsame row reciprocalWindow)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont a w reciprocalWindow ∧
              PkgSig bundle reciprocalWindow pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro reciprocalWindow
        ⟨hsame_refl reciprocalWindow, reciprocalUnary⟩
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
      exact ⟨source.right, reciprocalCont, reciprocalPkg⟩
  }
  exact ⟨cert, reciprocalUnary⟩

end BEDC.Derived.RealInverseUp
