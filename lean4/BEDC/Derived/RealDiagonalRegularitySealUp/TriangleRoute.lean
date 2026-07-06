import BEDC.Derived.RealDiagonalRegularitySealUp.Obligations

namespace BEDC.Derived.RealDiagonalRegularitySealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealDiagonalRegularitySealCarrier_triangle_route [AskSetup] [PackageSetup]
    {D W T Q R E H _C P N publicRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    UnaryHistory D -> UnaryHistory W -> UnaryHistory Q -> UnaryHistory E ->
      hsame H (append D W) -> Cont D W T -> Cont T Q R -> Cont R E publicRead ->
        PkgSig bundle P pkg -> PkgSig bundle N pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row Q ∨
                hsame row R ∨ hsame row E ∨ hsame row publicRead)
            (fun row : BHist =>
              hsame row publicRead ∧ hsame H (append D W) ∧ Cont D W T ∧
                Cont T Q R ∧ Cont R E publicRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
            hsame ∧
            UnaryHistory T ∧ UnaryHistory R ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryD unaryW unaryQ unaryE sameH diagonalWindow triangleDyadic regularityReal
    provenancePkg namePkg
  have unaryTriangle : UnaryHistory T :=
    unary_cont_closed unaryD unaryW diagonalWindow
  have unaryRegularity : UnaryHistory R :=
    unary_cont_closed unaryTriangle unaryQ triangleDyadic
  have unaryPublic : UnaryHistory publicRead :=
    unary_cont_closed unaryRegularity unaryE regularityReal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row Q ∨ hsame row R ∨
            hsame row E ∨ hsame row publicRead)
        (fun row : BHist =>
          hsame row publicRead ∧ hsame H (append D W) ∧ Cont D W T ∧
            Cont T Q R ∧ Cont R E publicRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, unaryPublic⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, sameH, diagonalWindow, triangleDyadic, regularityReal,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, unaryTriangle, unaryRegularity, unaryPublic⟩

end BEDC.Derived.RealDiagonalRegularitySealUp
