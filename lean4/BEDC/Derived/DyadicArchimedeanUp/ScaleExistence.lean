import BEDC.Derived.DyadicArchimedeanUp.NameCertObligations

namespace BEDC.Derived.DyadicArchimedeanUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicArchimedeanScaleExistence [AskSetup] [PackageSetup]
    {D B K S C I _H _T P N scaleRead dominationRead enclosureRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory B ->
        UnaryHistory K ->
          UnaryHistory S ->
            UnaryHistory C ->
              UnaryHistory I ->
                UnaryHistory N ->
                  Cont D B scaleRead ->
                    Cont scaleRead K dominationRead ->
                      Cont dominationRead I enclosureRead ->
                        Cont enclosureRead N namedRead ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle N pkg ->
                              PkgSig bundle namedRead pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row dominationRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row D ∨ hsame row B ∨ hsame row K ∨
                                        hsame row S ∨ hsame row C ∨
                                          hsame row dominationRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont D B scaleRead ∧
                                        Cont scaleRead K dominationRead ∧
                                          PkgSig bundle P pkg)
                                    hsame ∧
                                  UnaryHistory scaleRead ∧
                                    UnaryHistory dominationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro dUnary bUnary kUnary _sUnary _cUnary _iUnary _nUnary scaleRoute dominationRoute
    _enclosureRoute _namedRoute provenancePkg _namePkg _namedPkg
  have scaleUnary : UnaryHistory scaleRead :=
    unary_cont_closed dUnary bUnary scaleRoute
  have dominationUnary : UnaryHistory dominationRead :=
    unary_cont_closed scaleUnary kUnary dominationRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row dominationRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row D ∨ hsame row B ∨ hsame row K ∨ hsame row S ∨ hsame row C ∨
            hsame row dominationRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont D B scaleRead ∧ Cont scaleRead K dominationRead ∧
            PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro dominationRead ⟨hsame_refl dominationRead, dominationUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, scaleRoute, dominationRoute, provenancePkg⟩
  }
  exact ⟨cert, scaleUnary, dominationUnary⟩

end BEDC.Derived.DyadicArchimedeanUp
