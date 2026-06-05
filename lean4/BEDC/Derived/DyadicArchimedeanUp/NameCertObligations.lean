import BEDC.Derived.DyadicArchimedeanUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicArchimedeanUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicArchimedeanNameCertObligations [AskSetup] [PackageSetup]
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
                                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row D ∨ hsame row B ∨ hsame row K ∨
                                        hsame row S ∨ hsame row C ∨ hsame row I ∨
                                          hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                        PkgSig bundle N pkg ∧ PkgSig bundle namedRead pkg)
                                    hsame ∧
                                  UnaryHistory scaleRead ∧ UnaryHistory dominationRead ∧
                                    UnaryHistory enclosureRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro dUnary bUnary kUnary _sUnary _cUnary iUnary nUnary scaleRoute dominationRoute
    enclosureRoute namedRoute provenancePkg namePkg namedPkg
  have scaleUnary : UnaryHistory scaleRead :=
    unary_cont_closed dUnary bUnary scaleRoute
  have dominationUnary : UnaryHistory dominationRead :=
    unary_cont_closed scaleUnary kUnary dominationRoute
  have enclosureUnary : UnaryHistory enclosureRead :=
    unary_cont_closed dominationUnary iUnary enclosureRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed enclosureUnary nUnary namedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row D ∨ hsame row B ∨ hsame row K ∨ hsame row S ∨ hsame row C ∨
            hsame row I ∨ hsame row namedRead)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
            PkgSig bundle namedRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, provenancePkg, namePkg, namedPkg⟩
  }
  exact ⟨cert, scaleUnary, dominationUnary, enclosureUnary, namedUnary⟩

end BEDC.Derived.DyadicArchimedeanUp
