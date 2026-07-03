import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObserverGeodesicSectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverGeodesicSectionCarrier_finite_readback [AskSetup] [PackageSetup]
    {S L B Q D R _F _H C P _N residualRead geodesicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S ->
      UnaryHistory L ->
        UnaryHistory B ->
          UnaryHistory Q ->
            UnaryHistory D ->
              UnaryHistory R ->
                UnaryHistory P ->
                  Cont S L B ->
                    Cont B Q residualRead ->
                      Cont D R geodesicRead ->
                        Cont residualRead geodesicRead C ->
                          PkgSig bundle P pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row C ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row S ∨ hsame row L ∨ hsame row B ∨
                                    hsame row Q ∨ hsame row D ∨ hsame row R ∨
                                      hsame row residualRead ∨ hsame row geodesicRead ∨
                                        hsame row C)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont S L B ∧ Cont B Q residualRead ∧
                                    Cont D R geodesicRead ∧
                                      Cont residualRead geodesicRead C ∧
                                        PkgSig bundle P pkg)
                                hsame ∧
                              UnaryHistory residualRead ∧ UnaryHistory geodesicRead ∧
                                UnaryHistory C := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro unaryS unaryL unaryB unaryQ unaryD unaryR _unaryP routeB routeResidual
    routeGeodesic routeC pkgP
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed unaryB unaryQ routeResidual
  have geodesicUnary : UnaryHistory geodesicRead :=
    unary_cont_closed unaryD unaryR routeGeodesic
  have cUnary : UnaryHistory C :=
    unary_cont_closed residualUnary geodesicUnary routeC
  have sourceAtC : hsame C C ∧ UnaryHistory C :=
    ⟨hsame_refl C, cUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row C ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row L ∨ hsame row B ∨ hsame row Q ∨ hsame row D ∨
              hsame row R ∨ hsame row residualRead ∨ hsame row geodesicRead ∨ hsame row C)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S L B ∧ Cont B Q residualRead ∧
              Cont D R geodesicRead ∧ Cont residualRead geodesicRead C ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro C sourceAtC
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
      intro row source
      right; right; right; right; right; right; right; right
      exact source.left
    ledger_sound := by
      intro row source
      exact ⟨source.right, routeB, routeResidual, routeGeodesic, routeC, pkgP⟩
  }
  exact ⟨cert, residualUnary, geodesicUnary, cUnary⟩

end BEDC.Derived.ObserverGeodesicSectionUp
