import BEDC.Derived.SeparatedPseudometricCompletionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparatedPseudometricCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparatedPseudometricCompletionCarrier_scope [AskSetup] [PackageSetup]
    {P Z Q M S R D E H C K N routeSep routeCompletion routeWindow routeReg routeDyadic
      routeReal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory P ->
      UnaryHistory Z ->
        UnaryHistory Q ->
          UnaryHistory M ->
            UnaryHistory S ->
              UnaryHistory R ->
                UnaryHistory D ->
                  UnaryHistory E ->
                    Cont P Z routeSep ->
                      Cont routeSep Q routeCompletion ->
                        Cont routeCompletion M routeWindow ->
                          Cont routeWindow S routeReg ->
                            Cont routeReg R routeDyadic ->
                              Cont routeDyadic D routeReal ->
                                Cont routeReal E C ->
                                  PkgSig bundle K pkg ->
                                    PkgSig bundle N pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row routeReal ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row P ∨ hsame row Z ∨ hsame row Q ∨
                                              hsame row M ∨ hsame row S ∨ hsame row R ∨
                                                hsame row D ∨ hsame row E ∨
                                                  hsame row routeReal)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont P Z routeSep ∧
                                              Cont routeSep Q routeCompletion ∧
                                                Cont routeCompletion M routeWindow ∧
                                                  Cont routeWindow S routeReg ∧
                                                    Cont routeReg R routeDyadic ∧
                                                      Cont routeDyadic D routeReal ∧
                                                        Cont routeReal E C ∧
                                                          PkgSig bundle K pkg ∧
                                                            PkgSig bundle N pkg)
                                          hsame ∧ UnaryHistory routeSep ∧
                                        UnaryHistory routeCompletion ∧
                                          UnaryHistory routeWindow ∧ UnaryHistory routeReg ∧
                                            UnaryHistory routeDyadic ∧
                                              UnaryHistory routeReal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro unaryP unaryZ unaryQ unaryM unaryS unaryR unaryD unaryE sepRoute completionRoute
    windowRoute regRoute dyadicRoute realRoute consumerRoute pkgK pkgN
  have unarySep : UnaryHistory routeSep :=
    unary_cont_closed unaryP unaryZ sepRoute
  have unaryCompletion : UnaryHistory routeCompletion :=
    unary_cont_closed unarySep unaryQ completionRoute
  have unaryWindow : UnaryHistory routeWindow :=
    unary_cont_closed unaryCompletion unaryM windowRoute
  have unaryReg : UnaryHistory routeReg :=
    unary_cont_closed unaryWindow unaryS regRoute
  have unaryDyadic : UnaryHistory routeDyadic :=
    unary_cont_closed unaryReg unaryR dyadicRoute
  have unaryReal : UnaryHistory routeReal :=
    unary_cont_closed unaryDyadic unaryD realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeReal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row Z ∨ hsame row Q ∨ hsame row M ∨ hsame row S ∨
              hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row routeReal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P Z routeSep ∧ Cont routeSep Q routeCompletion ∧
              Cont routeCompletion M routeWindow ∧ Cont routeWindow S routeReg ∧
                Cont routeReg R routeDyadic ∧ Cont routeDyadic D routeReal ∧
                  Cont routeReal E C ∧ PkgSig bundle K pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro routeReal ⟨hsame_refl routeReal, unaryReal⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sepRoute, completionRoute, windowRoute, regRoute, dyadicRoute,
          realRoute, consumerRoute, pkgK, pkgN⟩
  }
  exact ⟨cert, unarySep, unaryCompletion, unaryWindow, unaryReg, unaryDyadic, unaryReal⟩

end BEDC.Derived.SeparatedPseudometricCompletionUp
