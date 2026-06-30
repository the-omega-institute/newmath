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

theorem SeparatedPseudometricCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {P Z Q M S R D E H C K N sepRead completionRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont P Z sepRead ->
      Cont sepRead Q completionRead ->
        Cont S R realRead ->
          PkgSig bundle K pkg ->
            PkgSig bundle N pkg ->
              UnaryHistory P ->
                UnaryHistory Z ->
                  UnaryHistory Q ->
                    UnaryHistory S ->
                      UnaryHistory R ->
                        SemanticNameCert
                            (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row completionRead ∧ Cont P Z sepRead)
                            (fun row : BHist =>
                              hsame row completionRead ∧
                                Cont sepRead Q completionRead ∧ PkgSig bundle K pkg)
                            hsame ∧
                          UnaryHistory sepRead ∧ UnaryHistory completionRead ∧
                            UnaryHistory realRead ∧ Cont P Z sepRead ∧
                              Cont sepRead Q completionRead ∧ Cont S R realRead ∧
                                PkgSig bundle K pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro sepRoute completionRoute realRoute pkgK pkgN unaryP unaryZ unaryQ unaryS unaryR
  have unarySep : UnaryHistory sepRead :=
    unary_cont_closed unaryP unaryZ sepRoute
  have unaryCompletion : UnaryHistory completionRead :=
    unary_cont_closed unarySep unaryQ completionRoute
  have unaryReal : UnaryHistory realRead :=
    unary_cont_closed unaryS unaryR realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row completionRead ∧ Cont P Z sepRead)
          (fun row : BHist =>
            hsame row completionRead ∧ Cont sepRead Q completionRead ∧
              PkgSig bundle K pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, unaryCompletion⟩
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
      exact ⟨source.left, sepRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, completionRoute, pkgK⟩
  }
  exact
    ⟨cert, unarySep, unaryCompletion, unaryReal, sepRoute, completionRoute, realRoute, pkgK,
      pkgN⟩

end BEDC.Derived.SeparatedPseudometricCompletionUp
