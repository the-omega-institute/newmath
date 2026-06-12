import BEDC.Derived.RegularCauchyReciprocalUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyReciprocalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyReciprocalReadbackBudgetExactness [AskSetup] [PackageSetup]
    {Q A M W D B T E H C P N apartnessWindow modulusWindow finiteWindow dyadicRead budgetRead
      readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q ->
      UnaryHistory A ->
        UnaryHistory M ->
          UnaryHistory W ->
            UnaryHistory D ->
              UnaryHistory B ->
                UnaryHistory T ->
                  Cont Q A apartnessWindow ->
                    Cont apartnessWindow M modulusWindow ->
                      Cont modulusWindow W finiteWindow ->
                        Cont finiteWindow D dyadicRead ->
                          Cont dyadicRead B budgetRead ->
                            Cont budgetRead T readbackRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row readbackRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row Q ∨ hsame row A ∨ hsame row M ∨
                                          hsame row W ∨ hsame row D ∨ hsame row B ∨
                                            hsame row T ∨ hsame row readbackRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont Q A apartnessWindow ∧
                                          Cont apartnessWindow M modulusWindow ∧
                                            Cont modulusWindow W finiteWindow ∧
                                              Cont finiteWindow D dyadicRead ∧
                                                Cont dyadicRead B budgetRead ∧
                                                  Cont budgetRead T readbackRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory apartnessWindow ∧
                                      UnaryHistory modulusWindow ∧
                                        UnaryHistory finiteWindow ∧
                                          UnaryHistory dyadicRead ∧
                                            UnaryHistory budgetRead ∧
                                              UnaryHistory readbackRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro qUnary aUnary mUnary wUnary dUnary bUnary tUnary apartnessRoute modulusRoute
    finiteRoute dyadicRoute budgetRoute readbackRoute provenancePkg namePkg
  have apartnessUnary : UnaryHistory apartnessWindow :=
    unary_cont_closed qUnary aUnary apartnessRoute
  have modulusUnary : UnaryHistory modulusWindow :=
    unary_cont_closed apartnessUnary mUnary modulusRoute
  have finiteUnary : UnaryHistory finiteWindow :=
    unary_cont_closed modulusUnary wUnary finiteRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed finiteUnary dUnary dyadicRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed dyadicUnary bUnary budgetRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed budgetUnary tUnary readbackRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro readbackRead ⟨hsame_refl readbackRead, readbackUnary⟩
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, apartnessRoute, modulusRoute, finiteRoute, dyadicRoute,
            budgetRoute, readbackRoute, provenancePkg, namePkg⟩
    }
  · exact
      ⟨apartnessUnary, modulusUnary, finiteUnary, dyadicUnary, budgetUnary,
        readbackUnary⟩

end BEDC.Derived.RegularCauchyReciprocalUp
