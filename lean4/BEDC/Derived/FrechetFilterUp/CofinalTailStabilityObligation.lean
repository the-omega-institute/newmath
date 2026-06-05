import BEDC.Derived.FrechetFilterUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FrechetFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FrechetFilterCofinalTailStabilityObligation [AskSetup] [PackageSetup]
    {U T S M B Q R A H C P N firstTail secondTail commonTail scheduleRead
      metricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    frechetFilterFields (FrechetFilterUp.mk U T S M B Q R A H C P N) =
        [U, T, S, M, B, Q, R, A, H, C, P, N] ->
      UnaryHistory U ->
        UnaryHistory T ->
          UnaryHistory S ->
            UnaryHistory M ->
              UnaryHistory B ->
                UnaryHistory C ->
                  Cont U T firstTail ->
                    Cont U T secondTail ->
                      Cont firstTail B commonTail ->
                        Cont commonTail S scheduleRead ->
                          Cont scheduleRead M metricRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row commonTail ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row U ∨ hsame row T ∨ hsame row B ∨
                                        hsame row commonTail ∨ Cont firstTail B commonTail)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont U T firstTail ∧
                                        Cont U T secondTail ∧ Cont firstTail B commonTail ∧
                                          Cont commonTail S scheduleRead ∧
                                            Cont scheduleRead M metricRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory firstTail ∧ UnaryHistory secondTail ∧
                                    UnaryHistory commonTail ∧ UnaryHistory scheduleRead ∧
                                      UnaryHistory metricRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fieldRows uUnary tUnary sUnary mUnary bUnary _cUnary firstRoute secondRoute
    commonRoute scheduleRoute metricRoute provenancePkg namePkg
  cases fieldRows
  have firstUnary : UnaryHistory firstTail :=
    unary_cont_closed uUnary tUnary firstRoute
  have secondUnary : UnaryHistory secondTail :=
    unary_cont_closed uUnary tUnary secondRoute
  have commonUnary : UnaryHistory commonTail :=
    unary_cont_closed firstUnary bUnary commonRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed commonUnary sUnary scheduleRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed scheduleUnary mUnary metricRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro commonTail ⟨hsame_refl commonTail, commonUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, firstRoute, secondRoute, commonRoute, scheduleRoute, metricRoute,
            provenancePkg, namePkg⟩
    }
  · exact ⟨firstUnary, secondUnary, commonUnary, scheduleUnary, metricUnary⟩

end BEDC.Derived.FrechetFilterUp
