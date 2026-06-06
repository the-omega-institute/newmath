import BEDC.Derived.SequentiallyCompleteMetricUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricLateBoundCoverage [AskSetup] [PackageSetup]
    {X S M L D H C P N sequenceRead modulusRead limitRead distanceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X -> UnaryHistory S -> UnaryHistory M -> UnaryHistory L ->
        UnaryHistory D ->
          Cont X S sequenceRead ->
            Cont sequenceRead M modulusRead ->
              Cont modulusRead L limitRead ->
                Cont limitRead D distanceRead ->
                  PkgSig bundle P pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row distanceRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row D ∨ hsame row sequenceRead ∨
                            hsame row modulusRead ∨ hsame row limitRead ∨
                              hsame row distanceRead ∨ Cont sequenceRead M modulusRead ∨
                                Cont limitRead D distanceRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont X S sequenceRead ∧
                            Cont sequenceRead M modulusRead ∧
                              Cont modulusRead L limitRead ∧
                                Cont limitRead D distanceRead ∧ PkgSig bundle P pkg)
                        hsame ∧
                      UnaryHistory distanceRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fieldRows xUnary sUnary mUnary lUnary dUnary sequenceRoute modulusRoute limitRoute
    distanceRoute provenancePkg
  cases fieldRows
  have sequenceUnary : UnaryHistory sequenceRead :=
    unary_cont_closed xUnary sUnary sequenceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sequenceUnary mUnary modulusRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusUnary lUnary limitRoute
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed limitUnary dUnary distanceRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro distanceRead (And.intro (hsame_refl distanceRead) distanceUnary)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, sequenceRoute, modulusRoute, limitRoute, distanceRoute,
          provenancePkg⟩
    }
  · exact distanceUnary

end BEDC.Derived.SequentiallyCompleteMetricUp
