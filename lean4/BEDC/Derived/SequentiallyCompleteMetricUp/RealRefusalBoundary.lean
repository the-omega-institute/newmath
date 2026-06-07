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

theorem SequentiallyCompleteMetricRealRefusalBoundary [AskSetup] [PackageSetup]
    {X S M L D H C P N sequenceRead modulusRead limitRead distanceRead replayRead
      namedRead realBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory S ->
          UnaryHistory M ->
            UnaryHistory L ->
              UnaryHistory D ->
                UnaryHistory C ->
                  UnaryHistory N ->
                    UnaryHistory P ->
                      Cont X S sequenceRead ->
                        Cont sequenceRead M modulusRead ->
                          Cont modulusRead L limitRead ->
                            Cont limitRead D distanceRead ->
                              Cont distanceRead C replayRead ->
                                Cont replayRead N namedRead ->
                                  Cont namedRead P realBoundary ->
                                    PkgSig bundle P pkg ->
                                      PkgSig bundle N pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row realBoundary ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row X ∨ hsame row S ∨ hsame row M ∨
                                                hsame row L ∨ hsame row D ∨ hsame row N ∨
                                                  hsame row realBoundary)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont X S sequenceRead ∧
                                                Cont sequenceRead M modulusRead ∧
                                                  Cont modulusRead L limitRead ∧
                                                    Cont limitRead D distanceRead ∧
                                                      Cont distanceRead C replayRead ∧
                                                        Cont replayRead N namedRead ∧
                                                          Cont namedRead P realBoundary ∧
                                                            PkgSig bundle P pkg ∧
                                                              PkgSig bundle N pkg)
                                            hsame ∧ UnaryHistory realBoundary := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro fields xUnary sUnary mUnary lUnary dUnary cUnary nUnary pUnary sequenceRoute
    modulusRoute limitRoute distanceRoute replayRoute namedRoute boundaryRoute provenancePkg
    namePkg
  have _acceptedFields :
      sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] := fields
  have sequenceUnary : UnaryHistory sequenceRead :=
    unary_cont_closed xUnary sUnary sequenceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sequenceUnary mUnary modulusRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusUnary lUnary limitRoute
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed limitUnary dUnary distanceRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed distanceUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  have boundaryUnary : UnaryHistory realBoundary :=
    unary_cont_closed namedUnary pUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realBoundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row M ∨ hsame row L ∨ hsame row D ∨
              hsame row N ∨ hsame row realBoundary)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X S sequenceRead ∧ Cont sequenceRead M modulusRead ∧
              Cont modulusRead L limitRead ∧ Cont limitRead D distanceRead ∧
                Cont distanceRead C replayRead ∧ Cont replayRead N namedRead ∧
                  Cont namedRead P realBoundary ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realBoundary ⟨hsame_refl realBoundary, boundaryUnary⟩
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
        ⟨source.right, sequenceRoute, modulusRoute, limitRoute, distanceRoute, replayRoute,
          namedRoute, boundaryRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, boundaryUnary⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
