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

theorem SequentiallyCompleteMetricRootLimitWitness [AskSetup] [PackageSetup]
    {X S M L D H C P N metricRead modulusRead limitRead distanceRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X -> UnaryHistory S -> UnaryHistory M -> UnaryHistory L ->
        UnaryHistory D -> UnaryHistory C -> Cont X S metricRead ->
          Cont metricRead M modulusRead -> Cont modulusRead L limitRead ->
            Cont limitRead D distanceRead -> Cont distanceRead C replayRead ->
              PkgSig bundle P pkg -> PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row limitRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row S ∨ hsame row M ∨ hsame row L ∨
                        hsame row D ∨ hsame row limitRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont metricRead M modulusRead ∧
                        Cont modulusRead L limitRead ∧ Cont limitRead D distanceRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory limitRead ∧ UnaryHistory distanceRead ∧
                    UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fields xUnary sUnary mUnary lUnary dUnary cUnary metricRoute modulusRoute limitRoute
    distanceRoute replayRoute provenancePkg namePkg
  have _acceptedFields :
      sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] := fields
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed xUnary sUnary metricRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed metricReadUnary mUnary modulusRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusReadUnary lUnary limitRoute
  have distanceReadUnary : UnaryHistory distanceRead :=
    unary_cont_closed limitReadUnary dUnary distanceRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed distanceReadUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row limitRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row M ∨ hsame row L ∨ hsame row D ∨
              hsame row limitRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont metricRead M modulusRead ∧
              Cont modulusRead L limitRead ∧ Cont limitRead D distanceRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro limitRead
        ⟨hsame_refl limitRead, limitReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, modulusRoute, limitRoute, distanceRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, limitReadUnary, distanceReadUnary, replayReadUnary⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
