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

theorem SequentiallyCompleteMetricSourceFirstTailRead [AskSetup] [PackageSetup]
    {X S M L D H C P N tailRead modulusRead limitRead distanceRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory S ->
          UnaryHistory M ->
            UnaryHistory L ->
              UnaryHistory D ->
                UnaryHistory C ->
                  Cont X S tailRead ->
                    Cont tailRead M modulusRead ->
                      Cont modulusRead L limitRead ->
                        Cont limitRead D distanceRead ->
                          Cont distanceRead C replayRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row X ∨ hsame row S ∨ hsame row M ∨
                                        hsame row L ∨ hsame row D ∨ Cont X S tailRead ∨
                                          Cont tailRead M modulusRead ∨
                                            Cont modulusRead L limitRead ∨
                                              Cont limitRead D distanceRead ∨
                                                Cont distanceRead C replayRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont X S tailRead ∧
                                        Cont tailRead M modulusRead ∧
                                          Cont modulusRead L limitRead ∧
                                            Cont limitRead D distanceRead ∧
                                              Cont distanceRead C replayRead ∧
                                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory tailRead ∧ UnaryHistory modulusRead ∧
                                    UnaryHistory limitRead ∧ UnaryHistory distanceRead ∧
                                      UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fieldRows xUnary sUnary mUnary lUnary dUnary cUnary tailRoute modulusRoute
    limitRoute distanceRoute replayRoute provenancePkg namePkg
  cases fieldRows
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed xUnary sUnary tailRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed tailUnary mUnary modulusRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusUnary lUnary limitRoute
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed limitUnary dUnary distanceRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed distanceUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row M ∨ hsame row L ∨ hsame row D ∨
              Cont X S tailRead ∨ Cont tailRead M modulusRead ∨
                Cont modulusRead L limitRead ∨ Cont limitRead D distanceRead ∨
                  Cont distanceRead C replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X S tailRead ∧ Cont tailRead M modulusRead ∧
              Cont modulusRead L limitRead ∧ Cont limitRead D distanceRead ∧
                Cont distanceRead C replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      intro _row _source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr replayRoute))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, tailRoute, modulusRoute, limitRoute, distanceRoute, replayRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, tailUnary, modulusUnary, limitUnary, distanceUnary, replayUnary⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
