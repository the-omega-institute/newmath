import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringDimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootRealSeparabilityWindow [AskSetup] [PackageSetup]
    {K E C R O L H T P N denseRead scaleRead dyadicRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory K ->
      UnaryHistory E ->
        UnaryHistory C ->
          UnaryHistory R ->
            UnaryHistory O ->
              UnaryHistory L ->
                UnaryHistory H ->
                  UnaryHistory T ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont K E C ->
                          Cont C R O ->
                            Cont O L denseRead ->
                              Cont denseRead T scaleRead ->
                                Cont scaleRead H dyadicRead ->
                                  Cont dyadicRead N realSeal ->
                                    PkgSig bundle P pkg ->
                                      PkgSig bundle N pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row realSeal ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row K ∨ hsame row E ∨ hsame row C ∨
                                                hsame row R ∨ hsame row O ∨ hsame row L ∨
                                                  hsame row denseRead ∨
                                                    hsame row scaleRead ∨
                                                      hsame row dyadicRead ∨
                                                        hsame row realSeal)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont O L denseRead ∧
                                                Cont denseRead T scaleRead ∧
                                                  Cont scaleRead H dyadicRead ∧
                                                    Cont dyadicRead N realSeal ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle N pkg)
                                            hsame ∧
                                          UnaryHistory denseRead ∧
                                            UnaryHistory scaleRead ∧
                                              UnaryHistory dyadicRead ∧
                                                UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro compactSource epsilonSource coverSource refinementSource orderSource lebesgueSource
    transportSource replaySource _provenanceSource nameSource compactRoute orderRoute denseRoute
    scaleRoute dyadicRoute sealRoute provenancePkg namePkg
  have _coverRouteUnary : UnaryHistory C :=
    unary_cont_closed compactSource epsilonSource compactRoute
  have _orderRouteUnary : UnaryHistory O :=
    unary_cont_closed coverSource refinementSource orderRoute
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed orderSource lebesgueSource denseRoute
  have scaleUnary : UnaryHistory scaleRead :=
    unary_cont_closed denseUnary replaySource scaleRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed scaleUnary transportSource dyadicRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicUnary nameSource sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row R ∨ hsame row O ∨
              hsame row L ∨ hsame row denseRead ∨ hsame row scaleRead ∨
                hsame row dyadicRead ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont O L denseRead ∧ Cont denseRead T scaleRead ∧
              Cont scaleRead H dyadicRead ∧ Cont dyadicRead N realSeal ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, denseRoute, scaleRoute, dyadicRoute, sealRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, denseUnary, scaleUnary, dyadicUnary, realSealUnary⟩

end BEDC.Derived.CoveringDimensionUp
