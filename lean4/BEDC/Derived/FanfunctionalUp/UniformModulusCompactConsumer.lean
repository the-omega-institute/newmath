import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalUniformModulusCompactConsumer [AskSetup] [PackageSetup]
    {C F eps B D W M H K P N prefixRead depthRead toleranceRead witnessRead compactRead
      modulusRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C ->
      UnaryHistory F ->
        UnaryHistory eps ->
          UnaryHistory B ->
            UnaryHistory D ->
              UnaryHistory W ->
                UnaryHistory M ->
                  UnaryHistory H ->
                    UnaryHistory K ->
                      Cont C F prefixRead ->
                        Cont prefixRead B depthRead ->
                          Cont depthRead eps toleranceRead ->
                            Cont toleranceRead W witnessRead ->
                              Cont witnessRead M compactRead ->
                                Cont compactRead H modulusRead ->
                                  Cont modulusRead K replayRead ->
                                    PkgSig bundle P pkg ->
                                      PkgSig bundle N pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row replayRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row C ∨ hsame row F ∨ hsame row eps ∨
                                                hsame row B ∨ hsame row D ∨
                                                  hsame row W ∨ hsame row M ∨
                                                    hsame row H ∨ hsame row K ∨
                                                      hsame row P ∨ hsame row N ∨
                                                        hsame row replayRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont C F prefixRead ∧
                                                Cont prefixRead B depthRead ∧
                                                  Cont depthRead eps toleranceRead ∧
                                                    Cont toleranceRead W witnessRead ∧
                                                      Cont witnessRead M compactRead ∧
                                                        Cont compactRead H modulusRead ∧
                                                          Cont modulusRead K replayRead ∧
                                                            PkgSig bundle P pkg ∧
                                                              PkgSig bundle N pkg)
                                            hsame ∧
                                          UnaryHistory prefixRead ∧ UnaryHistory depthRead ∧
                                            UnaryHistory toleranceRead ∧
                                              UnaryHistory witnessRead ∧
                                                UnaryHistory compactRead ∧
                                                  UnaryHistory modulusRead ∧
                                                    UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro cUnary fUnary epsUnary bUnary _dUnary wUnary mUnary hUnary kUnary prefixRoute
    depthRoute toleranceRoute witnessRoute compactRoute modulusRoute replayRoute provenancePkg
    localPkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cUnary fUnary prefixRoute
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed prefixUnary bUnary depthRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed depthUnary epsUnary toleranceRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed toleranceUnary wUnary witnessRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed witnessUnary mUnary compactRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed compactUnary hUnary modulusRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed modulusUnary kUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row F ∨ hsame row eps ∨ hsame row B ∨ hsame row D ∨
              hsame row W ∨ hsame row M ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨
                hsame row N ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C F prefixRead ∧ Cont prefixRead B depthRead ∧
              Cont depthRead eps toleranceRead ∧ Cont toleranceRead W witnessRead ∧
                Cont witnessRead M compactRead ∧ Cont compactRead H modulusRead ∧
                  Cont modulusRead K replayRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
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
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, prefixRoute, depthRoute, toleranceRoute, witnessRoute, compactRoute,
          modulusRoute, replayRoute, provenancePkg, localPkg⟩
  }
  exact
    ⟨cert, prefixUnary, depthUnary, toleranceUnary, witnessUnary, compactUnary, modulusUnary,
      replayUnary⟩

end BEDC.Derived.FanfunctionalUp
