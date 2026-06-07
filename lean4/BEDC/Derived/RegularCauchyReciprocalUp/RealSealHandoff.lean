import BEDC.Derived.RegularCauchyReciprocalUp.WindowComposition

namespace BEDC.Derived.RegularCauchyReciprocalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyReciprocalRealSealHandoff [AskSetup] [PackageSetup]
    {Q A M W D B T E H C P N apartnessWindow modulusWindow finiteWindow dyadicRead
      budgetRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q ->
      UnaryHistory A ->
        UnaryHistory M ->
          UnaryHistory W ->
            UnaryHistory D ->
              UnaryHistory B ->
                UnaryHistory T ->
                  UnaryHistory E ->
                    Cont Q A apartnessWindow ->
                      Cont apartnessWindow M modulusWindow ->
                        Cont modulusWindow W finiteWindow ->
                          Cont finiteWindow D dyadicRead ->
                            Cont dyadicRead B budgetRead ->
                              Cont budgetRead T readbackRead ->
                                Cont readbackRead E sealRead ->
                                  hsame H (append C P) ->
                                    PkgSig bundle P pkg ->
                                      PkgSig bundle N pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row sealRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row Q ∨ hsame row A ∨
                                                hsame row M ∨ hsame row W ∨
                                                  hsame row D ∨ hsame row B ∨
                                                    hsame row T ∨ hsame row E ∨
                                                      hsame row sealRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                Cont Q A apartnessWindow ∧
                                                  Cont apartnessWindow M modulusWindow ∧
                                                    Cont modulusWindow W finiteWindow ∧
                                                      Cont finiteWindow D dyadicRead ∧
                                                        Cont dyadicRead B budgetRead ∧
                                                          Cont budgetRead T readbackRead ∧
                                                            Cont readbackRead E sealRead ∧
                                                              hsame H (append C P) ∧
                                                                PkgSig bundle P pkg ∧
                                                                  PkgSig bundle N pkg)
                                            hsame ∧
                                          UnaryHistory apartnessWindow ∧
                                            UnaryHistory modulusWindow ∧
                                              UnaryHistory finiteWindow ∧
                                                UnaryHistory dyadicRead ∧
                                                  UnaryHistory budgetRead ∧
                                                    UnaryHistory readbackRead ∧
                                                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro qUnary aUnary mUnary wUnary dUnary bUnary tUnary eUnary apartnessRoute
    modulusRoute finiteRoute dyadicRoute budgetRoute readbackRoute sealRoute appendAnchor
    provenancePkg namePkg
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
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, apartnessRoute, modulusRoute, finiteRoute, dyadicRoute,
            budgetRoute, readbackRoute, sealRoute, appendAnchor, provenancePkg, namePkg⟩
    }
  · exact
      ⟨apartnessUnary, modulusUnary, finiteUnary, dyadicUnary, budgetUnary, readbackUnary,
        sealUnary⟩

theorem RegularCauchyReciprocalScopeDependencyLock [AskSetup] [PackageSetup]
    {Q A M W D B T E H C P N apartnessWindow modulusWindow finiteWindow dyadicRead
      budgetRead readbackRead sealRead structuralRead replayRead provenanceRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q ->
      UnaryHistory A ->
        UnaryHistory M ->
          UnaryHistory W ->
            UnaryHistory D ->
              UnaryHistory B ->
                UnaryHistory T ->
                  UnaryHistory E ->
                    UnaryHistory H ->
                      UnaryHistory C ->
                        UnaryHistory P ->
                          UnaryHistory N ->
                            Cont Q A apartnessWindow ->
                              Cont apartnessWindow M modulusWindow ->
                                Cont modulusWindow W finiteWindow ->
                                  Cont finiteWindow D dyadicRead ->
                                    Cont dyadicRead B budgetRead ->
                                      Cont budgetRead T readbackRead ->
                                        Cont readbackRead E sealRead ->
                                          Cont sealRead H structuralRead ->
                                            Cont structuralRead C replayRead ->
                                              Cont replayRead P provenanceRead ->
                                                Cont provenanceRead N scopedRead ->
                                                  PkgSig bundle P pkg ->
                                                    PkgSig bundle N pkg ->
                                                      SemanticNameCert
                                                          (fun row : BHist =>
                                                            hsame row scopedRead ∧
                                                              UnaryHistory row)
                                                          (fun row : BHist =>
                                                            hsame row Q ∨ hsame row A ∨
                                                              hsame row M ∨
                                                                hsame row W ∨
                                                                  hsame row D ∨
                                                                    hsame row B ∨
                                                                      hsame row T ∨
                                                                        hsame row E ∨
                                                                          hsame row H ∨
                                                                            hsame row C ∨
                                                                              hsame row P ∨
                                                                                hsame row N ∨
                                                                                  hsame row
                                                                                    scopedRead)
                                                          (fun row : BHist =>
                                                            UnaryHistory row ∧
                                                              Cont Q A apartnessWindow ∧
                                                                Cont apartnessWindow M
                                                                  modulusWindow ∧
                                                                  Cont modulusWindow W
                                                                    finiteWindow ∧
                                                                    Cont finiteWindow D
                                                                      dyadicRead ∧
                                                                      Cont dyadicRead B
                                                                        budgetRead ∧
                                                                        Cont budgetRead T
                                                                          readbackRead ∧
                                                                          Cont readbackRead E
                                                                            sealRead ∧
                                                                            Cont sealRead H
                                                                              structuralRead ∧
                                                                              Cont structuralRead C
                                                                                replayRead ∧
                                                                                Cont replayRead P
                                                                                  provenanceRead ∧
                                                                                  Cont provenanceRead N
                                                                                    scopedRead ∧
                                                                                    PkgSig bundle P
                                                                                      pkg ∧
                                                                                      PkgSig bundle N
                                                                                        pkg)
                                                          hsame ∧
                                                        UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro qUnary aUnary mUnary wUnary dUnary bUnary tUnary eUnary hUnary cUnary pUnary
    nUnary apartnessRoute modulusRoute finiteRoute dyadicRoute budgetRoute readbackRoute
    sealRoute structuralRoute replayRoute provenanceRoute scopedRoute provenancePkg namePkg
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
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed sealUnary hUnary structuralRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed structuralUnary cUnary replayRoute
  have provenanceUnary : UnaryHistory provenanceRead :=
    unary_cont_closed replayUnary pUnary provenanceRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed provenanceUnary nUnary scopedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
                              (Or.inr
                                (Or.inr source.left)))))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, apartnessRoute, modulusRoute, finiteRoute, dyadicRoute,
            budgetRoute, readbackRoute, sealRoute, structuralRoute, replayRoute,
            provenanceRoute, scopedRoute, provenancePkg, namePkg⟩
    }
  · exact scopedUnary

end BEDC.Derived.RegularCauchyReciprocalUp
