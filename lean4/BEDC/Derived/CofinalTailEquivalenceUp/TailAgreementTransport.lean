import BEDC.Derived.CofinalTailEquivalenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CofinalTailEquivalenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CofinalTailEquivalenceTailAgreementTransport [AskSetup] [PackageSetup]
    {R0 R1 W Q D A H C P N route0 route1 sharedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cofinalTailEquivalenceFields (CofinalTailEquivalenceUp.mk R0 R1 W Q D A H C P N) =
        [R0, R1, W, Q, D, A, H, C, P, N] ->
      UnaryHistory R0 ->
        UnaryHistory R1 ->
          UnaryHistory W ->
            UnaryHistory Q ->
              UnaryHistory D ->
                Cont R0 W route0 ->
                  Cont R1 W route1 ->
                    Cont Q D sharedRead ->
                      PkgSig bundle sharedRead pkg ->
                        SemanticNameCert
                            (fun row : BHist =>
                              (hsame row route0 ∨ hsame row route1 ∨
                                  hsame row sharedRead) ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row R0 ∨ hsame row R1 ∨ hsame row W ∨
                                hsame row Q ∨ hsame row D ∨ hsame row A ∨
                                  hsame row route0 ∨ hsame row route1 ∨
                                    hsame row sharedRead)
                            (fun _row : BHist =>
                              UnaryHistory route0 ∧ UnaryHistory route1 ∧
                                UnaryHistory sharedRead ∧ Cont R0 W route0 ∧
                                  Cont R1 W route1 ∧ Cont Q D sharedRead ∧
                                    PkgSig bundle sharedRead pkg)
                            hsame ∧
                          UnaryHistory route0 ∧
                            UnaryHistory route1 ∧ UnaryHistory sharedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fieldProjection unaryR0 unaryR1 unaryW unaryQ unaryD route0Cont route1Cont
    sharedReadCont sharedReadPkg
  have projectedFields :
      cofinalTailEquivalenceFields (CofinalTailEquivalenceUp.mk R0 R1 W Q D A H C P N) =
        [R0, R1, W, Q, D, A, H, C, P, N] :=
    fieldProjection
  have route0Unary : UnaryHistory route0 :=
    unary_cont_closed unaryR0 unaryW route0Cont
  have route1Unary : UnaryHistory route1 :=
    unary_cont_closed unaryR1 unaryW route1Cont
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed unaryQ unaryD sharedReadCont
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row route0 ∨ hsame row route1 ∨ hsame row sharedRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row R0 ∨ hsame row R1 ∨ hsame row W ∨ hsame row Q ∨
              hsame row D ∨ hsame row A ∨ hsame row route0 ∨
                hsame row route1 ∨ hsame row sharedRead)
          (fun _row : BHist =>
            UnaryHistory route0 ∧ UnaryHistory route1 ∧ UnaryHistory sharedRead ∧
              Cont R0 W route0 ∧ Cont R1 W route1 ∧ Cont Q D sharedRead ∧
                PkgSig bundle sharedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro route0
          ⟨Or.inl (hsame_refl route0), route0Unary⟩
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
        have sameOtherRow : hsame _row _other := sameRows
        have otherUnary : UnaryHistory _other :=
          unary_transport source.right sameOtherRow
        cases source.left with
        | inl sameRoute0 =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameOtherRow) sameRoute0),
                otherUnary⟩
        | inr route1OrShared =>
            cases route1OrShared with
            | inl sameRoute1 =>
                exact
                  ⟨Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameOtherRow) sameRoute1)),
                    otherUnary⟩
            | inr sameShared =>
                exact
                  ⟨Or.inr
                      (Or.inr (hsame_trans (hsame_symm sameOtherRow) sameShared)),
                    otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases projectedFields
      cases source.left with
      | inl sameRoute0 =>
          exact Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameRoute0))))))
      | inr route1OrShared =>
          cases route1OrShared with
          | inl sameRoute1 =>
              exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inl sameRoute1)))))))
          | inr sameShared =>
              exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr sameShared)))))))
    ledger_sound := by
      intro _row _source
      exact
        ⟨route0Unary, route1Unary, sharedReadUnary, route0Cont, route1Cont,
          sharedReadCont, sharedReadPkg⟩
  }
  exact ⟨cert, route0Unary, route1Unary, sharedReadUnary⟩

end BEDC.Derived.CofinalTailEquivalenceUp
