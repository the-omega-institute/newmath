import BEDC.Derived.RegularCauchyReciprocalUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyReciprocalUp.TasteGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyReciprocalScopedDenominatorApartness [AskSetup] [PackageSetup]
    {Q A M W D B H C P N apartnessWindow modulusWindow finiteWindow dyadicRead
      budgetRead transportRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q →
      UnaryHistory A →
        UnaryHistory M →
          UnaryHistory W →
            UnaryHistory D →
              UnaryHistory B →
                UnaryHistory H →
                  UnaryHistory C →
                    Cont Q A apartnessWindow →
                      Cont apartnessWindow M modulusWindow →
                        Cont modulusWindow W finiteWindow →
                          Cont finiteWindow D dyadicRead →
                            Cont dyadicRead B budgetRead →
                              Cont budgetRead H transportRead →
                                Cont transportRead C scopedRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row scopedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row Q ∨ hsame row A ∨ hsame row M ∨
                                              hsame row W ∨ hsame row D ∨ hsame row B ∨
                                                hsame row H ∨ hsame row C ∨
                                                  hsame row scopedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont Q A apartnessWindow ∧
                                              Cont apartnessWindow M modulusWindow ∧
                                                Cont modulusWindow W finiteWindow ∧
                                                  Cont finiteWindow D dyadicRead ∧
                                                    Cont dyadicRead B budgetRead ∧
                                                      Cont budgetRead H transportRead ∧
                                                        Cont transportRead C scopedRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro qUnary aUnary mUnary wUnary dUnary bUnary hUnary cUnary apartnessRoute
    modulusRoute finiteRoute dyadicRoute budgetRoute transportRoute scopedRoute
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
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed budgetUnary hUnary transportRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed transportUnary cUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨
              hsame row B ∨ hsame row H ∨ hsame row C ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q A apartnessWindow ∧
              Cont apartnessWindow M modulusWindow ∧ Cont modulusWindow W finiteWindow ∧
                Cont finiteWindow D dyadicRead ∧ Cont dyadicRead B budgetRead ∧
                  Cont budgetRead H transportRead ∧ Cont transportRead C scopedRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, apartnessRoute, modulusRoute, finiteRoute, dyadicRoute,
          budgetRoute, transportRoute, scopedRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, scopedUnary⟩

end BEDC.Derived.RegularCauchyReciprocalUp.TasteGate
