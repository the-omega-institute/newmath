import BEDC.Derived.DyadicNestedIntervalSelectorUp.RealHandoff
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.DyadicNestedIntervalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem DyadicNestedIntervalSelectorPrefixSeal [AskSetup] [PackageSetup]
    {I D S R E H C P N nestedRead dyadicRead streamRead regularRead realRead
      replayRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    dyadicNestedIntervalSelectorToEventFlow
        (DyadicNestedIntervalSelectorUp.mk I D S R E H C P N) =
        [dyadicNestedIntervalSelectorEncodeBHist I, dyadicNestedIntervalSelectorEncodeBHist D,
          dyadicNestedIntervalSelectorEncodeBHist S, dyadicNestedIntervalSelectorEncodeBHist R,
          dyadicNestedIntervalSelectorEncodeBHist E, dyadicNestedIntervalSelectorEncodeBHist H,
          dyadicNestedIntervalSelectorEncodeBHist C, dyadicNestedIntervalSelectorEncodeBHist P,
          dyadicNestedIntervalSelectorEncodeBHist N] →
      Cont I D nestedRead →
        Cont D S dyadicRead →
          Cont S R streamRead →
            Cont R E realRead →
              Cont H C replayRead →
                PkgSig bundle P pkg →
                  PkgSig bundle N pkg →
                    SemanticNameCert
                      (fun row : BHist => hsame row realRead ∧ Cont R E realRead)
                      (fun row : BHist =>
                        hsame row I ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
                          hsame row E ∨ hsame row realRead ∨ Cont H C replayRead)
                      (fun row : BHist =>
                        hsame row realRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle N pkg ∧ Cont I D nestedRead ∧
                            Cont D S dyadicRead ∧ Cont S R streamRead ∧
                              Cont R E realRead)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fieldRows nestedRoute dyadicRoute streamRoute realRoute replayRoute provenancePkg
    namePkg
  cases fieldRows
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro realRead (And.intro (hsame_refl realRead) realRoute)
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
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact
        And.intro source.left
          (And.intro provenancePkg
            (And.intro namePkg
              (And.intro nestedRoute
                (And.intro dyadicRoute
                  (And.intro streamRoute source.right)))))
  }

end BEDC.Derived.DyadicNestedIntervalSelectorUp
