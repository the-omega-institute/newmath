import BEDC.Derived.SequentialCompletionUp.NameCertObligations

namespace BEDC.Derived.SequentialCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompletionRegSeqRatRealHandoff [AskSetup] [PackageSetup]
    {S Q D K E H C P N readbackRead toleranceRead criterionRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory Q →
        UnaryHistory D →
          UnaryHistory K →
            UnaryHistory E →
              Cont S Q readbackRead →
                Cont readbackRead D toleranceRead →
                  Cont toleranceRead K criterionRead →
                    Cont criterionRead E sealRead →
                      PkgSig bundle sealRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row Q ∨ hsame row D ∨ hsame row K ∨
                                hsame row E ∨ hsame row sealRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont S Q readbackRead ∧
                                Cont readbackRead D toleranceRead ∧
                                  Cont toleranceRead K criterionRead ∧
                                    Cont criterionRead E sealRead ∧
                                      PkgSig bundle sealRead pkg)
                            hsame ∧
                          UnaryHistory readbackRead ∧ UnaryHistory toleranceRead ∧
                            UnaryHistory criterionRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryS unaryQ unaryD unaryK unaryE routeReadback routeTolerance routeCriterion
    routeSeal pkgSeal
  have unaryReadback : UnaryHistory readbackRead :=
    unary_cont_closed unaryS unaryQ routeReadback
  have unaryTolerance : UnaryHistory toleranceRead :=
    unary_cont_closed unaryReadback unaryD routeTolerance
  have unaryCriterion : UnaryHistory criterionRead :=
    unary_cont_closed unaryTolerance unaryK routeCriterion
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryCriterion unaryE routeSeal
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro sealRead (And.intro (hsame_refl sealRead) unarySeal)
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
            And.intro (hsame_trans (hsame_symm sameRows) source.left)
              (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact
          And.intro source.right
            (And.intro routeReadback
              (And.intro routeTolerance
                (And.intro routeCriterion (And.intro routeSeal pkgSeal))))
    }
  · exact And.intro unaryReadback
      (And.intro unaryTolerance (And.intro unaryCriterion unarySeal))

end BEDC.Derived.SequentialCompletionUp
