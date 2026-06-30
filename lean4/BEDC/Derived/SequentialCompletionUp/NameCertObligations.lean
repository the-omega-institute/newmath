import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentialCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SequentialCompletionCarrier [AskSetup] [PackageSetup]
    (schedule readback dyadic criterion realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory readback ∧ UnaryHistory dyadic ∧
    UnaryHistory criterion ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem SequentialCompletionNamecertObligations [AskSetup] [PackageSetup]
    {S Q D K E H C P N readbackRead toleranceRead criterionRead sealRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S → UnaryHistory Q → UnaryHistory D → UnaryHistory K →
      UnaryHistory E → UnaryHistory N →
        Cont S Q readbackRead →
          Cont readbackRead D toleranceRead →
            Cont toleranceRead K criterionRead →
              Cont criterionRead E sealRead →
                Cont sealRead N localRead →
                  PkgSig bundle localRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row Q ∨ hsame row D ∨ hsame row K ∨
                            hsame row E ∨ hsame row N ∨ hsame row localRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont S Q readbackRead ∧
                            Cont readbackRead D toleranceRead ∧
                              Cont toleranceRead K criterionRead ∧
                                Cont criterionRead E sealRead ∧
                                  Cont sealRead N localRead ∧ PkgSig bundle localRead pkg)
                        hsame ∧ UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryS unaryQ unaryD unaryK unaryE unaryN
  intro routeReadback routeTolerance routeCriterion routeSeal routeLocal pkgLocal
  have unaryReadback : UnaryHistory readbackRead :=
    unary_cont_closed unaryS unaryQ routeReadback
  have unaryTolerance : UnaryHistory toleranceRead :=
    unary_cont_closed unaryReadback unaryD routeTolerance
  have unaryCriterion : UnaryHistory criterionRead :=
    unary_cont_closed unaryTolerance unaryK routeCriterion
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryCriterion unaryE routeSeal
  have unaryLocal : UnaryHistory localRead :=
    unary_cont_closed unarySeal unaryN routeLocal
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro localRead (And.intro (hsame_refl localRead) unaryLocal)
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
        intro row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro row source
        exact
          And.intro source.right
            (And.intro routeReadback
              (And.intro routeTolerance
                (And.intro routeCriterion
                  (And.intro routeSeal (And.intro routeLocal pkgLocal)))))
    }
  · exact unaryLocal

theorem SequentialCompletionRegseqratRealHandoff [AskSetup] [PackageSetup]
    {schedule readback dyadic criterion realSeal transport replay provenance localName
      scheduleRead dyadicRead criterionRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompletionCarrier schedule readback dyadic criterion realSeal transport replay
      provenance localName bundle pkg →
      Cont schedule readback scheduleRead →
        Cont scheduleRead dyadic dyadicRead →
          Cont dyadicRead criterion criterionRead →
            Cont criterionRead realSeal sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory scheduleRead ∧ UnaryHistory dyadicRead ∧
                  UnaryHistory criterionRead ∧ UnaryHistory sealRead ∧
                    Cont schedule readback scheduleRead ∧
                      Cont scheduleRead dyadic dyadicRead ∧
                        Cont dyadicRead criterion criterionRead ∧
                          Cont criterionRead realSeal sealRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory SequentialCompletionCarrier
  intro carrier scheduleRoute dyadicRoute criterionRoute sealRoute sealPkg
  obtain ⟨scheduleUnary, readbackUnary, _dyadicUnary, _criterionUnary, realSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, provenancePkg,
    _localNamePkg⟩ := carrier
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed scheduleUnary readbackUnary scheduleRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed scheduleReadUnary _dyadicUnary dyadicRoute
  have criterionReadUnary : UnaryHistory criterionRead :=
    unary_cont_closed dyadicReadUnary _criterionUnary criterionRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed criterionReadUnary realSealUnary sealRoute
  exact
    ⟨scheduleReadUnary, dyadicReadUnary, criterionReadUnary, sealReadUnary,
      scheduleRoute, dyadicRoute, criterionRoute, sealRoute, provenancePkg, sealPkg⟩

end BEDC.Derived.SequentialCompletionUp
