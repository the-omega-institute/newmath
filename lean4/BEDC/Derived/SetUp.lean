import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.SetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem SetExtensionalityLedger_semantic_name_certificate [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {s : BHist} {p : Pkg}
    (token : TokIntro bundle s p) :
    SemanticNameCert
      (fun h : BHist => exists q : Pkg, TokIntro bundle h q)
      (fun h : BHist => exists q : Pkg, TokIntro bundle h q)
      (fun h : BHist => exists q : Pkg, TokIntro bundle h q)
      (fun h k : BHist =>
        hsame h k ∧ exists ph : Pkg, exists pk : Pkg,
          TokIntro bundle h ph ∧ TokIntro bundle k pk ∧ psame bundle ph pk) := by
  constructor
  · constructor
    · exact Exists.intro s (Exists.intro p token)
    · intro h carrier
      cases carrier with
      | intro q tokenH =>
          exact And.intro (hsame_refl h)
            (Exists.intro q
              (Exists.intro q
                (And.intro tokenH
                  (And.intro tokenH (psame.intro tokenH tokenH (hsame_refl h))))))
    · intro h k classified
      cases classified.right with
      | intro ph rest =>
          cases rest with
          | intro pk fields =>
              exact And.intro (hsame_symm classified.left)
                (Exists.intro pk
                  (Exists.intro ph
                    (And.intro fields.right.left
                      (And.intro fields.left (psame_symm_constructor fields.right.right)))))
    · intro h k r classifiedLeft classifiedRight
      cases classifiedLeft.right with
      | intro ph leftRest =>
          cases leftRest with
          | intro _pk leftFields =>
              cases classifiedRight.right with
              | intro _qk rightRest =>
                  cases rightRest with
                  | intro pr rightFields =>
                      have sameHR : hsame h r :=
                        hsame_trans classifiedLeft.left classifiedRight.left
                      exact And.intro sameHR
                        (Exists.intro ph
                          (Exists.intro pr
                            (And.intro leftFields.left
                              (And.intro rightFields.right.left
                                (psame.intro leftFields.left rightFields.right.left sameHR)))))
    · intro h k classified _carrier
      cases classified.right with
      | intro _ph rest =>
          cases rest with
          | intro pk fields =>
              exact Exists.intro pk fields.right.left
  · intro _h source
    exact source
  · intro _h source
    exact source

end BEDC.Derived.SetUp
