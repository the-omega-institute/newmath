import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.SetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def SetPkgMembershipSource [AskSetup] [PackageSetup]
    (bundle : ProbeBundle ProbeName) (h : BHist) : Prop :=
  exists p : Pkg, TokIntro bundle h p

theorem SetPkgMembership_semantic_name_certificate [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName}
    (witness : exists h : BHist, SetPkgMembershipSource bundle h)
    (tok : TokUnique bundle) :
    SemanticNameCert (SetPkgMembershipSource bundle) (SetPkgMembershipSource bundle)
      (SetPkgMembershipSource bundle)
      (fun h k : BHist =>
        exists p : Pkg, exists q : Pkg,
          TokIntro bundle h p ∧ TokIntro bundle k q ∧ psame bundle p q) := by
  constructor
  · constructor
    · exact witness
    · intro h source
      cases source with
      | intro p token =>
          exact Exists.intro p
            (Exists.intro p
              (And.intro token
                (And.intro token (psame.intro token token (hsame_refl h)))))
    · intro h k classified
      cases classified with
      | intro p classifiedTail =>
          cases classifiedTail with
          | intro q rows =>
              exact Exists.intro q
                (Exists.intro p
                  (And.intro rows.right.left
                    (And.intro rows.left
                      (packageTokenPolicy_psame_symm_on_introduced
                        (packageTokenPolicy_from_tokUnique tok) rows.left rows.right.left
                        rows.right.right))))
    · intro h k r leftClass rightClass
      cases leftClass with
      | intro p leftTail =>
          cases leftTail with
          | intro q leftRows =>
              cases rightClass with
              | intro q' rightTail =>
                  cases rightTail with
                  | intro s rightRows =>
                      have sameHK : hsame h k :=
                        package_reflection_token_unique tok leftRows.left leftRows.right.left
                          leftRows.right.right
                      have sameKR : hsame k r :=
                        package_reflection_token_unique tok rightRows.left rightRows.right.left
                          rightRows.right.right
                      have link : psame bundle q s :=
                        psame.intro leftRows.right.left rightRows.right.left sameKR
                      have whole : psame bundle p s :=
                        psame.intro leftRows.left rightRows.right.left
                          (hsame_trans sameHK sameKR)
                      exact Exists.intro p
                        (Exists.intro s
                          (And.intro leftRows.left
                            (And.intro rightRows.right.left whole)))
    · intro h k classified source
      cases classified with
      | intro p classifiedTail =>
          cases classifiedTail with
          | intro q rows =>
              exact Exists.intro q rows.right.left
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.SetUp
