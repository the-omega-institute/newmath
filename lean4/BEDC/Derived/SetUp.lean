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

def SetMembershipVisibleCarrier [AskSetup] [PackageSetup]
    (bundle : ProbeBundle ProbeName) (h : BHist) : Prop :=
  ∃ p : Pkg, TokIntro bundle h p

def SetMembershipVisibleClassifier [AskSetup] [PackageSetup]
    (bundle : ProbeBundle ProbeName) (h k : BHist) : Prop :=
  ∃ p : Pkg, ∃ q : Pkg, TokIntro bundle h p ∧ TokIntro bundle k q ∧ psame bundle p q

theorem SetMembershipVisibleClassifier_carrier_hsame_boundary [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle) {h k : BHist} :
    SetMembershipVisibleClassifier bundle h k ->
      SetMembershipVisibleCarrier bundle h ∧ SetMembershipVisibleCarrier bundle k ∧ hsame h k := by
  intro visible
  cases visible with
  | intro p rest =>
      cases rest with
      | intro q data =>
          exact And.intro
            (Exists.intro p data.left)
            (And.intro
              (Exists.intro q data.right.left)
              (policy.reflection data.left data.right.left data.right.right))

theorem SetCarrier_obligation_surface [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle) {h k : BHist} :
    SetMembershipVisibleClassifier bundle h k ->
      SetMembershipVisibleCarrier bundle h ∧ SetMembershipVisibleCarrier bundle k ∧
        hsame h k ∧ SetMembershipVisibleClassifier bundle k h := by
  intro visible
  cases visible with
  | intro p rest =>
      cases rest with
      | intro q data =>
          have sameHist : hsame h k :=
            policy.reflection data.left data.right.left data.right.right
          have reversedSame : psame bundle q p :=
            packageTokenPolicy_psame_symm_on_introduced policy data.left data.right.left
              data.right.right
          exact And.intro
            (Exists.intro p data.left)
            (And.intro
              (Exists.intro q data.right.left)
              (And.intro sameHist
                (Exists.intro q
                  (Exists.intro p
                    (And.intro data.right.left
                      (And.intro data.left reversedSame))))))

inductive SetMembershipVisibleTransportChain [AskSetup] [PackageSetup]
    (bundle : ProbeBundle ProbeName) : BHist -> BHist -> Prop where
  | single {h k : BHist} :
      SetMembershipVisibleClassifier bundle h k ->
        SetMembershipVisibleTransportChain bundle h k
  | cons {h k r : BHist} :
      SetMembershipVisibleClassifier bundle h k ->
        SetMembershipVisibleTransportChain bundle k r ->
          SetMembershipVisibleTransportChain bundle h r

theorem SetMembershipVisibleTransportChain_hsame [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle) {h k : BHist} :
    SetMembershipVisibleTransportChain bundle h k -> hsame h k := by
  intro chain
  induction chain with
  | single visible =>
      cases visible with
      | intro p rest =>
          cases rest with
          | intro q data =>
              exact policy.reflection data.left data.right.left data.right.right
  | cons visible _ tailSame =>
      cases visible with
      | intro p rest =>
          cases rest with
          | intro q data =>
              have headSame :=
                policy.reflection data.left data.right.left data.right.right
              exact hsame_trans headSame tailSame

theorem SetMembershipVisibleClassifier_carrier_rows [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {h k : BHist} :
    SetMembershipVisibleClassifier bundle h k ->
      SetMembershipVisibleCarrier bundle h ∧ SetMembershipVisibleCarrier bundle k := by
  intro visible
  cases visible with
  | intro p rest =>
      cases rest with
      | intro q data =>
          exact And.intro
            (Exists.intro p data.left)
            (Exists.intro q data.right.left)

theorem SetMembershipVisibleTransportChain_carrier_transport [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {h k : BHist} :
    SetMembershipVisibleCarrier bundle h ->
      SetMembershipVisibleTransportChain bundle h k ->
        SetMembershipVisibleCarrier bundle k := by
  intro carrier chain
  induction chain with
  | single visible =>
      exact (SetMembershipVisibleClassifier_carrier_rows visible).right
  | cons visible _ tailCarrier =>
      exact tailCarrier (SetMembershipVisibleClassifier_carrier_rows visible).right

theorem SetPublicNameCert_transport_target_carrier [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {h k : BHist} :
    SetMembershipVisibleTransportChain bundle h k -> SetMembershipVisibleCarrier bundle k := by
  intro chain
  induction chain with
  | single visible =>
      exact (SetMembershipVisibleClassifier_carrier_rows visible).right
  | cons _ _ tailCarrier =>
      exact tailCarrier

end BEDC.Derived.SetUp
