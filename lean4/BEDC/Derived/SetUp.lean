import BEDC.FKernel.Package

namespace BEDC.Derived.SetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def SetMembershipVisibleCarrier [AskSetup] [PackageSetup]
    (bundle : ProbeBundle ProbeName) (h : BHist) : Prop :=
  ∃ p : Pkg, TokIntro bundle h p

def SetMembershipVisibleClassifier [AskSetup] [PackageSetup]
    (bundle : ProbeBundle ProbeName) (h k : BHist) : Prop :=
  ∃ p : Pkg, ∃ q : Pkg, TokIntro bundle h p ∧ TokIntro bundle k q ∧ psame bundle p q

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

end BEDC.Derived.SetUp
