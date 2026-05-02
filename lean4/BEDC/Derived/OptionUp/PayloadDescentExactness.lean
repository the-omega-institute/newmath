import BEDC.Derived.OptionUp.PayloadDescent

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionMapRel_identity_carrier_hsame_iff {S : BHist -> Prop} {h k : BHist} :
    let delta : DescentCertificate BHist BHist hsame hsame :=
      { map := fun a => a
        respects := by
          intro _a _b same
          exact same }
    TaggedOptionMapRel S S delta h k ↔ TaggedOptionHistoryCarrier S h ∧ hsame h k := by
  constructor
  · intro mapRel
    cases mapRel with
    | inl absent =>
        exact And.intro (Or.inl absent.left)
          (hsame_trans absent.left (hsame_symm absent.right))
    | inr present =>
        cases present with
        | intro a data =>
            exact And.intro (Or.inr (Exists.intro a (And.intro data.left data.right.right.left)))
              (hsame_trans data.right.right.left (hsame_symm data.right.right.right))
  · intro data
    cases data with
    | intro carrier sameHK =>
        cases carrier with
        | inl absent =>
            exact Or.inl (And.intro absent (hsame_trans (hsame_symm sameHK) absent))
        | inr present =>
            cases present with
            | intro a sourceData =>
                exact Or.inr
                  (Exists.intro a
                    (And.intro sourceData.left
                      (And.intro sourceData.left
                        (And.intro sourceData.right
                          (hsame_trans (hsame_symm sameHK) sourceData.right)))))

theorem TaggedOptionMapRel_visible_payload_readback {S T : BHist -> Prop}
    {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT) {h k u v : BHist} :
    TaggedOptionMapRel S T delta h k -> S u -> hsame h (BHist.e1 u) -> T v ->
      hsame k (BHist.e1 v) ->
        ∃ a : BHist, S a ∧ T (delta.map a) ∧ hsame u a ∧ hsame v (delta.map a) := by
  intro mapRel _sourceU sameHU _targetV sameKV
  cases mapRel with
  | inl absent =>
      exact False.elim (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameHU))
  | inr present =>
      cases present with
      | intro a data =>
          have sameUA : hsame u a :=
            hsame_e1_iff.mp (hsame_trans (hsame_symm sameHU) data.right.right.left)
          have sameVDelta : hsame v (delta.map a) :=
            hsame_e1_iff.mp (hsame_trans (hsame_symm sameKV) data.right.right.right)
          exact Exists.intro a
            (And.intro data.left (And.intro data.right.left (And.intro sameUA sameVDelta)))

theorem TaggedOptionMapRel_target_carrier {S T : BHist -> Prop}
    {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT) {h k : BHist} :
    TaggedOptionMapRel S T delta h k -> TaggedOptionHistoryCarrier T k := by
  intro mapRel
  cases mapRel with
  | inl absent =>
      exact Or.inl absent.right
  | inr present =>
      cases present with
      | intro a data =>
          exact Or.inr
            (Exists.intro (delta.map a) (And.intro data.right.left data.right.right.right))

end BEDC.Derived.OptionUp
