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

theorem TaggedOptionMapRel_exclusive_visible_readback_single_valued {S T : BHist -> Prop}
    {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT) {h k : BHist} :
    TaggedOptionMapRel S T delta h k ->
      ((hsame h BHist.Empty ∧ hsame k BHist.Empty ∧
          (forall a' : BHist, S a' -> hsame h (BHist.e1 a') -> False) ∧
          (forall b : BHist, T b -> hsame k (BHist.e1 b) -> False)) ∨
        (exists a : BHist,
          S a ∧ T (delta.map a) ∧ hsame h (BHist.e1 a) ∧
            hsame k (BHist.e1 (delta.map a)) ∧
              (hsame h BHist.Empty -> False) ∧ (hsame k BHist.Empty -> False) ∧
                (forall a' : BHist, S a' -> hsame h (BHist.e1 a') -> hsame a a') ∧
                  (forall b : BHist, T b -> hsame k (BHist.e1 b) ->
                    hsame b (delta.map a)))) := by
  intro mapRel
  cases mapRel with
  | inl absent =>
      have noSource :
          forall a' : BHist, S a' -> hsame h (BHist.e1 a') -> False := by
        intro a' _sourceA' samePresent
        exact not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) samePresent)
      have noTarget :
          forall b : BHist, T b -> hsame k (BHist.e1 b) -> False := by
        intro b _targetB samePresent
        exact not_hsame_emp_e1 (hsame_trans (hsame_symm absent.right) samePresent)
      exact Or.inl (And.intro absent.left (And.intro absent.right
        (And.intro noSource noTarget)))
  | inr present =>
      cases present with
      | intro a data =>
          have notSourceEmpty : hsame h BHist.Empty -> False := by
            intro sameEmpty
            exact not_hsame_e1_empty
              (hsame_trans (hsame_symm data.right.right.left) sameEmpty)
          have notTargetEmpty : hsame k BHist.Empty -> False := by
            intro sameEmpty
            exact not_hsame_e1_empty
              (hsame_trans (hsame_symm data.right.right.right) sameEmpty)
          have sourceUnique :
              forall a' : BHist, S a' -> hsame h (BHist.e1 a') -> hsame a a' := by
            intro a' _sourceA' samePresent
            exact hsame_e1_iff.mp
              (hsame_trans (hsame_symm data.right.right.left) samePresent)
          have targetUnique :
              forall b : BHist, T b -> hsame k (BHist.e1 b) -> hsame b (delta.map a) := by
            intro b _targetB samePresent
            exact hsame_e1_iff.mp
              (hsame_trans (hsame_symm samePresent) data.right.right.right)
          exact Or.inr
            (Exists.intro a
              (And.intro data.left
                (And.intro data.right.left
                  (And.intro data.right.right.left
                    (And.intro data.right.right.right
                      (And.intro notSourceEmpty
                        (And.intro notTargetEmpty
                          (And.intro sourceUnique targetUnique))))))))

end BEDC.Derived.OptionUp
