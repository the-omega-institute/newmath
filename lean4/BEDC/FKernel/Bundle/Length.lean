import BEDC.FKernel.Bundle

namespace BEDC.FKernel.Bundle

theorem bundleLength_eq_zero_iff_nil {PName : Type} {bundle : ProbeBundle PName} :
    bundleLength bundle = 0 ↔ bundle = ProbeBundle.Bnil := by
  constructor
  · intro h
    cases bundle with
    | Bnil =>
        rfl
    | Bcons _ _ =>
        cases h
  · intro h
    cases h
    rfl

theorem bundleLength_zero_iff_nil {PName : Type} {bundle : ProbeBundle PName} :
    bundleLength bundle = 0 ↔ bundle = ProbeBundle.Bnil :=
  bundleLength_eq_zero_iff_nil

theorem bundleLength_eq_one_iff_singleton {PName : Type} {bundle : ProbeBundle PName} :
    bundleLength bundle = Nat.succ 0 ↔
      ∃ p : PName, bundle = ProbeBundle.Bcons p ProbeBundle.Bnil := by
  constructor
  · intro h
    cases bundle with
    | Bnil =>
        cases h
    | Bcons p tail =>
        have htail : bundleLength tail = 0 := Nat.succ.inj h
        have tailNil : tail = ProbeBundle.Bnil := bundleLength_eq_zero_iff_nil.mp htail
        cases tailNil
        exact Exists.intro p rfl
  · intro witness
    cases witness with
    | intro p hp =>
        cases hp
        rfl

theorem inBundle_length_one_singleton {PName : Type} {p : PName}
    {bundle : ProbeBundle PName} :
    InBundle p bundle -> bundleLength bundle = Nat.succ 0 ->
      bundle = ProbeBundle.Bcons p ProbeBundle.Bnil := by
  intro member lengthOne
  cases bundle with
  | Bnil =>
      cases member
  | Bcons q tail =>
      have tailLengthZero : bundleLength tail = 0 := Nat.succ.inj lengthOne
      have tailNil : tail = ProbeBundle.Bnil :=
        bundleLength_eq_zero_iff_nil.mp tailLengthZero
      cases member with
      | inl headSame =>
          cases headSame
          cases tailNil
          rfl
      | inr tailMember =>
          cases tailNil
          cases tailMember

theorem inBundle_length_one_unique {PName : Type} {p q : PName}
    {bundle : ProbeBundle PName} :
    InBundle p bundle -> InBundle q bundle -> bundleLength bundle = Nat.succ 0 ->
      p = q := by
  intro pMember qMember lengthOne
  have pSingleton : bundle = ProbeBundle.Bcons p ProbeBundle.Bnil :=
    inBundle_length_one_singleton pMember lengthOne
  have qSingleton : bundle = ProbeBundle.Bcons q ProbeBundle.Bnil :=
    inBundle_length_one_singleton qMember lengthOne
  cases pSingleton
  exact (ProbeBundle.Bcons.inj qSingleton).left

theorem bundleLength_eq_succ_iff_cons {PName : Type} {bundle : ProbeBundle PName} {n : Nat} :
    bundleLength bundle = Nat.succ n ↔
      ∃ p : PName, ∃ tail : ProbeBundle PName,
        bundle = ProbeBundle.Bcons p tail ∧ bundleLength tail = n := by
  constructor
  · intro h
    cases bundle with
    | Bnil =>
        cases h
    | Bcons p tail =>
        exact ⟨p, tail, rfl, Nat.succ.inj h⟩
  · intro witness
    cases witness with
    | intro p rest =>
        cases rest with
        | intro tail payload =>
            cases payload.left
            exact congrArg Nat.succ payload.right

theorem bundleAppend_nonempty_prefix_length_separation {PName : Type} (p : PName)
    (pref suff : ProbeBundle PName) :
    bundleLength (bundleAppend (ProbeBundle.Bcons p pref) suff) ≠ bundleLength suff ∧
      bundleAppend (ProbeBundle.Bcons p pref) suff ≠ suff := by
  have natSep : ∀ n : Nat, Nat.succ (bundleLength pref) + n ≠ n := by
    intro n
    induction n with
    | zero =>
        intro h
        cases h
    | succ n ih =>
        intro h
        exact ih (Nat.succ.inj h)
  have lengthEq :
      bundleLength (bundleAppend (ProbeBundle.Bcons p pref) suff) =
        Nat.succ (bundleLength pref) + bundleLength suff :=
    bundleLength_append (ProbeBundle.Bcons p pref) suff
  have lengthNe :
      bundleLength (bundleAppend (ProbeBundle.Bcons p pref) suff) ≠ bundleLength suff := by
    intro h
    exact natSep (bundleLength suff) (Eq.trans lengthEq.symm h)
  constructor
  · exact lengthNe
  · intro h
    exact lengthNe (congrArg bundleLength h)

theorem bundleAppend_eq_right_iff_left_nil {PName : Type}
    {left right : ProbeBundle PName} :
    bundleAppend left right = right <-> left = ProbeBundle.Bnil := by
  constructor
  · intro same
    cases left with
    | Bnil =>
        rfl
    | Bcons p pref =>
        exact False.elim ((bundleAppend_nonempty_prefix_length_separation p pref right).right same)
  · intro leftNil
    cases leftNil
    rfl

theorem bundleAppend_eq_left_iff_right_nil {PName : Type}
    {left right : ProbeBundle PName} :
    bundleAppend left right = left ↔ right = ProbeBundle.Bnil := by
  constructor
  · intro same
    induction left with
    | Bnil =>
        exact same
    | Bcons _ tail ih =>
        exact ih (ProbeBundle.Bcons.inj same).right
  · intro rightNil
    cases rightNil
    exact bundleAppend_right_nil left

end BEDC.FKernel.Bundle
