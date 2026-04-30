import BEDC.FKernel.Bundle

namespace BEDC.FKernel.Bundle

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

end BEDC.FKernel.Bundle
