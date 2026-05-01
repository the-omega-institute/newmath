import BEDC.FKernel.Bundle

namespace BEDC.FKernel.Bundle

theorem bundleAppend_cons_result_iff {PName : Type}
    {pref suff out : ProbeBundle PName} {p : PName} :
    bundleAppend pref suff = ProbeBundle.Bcons p out ↔
      (pref = ProbeBundle.Bnil ∧ suff = ProbeBundle.Bcons p out) ∨
        ∃ pref0 : ProbeBundle PName,
          pref = ProbeBundle.Bcons p pref0 ∧ bundleAppend pref0 suff = out := by
  constructor
  · intro same
    exact bundleAppend_cons_result_inversion same
  · intro split
    cases split with
    | inl emptyCase =>
        cases emptyCase with
        | intro prefEmpty suffCons =>
            cases prefEmpty
            exact suffCons
    | inr consCase =>
        cases consCase with
        | intro pref0 data =>
            cases data with
            | intro prefCons tailSame =>
                cases prefCons
                cases tailSame
                rfl

end BEDC.FKernel.Bundle
