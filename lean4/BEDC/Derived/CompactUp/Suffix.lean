import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CompactNetWitness_suffix_iff {p center precision net : BHist} :
    CompactNetWitness center (append precision p) (append net p) ↔
      UnaryHistory p ∧ CompactNetWitness center precision net := by
  constructor
  · intro witness
    cases witness with
    | intro centerCarrier rest =>
        cases rest with
        | intro precisionSuffixCarrier rest =>
            cases rest with
            | intro netSuffixCarrier netRel =>
                have precisionCarrier : UnaryHistory precision :=
                  unary_append_left_factor precisionSuffixCarrier
                have suffixCarrier : UnaryHistory p :=
                  unary_append_right_factor precisionSuffixCarrier
                have netCarrier : UnaryHistory net :=
                  unary_append_left_factor netSuffixCarrier
                have baseRel : Cont center precision net := by
                  apply cont_intro
                  exact append_right_cancel (k := p)
                    (netRel.trans (append_assoc center precision p).symm)
                exact And.intro suffixCarrier
                  (And.intro centerCarrier
                    (And.intro precisionCarrier (And.intro netCarrier baseRel)))
  · intro data
    cases data with
    | intro suffixCarrier witness =>
        cases witness with
        | intro centerCarrier rest =>
            cases rest with
            | intro precisionCarrier rest =>
                cases rest with
                | intro netCarrier netRel =>
                    have precisionSuffixCarrier : UnaryHistory (append precision p) :=
                      unary_append_closed precisionCarrier suffixCarrier
                    have netSuffixCarrier : UnaryHistory (append net p) :=
                      unary_append_closed netCarrier suffixCarrier
                    have suffixedRel : Cont center (append precision p) (append net p) := by
                      cases netRel
                      exact cont_intro (append_assoc center precision p)
                    exact And.intro centerCarrier
                      (And.intro precisionSuffixCarrier
                        (And.intro netSuffixCarrier suffixedRel))

theorem CompactNetWitness_visible_context_iff {p q center precision net : BHist} :
    CompactNetWitness (append p center) (append precision q) (append (append p net) q) ↔
      UnaryHistory p ∧ UnaryHistory q ∧ CompactNetWitness center precision net := by
  constructor
  · intro witness
    have suffixData := CompactNetWitness_suffix_iff.mp witness
    have prefixData := CompactNetWitness_prefix_iff.mp suffixData.right
    exact And.intro prefixData.left (And.intro suffixData.left prefixData.right)
  · intro data
    cases data with
    | intro prefixCarrier rest =>
        cases rest with
        | intro suffixCarrier witness =>
            have prefixedWitness : CompactNetWitness (append p center) precision (append p net) :=
              CompactNetWitness_prefix_iff.mpr (And.intro prefixCarrier witness)
            exact CompactNetWitness_suffix_iff.mpr (And.intro suffixCarrier prefixedWitness)

end BEDC.Derived.CompactUp
