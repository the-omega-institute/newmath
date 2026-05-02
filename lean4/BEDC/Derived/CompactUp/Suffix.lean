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

theorem CompactNetWitness_empty_precision_visible_context_iff {p q center net : BHist} :
    CompactNetWitness (append p center) (append BHist.Empty q)
      (append (append p net) q) ↔
      UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory center ∧ hsame net center := by
  constructor
  · intro witness
    have visibleData :=
      (CompactNetWitness_visible_context_iff (p := p) (q := q) (center := center)
        (precision := BHist.Empty) (net := net)).mp witness
    have central : CompactNetWitness center BHist.Empty net := visibleData.2.2
    exact
      And.intro visibleData.1
        (And.intro visibleData.2.1
          (And.intro central.1 (cont_right_unit_iff.mp central.2.2.2)))
  · intro data
    cases data with
    | intro prefixCarrier rest =>
        cases rest with
        | intro suffixCarrier rest =>
            cases rest with
            | intro centerCarrier sameNet =>
                have central : CompactNetWitness center BHist.Empty net :=
                  And.intro centerCarrier
                    (And.intro unary_empty
                      (And.intro (unary_transport centerCarrier (hsame_symm sameNet))
                        (cont_right_unit_iff.mpr sameNet)))
                exact
                  (CompactNetWitness_visible_context_iff (p := p) (q := q)
                    (center := center) (precision := BHist.Empty) (net := net)).mpr
                    (And.intro prefixCarrier (And.intro suffixCarrier central))

theorem CompactNetWitness_visible_context_result_deterministic
    {p q center precision net net' : BHist} :
    CompactNetWitness (append p center) (append precision q) (append (append p net) q) ->
      CompactNetWitness (append p center) (append precision q) (append (append p net') q) ->
        hsame net net' := by
  intro left right
  have leftData :=
    (CompactNetWitness_visible_context_iff (p := p) (q := q) (center := center)
      (precision := precision) (net := net)).mp left
  have rightData :=
    (CompactNetWitness_visible_context_iff (p := p) (q := q) (center := center)
      (precision := precision) (net := net')).mp right
  have leftWitness : CompactNetWitness center precision net := leftData.right.right
  have rightWitness : CompactNetWitness center precision net' := rightData.right.right
  exact cont_deterministic leftWitness.right.right.right rightWitness.right.right.right

theorem CompactNetWitness_visible_context_precision_deterministic
    {p q center precision precision' net : BHist} :
    CompactNetWitness (append p center) (append precision q) (append (append p net) q) ->
      CompactNetWitness (append p center) (append precision' q) (append (append p net) q) ->
        hsame precision precision' := by
  intro left right
  have leftData :=
    (CompactNetWitness_visible_context_iff (p := p) (q := q) (center := center)
      (precision := precision) (net := net)).mp left
  have rightData :=
    (CompactNetWitness_visible_context_iff (p := p) (q := q) (center := center)
      (precision := precision') (net := net)).mp right
  have leftWitness : CompactNetWitness center precision net := leftData.right.right
  have rightWitness : CompactNetWitness center precision' net := rightData.right.right
  exact cont_left_cancel leftWitness.right.right.right rightWitness.right.right.right

theorem CompactNetWitness_visible_context_center_deterministic
    {p q center center' precision net : BHist} :
    CompactNetWitness (append p center) (append precision q) (append (append p net) q) ->
      CompactNetWitness (append p center') (append precision q) (append (append p net) q) ->
        hsame center center' := by
  intro left right
  have leftData :=
    (CompactNetWitness_visible_context_iff (p := p) (q := q) (center := center)
      (precision := precision) (net := net)).mp left
  have rightData :=
    (CompactNetWitness_visible_context_iff (p := p) (q := q) (center := center')
      (precision := precision) (net := net)).mp right
  have leftWitness : CompactNetWitness center precision net := leftData.right.right
  have rightWitness : CompactNetWitness center' precision net := rightData.right.right
  exact cont_right_cancel leftWitness.right.right.right rightWitness.right.right.right

end BEDC.Derived.CompactUp
