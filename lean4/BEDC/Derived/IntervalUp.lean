import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.IntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def IntervalCarrier (lower upper : BHist → Prop) (h : BHist) : Prop :=
  UnaryHistory h ∧ lower h ∧ upper h

def IntervalClassifierSpec (lower upper : BHist → Prop) (h k : BHist) : Prop :=
  IntervalCarrier lower upper h ∧ IntervalCarrier lower upper k ∧ hsame h k

theorem IntervalCarrier_empty_boundary_of_hsame {h : BEDC.FKernel.Hist.BHist} :
    BEDC.FKernel.Hist.hsame h BEDC.FKernel.Hist.BHist.Empty ->
      IntervalCarrier
        (fun x : BEDC.FKernel.Hist.BHist =>
          BEDC.FKernel.Hist.hsame BEDC.FKernel.Hist.BHist.Empty x)
        (fun x : BEDC.FKernel.Hist.BHist =>
          BEDC.FKernel.Hist.hsame x BEDC.FKernel.Hist.BHist.Empty)
        h := by
  intro sameEmpty
  constructor
  · exact unary_transport unary_empty (BEDC.FKernel.Hist.hsame_symm sameEmpty)
  · constructor
    · exact BEDC.FKernel.Hist.hsame_symm sameEmpty
    · exact sameEmpty

theorem IntervalCarrier_empty_boundary_hsame_transport {h k : BEDC.FKernel.Hist.BHist} :
    BEDC.FKernel.Hist.hsame h k ->
      IntervalCarrier
        (fun x => BEDC.FKernel.Hist.hsame BEDC.FKernel.Hist.BHist.Empty x)
        (fun x => BEDC.FKernel.Hist.hsame x BEDC.FKernel.Hist.BHist.Empty)
        h ->
      IntervalCarrier
        (fun x => BEDC.FKernel.Hist.hsame BEDC.FKernel.Hist.BHist.Empty x)
        (fun x => BEDC.FKernel.Hist.hsame x BEDC.FKernel.Hist.BHist.Empty)
        k := by
  intro same carrier
  cases carrier with
  | intro hUnary boundary =>
      cases boundary with
      | intro lower upper =>
          constructor
          · exact BEDC.FKernel.Unary.unary_transport hUnary same
          · constructor
            · exact BEDC.FKernel.Hist.hsame_trans lower same
            · exact BEDC.FKernel.Hist.hsame_trans (BEDC.FKernel.Hist.hsame_symm same) upper

theorem IntervalClassifierSpec_empty_boundary_of_hsame {h k : BHist} :
    hsame h BHist.Empty -> hsame k BHist.Empty ->
      IntervalClassifierSpec
        (fun x : BHist => hsame BHist.Empty x)
        (fun x : BHist => hsame x BHist.Empty) h k := by
  intro hEmpty kEmpty
  constructor
  · exact IntervalCarrier_empty_boundary_of_hsame hEmpty
  · constructor
    · exact IntervalCarrier_empty_boundary_of_hsame kEmpty
    · exact hsame_trans hEmpty (hsame_symm kEmpty)

theorem IntervalClassifierSpec_empty_boundary_iff {h k : BHist} :
    IntervalClassifierSpec
      (fun x : BHist => hsame BHist.Empty x)
      (fun x : BHist => hsame x BHist.Empty) h k <->
        hsame h BHist.Empty /\ hsame k BHist.Empty := by
  constructor
  · intro classifier
    cases classifier with
    | intro hCarrier rest =>
        cases rest with
        | intro kCarrier _ =>
            constructor
            · exact hCarrier.right.right
            · exact kCarrier.right.right
  · intro boundaries
    cases boundaries with
    | intro hEmpty kEmpty =>
        exact IntervalClassifierSpec_empty_boundary_of_hsame hEmpty kEmpty

theorem IntervalClassifierSpec_empty_boundary_iff_endpoints {h k : BHist} :
    IntervalClassifierSpec
      (fun x : BHist => hsame BHist.Empty x)
      (fun x : BHist => hsame x BHist.Empty) h k ↔
      hsame h BHist.Empty ∧ hsame k BHist.Empty := by
  constructor
  · intro classifier
    cases classifier with
    | intro carrierH rest =>
        cases rest with
        | intro carrierK _ =>
            exact And.intro carrierH.right.right carrierK.right.right
  · intro endpoints
    exact IntervalClassifierSpec_empty_boundary_of_hsame endpoints.left endpoints.right

theorem IntervalClassifierSpec_trans {lower upper : BEDC.FKernel.Hist.BHist -> Prop}
    {h k r : BEDC.FKernel.Hist.BHist} :
    IntervalClassifierSpec lower upper h k ->
      IntervalClassifierSpec lower upper k r ->
        IntervalClassifierSpec lower upper h r := by
  intro left right
  cases left with
  | intro carrierH leftRest =>
      cases leftRest with
      | intro _ sameHK =>
          cases right with
          | intro _ rightRest =>
              cases rightRest with
              | intro carrierR sameKR =>
                  constructor
                  · exact carrierH
                  · constructor
                    · exact carrierR
                    · exact BEDC.FKernel.Hist.hsame_trans sameHK sameKR

theorem interval_name_certificate (lower upper : BHist → Prop)
    (lower_empty : lower BHist.Empty) (upper_empty : upper BHist.Empty)
    (lower_transport : ∀ {h k : BHist}, hsame h k → lower h → lower k)
    (upper_transport : ∀ {h k : BHist}, hsame h k → upper h → upper k) :
    NameCert (IntervalCarrier lower upper) (IntervalClassifierSpec lower upper) ∧
      (∀ {h k : BHist}, hsame h k → IntervalCarrier lower upper h →
        IntervalCarrier lower upper k) := by
  constructor
  · constructor
    · exact ⟨BHist.Empty, unary_empty, lower_empty, upper_empty⟩
    · intro h carrier
      exact ⟨carrier, carrier, hsame_refl h⟩
    · intro h k same
      exact ⟨same.right.left, same.left, hsame_symm same.right.right⟩
    · intro h k r hk kr
      exact ⟨hk.left, kr.right.left, hsame_trans hk.right.right kr.right.right⟩
    · intro h k same carrier
      exact ⟨unary_transport carrier.left same.right.right,
        lower_transport same.right.right carrier.right.left,
        upper_transport same.right.right carrier.right.right⟩
  · intro h k same carrier
    exact ⟨unary_transport carrier.left same,
      lower_transport same carrier.right.left,
      upper_transport same carrier.right.right⟩

end BEDC.Derived.IntervalUp
