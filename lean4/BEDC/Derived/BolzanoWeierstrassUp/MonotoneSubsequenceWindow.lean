import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BolzanoWeierstrassMonotoneSubsequenceWindow : Type where
  | mk (K R Q H C P N : BHist) : BolzanoWeierstrassMonotoneSubsequenceWindow
  deriving DecidableEq

def bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist h

def bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist tail)

private theorem
    BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist
        (bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bolzanoWeierstrassMonotoneSubsequenceWindowToEventFlow :
    BolzanoWeierstrassMonotoneSubsequenceWindow → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BolzanoWeierstrassMonotoneSubsequenceWindow.mk K R Q H C P N =>
      [bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist K,
        bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist R,
        bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist Q,
        bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist H,
        bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist C,
        bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist P,
        bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist N]

def bolzanoWeierstrassMonotoneSubsequenceWindowFromEventFlow :
    EventFlow → Option BolzanoWeierstrassMonotoneSubsequenceWindow
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: restK =>
      match restK with
      | [] => none
      | R :: restR =>
          match restR with
          | [] => none
          | Q :: restQ =>
              match restQ with
              | [] => none
              | H :: restH =>
                  match restH with
                  | [] => none
                  | C :: restC =>
                      match restC with
                      | [] => none
                      | P :: restP =>
                          match restP with
                          | [] => none
                          | N :: restN =>
                              match restN with
                              | [] =>
                                  some
                                    (BolzanoWeierstrassMonotoneSubsequenceWindow.mk
                                      (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist K)
                                      (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist R)
                                      (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist Q)
                                      (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist H)
                                      (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist C)
                                      (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist P)
                                      (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist N))
                              | _ :: _ => none

private theorem
    BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_round_trip :
    ∀ x : BolzanoWeierstrassMonotoneSubsequenceWindow,
      bolzanoWeierstrassMonotoneSubsequenceWindowFromEventFlow
        (bolzanoWeierstrassMonotoneSubsequenceWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K R Q H C P N =>
      change
        some
          (BolzanoWeierstrassMonotoneSubsequenceWindow.mk
            (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist
              (bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist K))
            (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist
              (bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist R))
            (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist
              (bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist Q))
            (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist
              (bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist H))
            (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist
              (bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist C))
            (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist
              (bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist P))
            (bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist
              (bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist N))) =
          some (BolzanoWeierstrassMonotoneSubsequenceWindow.mk K R Q H C P N)
      rw [BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_decode_encode K,
        BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_decode_encode R,
        BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_decode_encode Q,
        BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_decode_encode H,
        BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_decode_encode C,
        BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_decode_encode P,
        BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_decode_encode N]

private theorem
    BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_injective
    {x y : BolzanoWeierstrassMonotoneSubsequenceWindow} :
    bolzanoWeierstrassMonotoneSubsequenceWindowToEventFlow x =
      bolzanoWeierstrassMonotoneSubsequenceWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bolzanoWeierstrassMonotoneSubsequenceWindowFromEventFlow
          (bolzanoWeierstrassMonotoneSubsequenceWindowToEventFlow x) =
        bolzanoWeierstrassMonotoneSubsequenceWindowFromEventFlow
          (bolzanoWeierstrassMonotoneSubsequenceWindowToEventFlow y) :=
    congrArg bolzanoWeierstrassMonotoneSubsequenceWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_round_trip y)))

instance bolzanoWeierstrassMonotoneSubsequenceWindowBHistCarrier :
    BHistCarrier BolzanoWeierstrassMonotoneSubsequenceWindow where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bolzanoWeierstrassMonotoneSubsequenceWindowToEventFlow
  fromEventFlow := bolzanoWeierstrassMonotoneSubsequenceWindowFromEventFlow

instance bolzanoWeierstrassMonotoneSubsequenceWindowChapterTasteGate :
    ChapterTasteGate BolzanoWeierstrassMonotoneSubsequenceWindow where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bolzanoWeierstrassMonotoneSubsequenceWindowFromEventFlow
        (bolzanoWeierstrassMonotoneSubsequenceWindowToEventFlow x) = some x
    exact BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_injective heq)

theorem BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment :
    (forall h : BHist,
      bolzanoWeierstrassMonotoneSubsequenceWindowDecodeBHist
        (bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BolzanoWeierstrassMonotoneSubsequenceWindow) ∧
        Nonempty (ChapterTasteGate BolzanoWeierstrassMonotoneSubsequenceWindow) ∧
          bolzanoWeierstrassMonotoneSubsequenceWindowEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BolzanoWeierstrassMonotoneSubsequenceWindow_single_carrier_alignment_decode_encode,
      ⟨bolzanoWeierstrassMonotoneSubsequenceWindowBHistCarrier⟩,
      ⟨bolzanoWeierstrassMonotoneSubsequenceWindowChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BolzanoWeierstrassUp
