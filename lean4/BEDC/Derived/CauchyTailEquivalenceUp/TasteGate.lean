import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailEquivalenceUp : Type where
  | mk (X Y W M D T H C P N : BHist) : CauchyTailEquivalenceUp
  deriving DecidableEq

def cauchyTailEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailEquivalenceEncodeBHist h

def cauchyTailEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailEquivalenceDecodeBHist tail)

private theorem CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyTailEquivalenceToEventFlow : CauchyTailEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailEquivalenceUp.mk X Y W M D T H C P N =>
      [cauchyTailEquivalenceEncodeBHist X, cauchyTailEquivalenceEncodeBHist Y,
        cauchyTailEquivalenceEncodeBHist W, cauchyTailEquivalenceEncodeBHist M,
        cauchyTailEquivalenceEncodeBHist D, cauchyTailEquivalenceEncodeBHist T,
        cauchyTailEquivalenceEncodeBHist H, cauchyTailEquivalenceEncodeBHist C,
        cauchyTailEquivalenceEncodeBHist P, cauchyTailEquivalenceEncodeBHist N]

def cauchyTailEquivalenceFromEventFlow : EventFlow → Option CauchyTailEquivalenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: rest =>
      match rest with
      | [] => none
      | Y :: rest =>
          match rest with
          | [] => none
          | W :: rest =>
              match rest with
              | [] => none
              | M :: rest =>
                  match rest with
                  | [] => none
                  | D :: rest =>
                      match rest with
                      | [] => none
                      | T :: rest =>
                          match rest with
                          | [] => none
                          | H :: rest =>
                              match rest with
                              | [] => none
                              | C :: rest =>
                                  match rest with
                                  | [] => none
                                  | P :: rest =>
                                      match rest with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (CauchyTailEquivalenceUp.mk
                                                  (cauchyTailEquivalenceDecodeBHist X)
                                                  (cauchyTailEquivalenceDecodeBHist Y)
                                                  (cauchyTailEquivalenceDecodeBHist W)
                                                  (cauchyTailEquivalenceDecodeBHist M)
                                                  (cauchyTailEquivalenceDecodeBHist D)
                                                  (cauchyTailEquivalenceDecodeBHist T)
                                                  (cauchyTailEquivalenceDecodeBHist H)
                                                  (cauchyTailEquivalenceDecodeBHist C)
                                                  (cauchyTailEquivalenceDecodeBHist P)
                                                  (cauchyTailEquivalenceDecodeBHist N))
                                          | _ :: _ => none
  | [] => none

private theorem CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyTailEquivalenceUp,
      cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y W M D T H C P N =>
      change
        some
          (CauchyTailEquivalenceUp.mk
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist X))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist Y))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist W))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist M))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist D))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist T))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist H))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist C))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist P))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist N))) =
          some (CauchyTailEquivalenceUp.mk X Y W M D T H C P N)
      rw [CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_decode_encode X,
        CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_decode_encode Y,
        CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_decode_encode W,
        CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_decode_encode M,
        CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_decode_encode D,
        CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_decode_encode T,
        CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_decode_encode H,
        CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_decode_encode C,
        CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_decode_encode P,
        CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyTailEquivalenceUp} :
    cauchyTailEquivalenceToEventFlow x = cauchyTailEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow x) =
        cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow y) :=
    congrArg cauchyTailEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyTailEquivalenceBHistCarrier : BHistCarrier CauchyTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailEquivalenceToEventFlow
  fromEventFlow := cauchyTailEquivalenceFromEventFlow

instance cauchyTailEquivalenceChapterTasteGate :
    ChapterTasteGate CauchyTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow x) = some x
    exact CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyTailEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailEquivalenceChapterTasteGate

theorem CauchyTailEquivalenceUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist h) = h) ∧
      (∀ x : CauchyTailEquivalenceUp,
        cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow x) = some x) ∧
      (∀ x y : CauchyTailEquivalenceUp,
        cauchyTailEquivalenceToEventFlow x = cauchyTailEquivalenceToEventFlow y → x = y) ∧
      cauchyTailEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_decode_encode,
      CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        CauchyTailEquivalenceUpTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyTailEquivalenceUp
