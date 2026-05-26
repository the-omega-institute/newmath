import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DecimalNormalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DecimalNormalityUp : Type where
  | mk (D W F R E H C P N : BHist) : DecimalNormalityUp
  deriving DecidableEq

def decimalNormalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: decimalNormalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: decimalNormalityEncodeBHist h

def decimalNormalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decimalNormalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decimalNormalityDecodeBHist tail)

private theorem DecimalNormalityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, decimalNormalityDecodeBHist (decimalNormalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def decimalNormalityFields : DecimalNormalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DecimalNormalityUp.mk D W F R E H C P N => [D, W, F, R, E, H, C, P, N]

def decimalNormalityToEventFlow : DecimalNormalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map decimalNormalityEncodeBHist (decimalNormalityFields x)

def decimalNormalityFromEventFlow : EventFlow → Option DecimalNormalityUp
  -- BEDC touchpoint anchor: BHist BMark
  | D :: restD =>
      match restD with
      | W :: restW =>
          match restW with
          | F :: restF =>
              match restF with
              | R :: restR =>
                  match restR with
                  | E :: restE =>
                      match restE with
                      | H :: restH =>
                          match restH with
                          | C :: restC =>
                              match restC with
                              | P :: restP =>
                                  match restP with
                                  | N :: restN =>
                                      match restN with
                                      | [] =>
                                          some
                                            (DecimalNormalityUp.mk
                                              (decimalNormalityDecodeBHist D)
                                              (decimalNormalityDecodeBHist W)
                                              (decimalNormalityDecodeBHist F)
                                              (decimalNormalityDecodeBHist R)
                                              (decimalNormalityDecodeBHist E)
                                              (decimalNormalityDecodeBHist H)
                                              (decimalNormalityDecodeBHist C)
                                              (decimalNormalityDecodeBHist P)
                                              (decimalNormalityDecodeBHist N))
                                      | _ :: _ => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem DecimalNormalityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DecimalNormalityUp,
      decimalNormalityFromEventFlow (decimalNormalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W F R E H C P N =>
      change
        some
          (DecimalNormalityUp.mk
            (decimalNormalityDecodeBHist (decimalNormalityEncodeBHist D))
            (decimalNormalityDecodeBHist (decimalNormalityEncodeBHist W))
            (decimalNormalityDecodeBHist (decimalNormalityEncodeBHist F))
            (decimalNormalityDecodeBHist (decimalNormalityEncodeBHist R))
            (decimalNormalityDecodeBHist (decimalNormalityEncodeBHist E))
            (decimalNormalityDecodeBHist (decimalNormalityEncodeBHist H))
            (decimalNormalityDecodeBHist (decimalNormalityEncodeBHist C))
            (decimalNormalityDecodeBHist (decimalNormalityEncodeBHist P))
            (decimalNormalityDecodeBHist (decimalNormalityEncodeBHist N))) =
          some (DecimalNormalityUp.mk D W F R E H C P N)
      rw [DecimalNormalityTasteGate_single_carrier_alignment_decode D,
        DecimalNormalityTasteGate_single_carrier_alignment_decode W,
        DecimalNormalityTasteGate_single_carrier_alignment_decode F,
        DecimalNormalityTasteGate_single_carrier_alignment_decode R,
        DecimalNormalityTasteGate_single_carrier_alignment_decode E,
        DecimalNormalityTasteGate_single_carrier_alignment_decode H,
        DecimalNormalityTasteGate_single_carrier_alignment_decode C,
        DecimalNormalityTasteGate_single_carrier_alignment_decode P,
        DecimalNormalityTasteGate_single_carrier_alignment_decode N]

private theorem DecimalNormalityTasteGate_single_carrier_alignment_injective
    {x y : DecimalNormalityUp} :
    decimalNormalityToEventFlow x = decimalNormalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      decimalNormalityFromEventFlow (decimalNormalityToEventFlow x) =
        decimalNormalityFromEventFlow (decimalNormalityToEventFlow y) :=
    congrArg decimalNormalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DecimalNormalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DecimalNormalityTasteGate_single_carrier_alignment_round_trip y)))

instance decimalNormalityBHistCarrier : BHistCarrier DecimalNormalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := decimalNormalityToEventFlow
  fromEventFlow := decimalNormalityFromEventFlow

instance decimalNormalityChapterTasteGate : ChapterTasteGate DecimalNormalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change decimalNormalityFromEventFlow (decimalNormalityToEventFlow x) = some x
    exact DecimalNormalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DecimalNormalityTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate DecimalNormalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  decimalNormalityChapterTasteGate

theorem DecimalNormalityTasteGate_single_carrier_alignment :
    (∀ h : BHist, decimalNormalityDecodeBHist (decimalNormalityEncodeBHist h) = h) ∧
      (∀ x : DecimalNormalityUp,
        decimalNormalityFromEventFlow (decimalNormalityToEventFlow x) = some x) ∧
        (∀ x y : DecimalNormalityUp,
          decimalNormalityToEventFlow x = decimalNormalityToEventFlow y → x = y) ∧
          decimalNormalityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DecimalNormalityTasteGate_single_carrier_alignment_decode,
      DecimalNormalityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ h => DecimalNormalityTasteGate_single_carrier_alignment_injective h),
      rfl⟩

end BEDC.Derived.DecimalNormalityUp
