import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EdelsteinContractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EdelsteinContractionUp : Type where
  | mk (X K F O D S H C P N : BHist) : EdelsteinContractionUp
  deriving DecidableEq

def edelsteinContractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: edelsteinContractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: edelsteinContractionEncodeBHist h

def edelsteinContractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (edelsteinContractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (edelsteinContractionDecodeBHist tail)

private theorem EdelsteinContractionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, edelsteinContractionDecodeBHist (edelsteinContractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def edelsteinContractionFields : EdelsteinContractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EdelsteinContractionUp.mk X K F O D S H C P N => [X, K, F, O, D, S, H, C, P, N]

def edelsteinContractionToEventFlow : EdelsteinContractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EdelsteinContractionUp.mk X K F O D S H C P N =>
      [edelsteinContractionEncodeBHist X,
        edelsteinContractionEncodeBHist K,
        edelsteinContractionEncodeBHist F,
        edelsteinContractionEncodeBHist O,
        edelsteinContractionEncodeBHist D,
        edelsteinContractionEncodeBHist S,
        edelsteinContractionEncodeBHist H,
        edelsteinContractionEncodeBHist C,
        edelsteinContractionEncodeBHist P,
        edelsteinContractionEncodeBHist N]

def edelsteinContractionFromEventFlow : EventFlow → Option EdelsteinContractionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: restK =>
      match restK with
      | [] => none
      | K :: restF =>
          match restF with
          | [] => none
          | F :: restO =>
              match restO with
              | [] => none
              | O :: restD =>
                  match restD with
                  | [] => none
                  | D :: restS =>
                      match restS with
                      | [] => none
                      | S :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (EdelsteinContractionUp.mk
                                                  (edelsteinContractionDecodeBHist X)
                                                  (edelsteinContractionDecodeBHist K)
                                                  (edelsteinContractionDecodeBHist F)
                                                  (edelsteinContractionDecodeBHist O)
                                                  (edelsteinContractionDecodeBHist D)
                                                  (edelsteinContractionDecodeBHist S)
                                                  (edelsteinContractionDecodeBHist H)
                                                  (edelsteinContractionDecodeBHist C)
                                                  (edelsteinContractionDecodeBHist P)
                                                  (edelsteinContractionDecodeBHist N))
                                          | _ :: _ => none

private theorem EdelsteinContractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EdelsteinContractionUp,
      edelsteinContractionFromEventFlow (edelsteinContractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X K F O D S H C P N =>
      change
        some
          (EdelsteinContractionUp.mk
            (edelsteinContractionDecodeBHist (edelsteinContractionEncodeBHist X))
            (edelsteinContractionDecodeBHist (edelsteinContractionEncodeBHist K))
            (edelsteinContractionDecodeBHist (edelsteinContractionEncodeBHist F))
            (edelsteinContractionDecodeBHist (edelsteinContractionEncodeBHist O))
            (edelsteinContractionDecodeBHist (edelsteinContractionEncodeBHist D))
            (edelsteinContractionDecodeBHist (edelsteinContractionEncodeBHist S))
            (edelsteinContractionDecodeBHist (edelsteinContractionEncodeBHist H))
            (edelsteinContractionDecodeBHist (edelsteinContractionEncodeBHist C))
            (edelsteinContractionDecodeBHist (edelsteinContractionEncodeBHist P))
            (edelsteinContractionDecodeBHist (edelsteinContractionEncodeBHist N))) =
          some (EdelsteinContractionUp.mk X K F O D S H C P N)
      rw [EdelsteinContractionTasteGate_single_carrier_alignment_decode_encode X,
        EdelsteinContractionTasteGate_single_carrier_alignment_decode_encode K,
        EdelsteinContractionTasteGate_single_carrier_alignment_decode_encode F,
        EdelsteinContractionTasteGate_single_carrier_alignment_decode_encode O,
        EdelsteinContractionTasteGate_single_carrier_alignment_decode_encode D,
        EdelsteinContractionTasteGate_single_carrier_alignment_decode_encode S,
        EdelsteinContractionTasteGate_single_carrier_alignment_decode_encode H,
        EdelsteinContractionTasteGate_single_carrier_alignment_decode_encode C,
        EdelsteinContractionTasteGate_single_carrier_alignment_decode_encode P,
        EdelsteinContractionTasteGate_single_carrier_alignment_decode_encode N]

private theorem edelsteinContractionToEventFlow_injective {x y : EdelsteinContractionUp} :
    edelsteinContractionToEventFlow x = edelsteinContractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      edelsteinContractionFromEventFlow (edelsteinContractionToEventFlow x) =
        edelsteinContractionFromEventFlow (edelsteinContractionToEventFlow y) :=
    congrArg edelsteinContractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EdelsteinContractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EdelsteinContractionTasteGate_single_carrier_alignment_round_trip y)))

instance edelsteinContractionBHistCarrier : BHistCarrier EdelsteinContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := edelsteinContractionToEventFlow
  fromEventFlow := edelsteinContractionFromEventFlow

instance edelsteinContractionChapterTasteGate : ChapterTasteGate EdelsteinContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change edelsteinContractionFromEventFlow (edelsteinContractionToEventFlow x) = some x
    exact EdelsteinContractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (edelsteinContractionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate EdelsteinContractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  edelsteinContractionChapterTasteGate

theorem EdelsteinContractionTasteGate_single_carrier_alignment :
    (∀ x : EdelsteinContractionUp,
        edelsteinContractionFromEventFlow (edelsteinContractionToEventFlow x) = some x) ∧
      (∀ x y : EdelsteinContractionUp,
        edelsteinContractionToEventFlow x = edelsteinContractionToEventFlow y → x = y) ∧
        edelsteinContractionFields
            (EdelsteinContractionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨EdelsteinContractionTasteGate_single_carrier_alignment_round_trip,
      ⟨fun _ _ heq => edelsteinContractionToEventFlow_injective heq, rfl⟩⟩

end BEDC.Derived.EdelsteinContractionUp
