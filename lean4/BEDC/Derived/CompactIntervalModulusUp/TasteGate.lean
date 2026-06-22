import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactIntervalModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactIntervalModulusUp : Type where
  | mk (I K F T W R E H C P N : BHist) : CompactIntervalModulusUp
  deriving DecidableEq

def compactIntervalModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactIntervalModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactIntervalModulusEncodeBHist h

def compactIntervalModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactIntervalModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactIntervalModulusDecodeBHist tail)

private theorem CompactIntervalModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, compactIntervalModulusDecodeBHist (compactIntervalModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactIntervalModulusFields : CompactIntervalModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactIntervalModulusUp.mk I K F T W R E H C P N => [I, K, F, T, W, R, E, H, C, P, N]

def compactIntervalModulusToEventFlow : CompactIntervalModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactIntervalModulusUp.mk I K F T W R E H C P N =>
      [compactIntervalModulusEncodeBHist I,
        compactIntervalModulusEncodeBHist K,
        compactIntervalModulusEncodeBHist F,
        compactIntervalModulusEncodeBHist T,
        compactIntervalModulusEncodeBHist W,
        compactIntervalModulusEncodeBHist R,
        compactIntervalModulusEncodeBHist E,
        compactIntervalModulusEncodeBHist H,
        compactIntervalModulusEncodeBHist C,
        compactIntervalModulusEncodeBHist P,
        compactIntervalModulusEncodeBHist N]

def compactIntervalModulusFromEventFlow : EventFlow → Option CompactIntervalModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: restK =>
      match restK with
      | [] => none
      | K :: restF =>
          match restF with
          | [] => none
          | F :: restT =>
              match restT with
              | [] => none
              | T :: restW =>
                  match restW with
                  | [] => none
                  | W :: restR =>
                      match restR with
                      | [] => none
                      | R :: restE =>
                          match restE with
                          | [] => none
                          | E :: restH =>
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
                                                    (CompactIntervalModulusUp.mk
                                                      (compactIntervalModulusDecodeBHist I)
                                                      (compactIntervalModulusDecodeBHist K)
                                                      (compactIntervalModulusDecodeBHist F)
                                                      (compactIntervalModulusDecodeBHist T)
                                                      (compactIntervalModulusDecodeBHist W)
                                                      (compactIntervalModulusDecodeBHist R)
                                                      (compactIntervalModulusDecodeBHist E)
                                                      (compactIntervalModulusDecodeBHist H)
                                                      (compactIntervalModulusDecodeBHist C)
                                                      (compactIntervalModulusDecodeBHist P)
                                                      (compactIntervalModulusDecodeBHist N))
                                              | _ :: _ => none

private theorem CompactIntervalModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactIntervalModulusUp,
      compactIntervalModulusFromEventFlow (compactIntervalModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I K F T W R E H C P N =>
      change
        some
          (CompactIntervalModulusUp.mk
            (compactIntervalModulusDecodeBHist (compactIntervalModulusEncodeBHist I))
            (compactIntervalModulusDecodeBHist (compactIntervalModulusEncodeBHist K))
            (compactIntervalModulusDecodeBHist (compactIntervalModulusEncodeBHist F))
            (compactIntervalModulusDecodeBHist (compactIntervalModulusEncodeBHist T))
            (compactIntervalModulusDecodeBHist (compactIntervalModulusEncodeBHist W))
            (compactIntervalModulusDecodeBHist (compactIntervalModulusEncodeBHist R))
            (compactIntervalModulusDecodeBHist (compactIntervalModulusEncodeBHist E))
            (compactIntervalModulusDecodeBHist (compactIntervalModulusEncodeBHist H))
            (compactIntervalModulusDecodeBHist (compactIntervalModulusEncodeBHist C))
            (compactIntervalModulusDecodeBHist (compactIntervalModulusEncodeBHist P))
            (compactIntervalModulusDecodeBHist (compactIntervalModulusEncodeBHist N))) =
          some (CompactIntervalModulusUp.mk I K F T W R E H C P N)
      rw [CompactIntervalModulusTasteGate_single_carrier_alignment_decode_encode I,
        CompactIntervalModulusTasteGate_single_carrier_alignment_decode_encode K,
        CompactIntervalModulusTasteGate_single_carrier_alignment_decode_encode F,
        CompactIntervalModulusTasteGate_single_carrier_alignment_decode_encode T,
        CompactIntervalModulusTasteGate_single_carrier_alignment_decode_encode W,
        CompactIntervalModulusTasteGate_single_carrier_alignment_decode_encode R,
        CompactIntervalModulusTasteGate_single_carrier_alignment_decode_encode E,
        CompactIntervalModulusTasteGate_single_carrier_alignment_decode_encode H,
        CompactIntervalModulusTasteGate_single_carrier_alignment_decode_encode C,
        CompactIntervalModulusTasteGate_single_carrier_alignment_decode_encode P,
        CompactIntervalModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem compactIntervalModulusToEventFlow_injective {x y : CompactIntervalModulusUp} :
    compactIntervalModulusToEventFlow x = compactIntervalModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactIntervalModulusFromEventFlow (compactIntervalModulusToEventFlow x) =
        compactIntervalModulusFromEventFlow (compactIntervalModulusToEventFlow y) :=
    congrArg compactIntervalModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactIntervalModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompactIntervalModulusTasteGate_single_carrier_alignment_round_trip y)))

instance compactIntervalModulusBHistCarrier : BHistCarrier CompactIntervalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactIntervalModulusToEventFlow
  fromEventFlow := compactIntervalModulusFromEventFlow

instance compactIntervalModulusChapterTasteGate : ChapterTasteGate CompactIntervalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactIntervalModulusFromEventFlow (compactIntervalModulusToEventFlow x) = some x
    exact CompactIntervalModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactIntervalModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactIntervalModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactIntervalModulusChapterTasteGate

theorem CompactIntervalModulusTasteGate_single_carrier_alignment :
    (∀ x : CompactIntervalModulusUp,
        compactIntervalModulusFromEventFlow (compactIntervalModulusToEventFlow x) = some x) ∧
      (∀ x y : CompactIntervalModulusUp,
        compactIntervalModulusToEventFlow x = compactIntervalModulusToEventFlow y → x = y) ∧
        compactIntervalModulusFields
            (CompactIntervalModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactIntervalModulusTasteGate_single_carrier_alignment_round_trip,
      ⟨fun _ _ heq => compactIntervalModulusToEventFlow_injective heq, rfl⟩⟩

end BEDC.Derived.CompactIntervalModulusUp
