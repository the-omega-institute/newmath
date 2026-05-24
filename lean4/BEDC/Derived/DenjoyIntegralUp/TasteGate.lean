import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DenjoyIntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DenjoyIntegralUp : Type where
  | mk (G I V R E H C P N : BHist) : DenjoyIntegralUp
  deriving DecidableEq

def denjoyIntegralEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: denjoyIntegralEncodeBHist h
  | BHist.e1 h => BMark.b1 :: denjoyIntegralEncodeBHist h

def denjoyIntegralDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (denjoyIntegralDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (denjoyIntegralDecodeBHist tail)

private theorem DenjoyIntegralTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, denjoyIntegralDecodeBHist (denjoyIntegralEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def denjoyIntegralFields : DenjoyIntegralUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DenjoyIntegralUp.mk G I V R E H C P N => [G, I, V, R, E, H, C, P, N]

def denjoyIntegralToEventFlow : DenjoyIntegralUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (denjoyIntegralFields x).map denjoyIntegralEncodeBHist

def denjoyIntegralFromEventFlow : EventFlow → Option DenjoyIntegralUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | G :: restG =>
      match restG with
      | [] => none
      | I :: restI =>
          match restI with
          | [] => none
          | V :: restV =>
              match restV with
              | [] => none
              | R :: restR =>
                  match restR with
                  | [] => none
                  | E :: restE =>
                      match restE with
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
                                            (DenjoyIntegralUp.mk
                                              (denjoyIntegralDecodeBHist G)
                                              (denjoyIntegralDecodeBHist I)
                                              (denjoyIntegralDecodeBHist V)
                                              (denjoyIntegralDecodeBHist R)
                                              (denjoyIntegralDecodeBHist E)
                                              (denjoyIntegralDecodeBHist H)
                                              (denjoyIntegralDecodeBHist C)
                                              (denjoyIntegralDecodeBHist P)
                                              (denjoyIntegralDecodeBHist N))
                                      | _ :: _ => none

private theorem DenjoyIntegralTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DenjoyIntegralUp,
      denjoyIntegralFromEventFlow (denjoyIntegralToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G I V R E H C P N =>
      change
        some
          (DenjoyIntegralUp.mk
            (denjoyIntegralDecodeBHist (denjoyIntegralEncodeBHist G))
            (denjoyIntegralDecodeBHist (denjoyIntegralEncodeBHist I))
            (denjoyIntegralDecodeBHist (denjoyIntegralEncodeBHist V))
            (denjoyIntegralDecodeBHist (denjoyIntegralEncodeBHist R))
            (denjoyIntegralDecodeBHist (denjoyIntegralEncodeBHist E))
            (denjoyIntegralDecodeBHist (denjoyIntegralEncodeBHist H))
            (denjoyIntegralDecodeBHist (denjoyIntegralEncodeBHist C))
            (denjoyIntegralDecodeBHist (denjoyIntegralEncodeBHist P))
            (denjoyIntegralDecodeBHist (denjoyIntegralEncodeBHist N))) =
          some (DenjoyIntegralUp.mk G I V R E H C P N)
      rw [DenjoyIntegralTasteGate_single_carrier_alignment_decode_encode G,
        DenjoyIntegralTasteGate_single_carrier_alignment_decode_encode I,
        DenjoyIntegralTasteGate_single_carrier_alignment_decode_encode V,
        DenjoyIntegralTasteGate_single_carrier_alignment_decode_encode R,
        DenjoyIntegralTasteGate_single_carrier_alignment_decode_encode E,
        DenjoyIntegralTasteGate_single_carrier_alignment_decode_encode H,
        DenjoyIntegralTasteGate_single_carrier_alignment_decode_encode C,
        DenjoyIntegralTasteGate_single_carrier_alignment_decode_encode P,
        DenjoyIntegralTasteGate_single_carrier_alignment_decode_encode N]

private theorem DenjoyIntegralTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DenjoyIntegralUp} :
    denjoyIntegralToEventFlow x = denjoyIntegralToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      denjoyIntegralFromEventFlow (denjoyIntegralToEventFlow x) =
        denjoyIntegralFromEventFlow (denjoyIntegralToEventFlow y) :=
    congrArg denjoyIntegralFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DenjoyIntegralTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DenjoyIntegralTasteGate_single_carrier_alignment_round_trip y)))

instance denjoyIntegralBHistCarrier : BHistCarrier DenjoyIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := denjoyIntegralToEventFlow
  fromEventFlow := denjoyIntegralFromEventFlow

instance denjoyIntegralChapterTasteGate : ChapterTasteGate DenjoyIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change denjoyIntegralFromEventFlow (denjoyIntegralToEventFlow x) = some x
    exact DenjoyIntegralTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DenjoyIntegralTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DenjoyIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  denjoyIntegralChapterTasteGate

theorem DenjoyIntegralTasteGate_single_carrier_alignment :
    (∀ h : BHist, denjoyIntegralDecodeBHist (denjoyIntegralEncodeBHist h) = h) ∧
      (∀ x : DenjoyIntegralUp,
        denjoyIntegralFromEventFlow (denjoyIntegralToEventFlow x) = some x) ∧
        (∀ x y : DenjoyIntegralUp,
          denjoyIntegralToEventFlow x = denjoyIntegralToEventFlow y → x = y) ∧
          denjoyIntegralEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DenjoyIntegralTasteGate_single_carrier_alignment_decode_encode,
      DenjoyIntegralTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => DenjoyIntegralTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.DenjoyIntegralUp
