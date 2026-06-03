import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GDeltaSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GDeltaSetUp : Type where
  | mk (P B S W O H C L N : BHist) : GDeltaSetUp
  deriving DecidableEq

def gDeltaSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gDeltaSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gDeltaSetEncodeBHist h

def gDeltaSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gDeltaSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gDeltaSetDecodeBHist tail)

private theorem GDeltaSetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, gDeltaSetDecodeBHist (gDeltaSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def gDeltaSetToEventFlow : GDeltaSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GDeltaSetUp.mk P B S W O H C L N =>
      [[BMark.b0],
        gDeltaSetEncodeBHist P,
        gDeltaSetEncodeBHist B,
        gDeltaSetEncodeBHist S,
        gDeltaSetEncodeBHist W,
        gDeltaSetEncodeBHist O,
        gDeltaSetEncodeBHist H,
        gDeltaSetEncodeBHist C,
        gDeltaSetEncodeBHist L,
        gDeltaSetEncodeBHist N]

def gDeltaSetFromEventFlow : EventFlow → Option GDeltaSetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest =>
      match rest with
      | [] => none
      | P :: rest =>
          match rest with
          | [] => none
          | B :: rest =>
              match rest with
              | [] => none
              | S :: rest =>
                  match rest with
                  | [] => none
                  | W :: rest =>
                      match rest with
                      | [] => none
                      | O :: rest =>
                          match rest with
                          | [] => none
                          | H :: rest =>
                              match rest with
                              | [] => none
                              | C :: rest =>
                                  match rest with
                                  | [] => none
                                  | L :: rest =>
                                      match rest with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (GDeltaSetUp.mk
                                                  (gDeltaSetDecodeBHist P)
                                                  (gDeltaSetDecodeBHist B)
                                                  (gDeltaSetDecodeBHist S)
                                                  (gDeltaSetDecodeBHist W)
                                                  (gDeltaSetDecodeBHist O)
                                                  (gDeltaSetDecodeBHist H)
                                                  (gDeltaSetDecodeBHist C)
                                                  (gDeltaSetDecodeBHist L)
                                                  (gDeltaSetDecodeBHist N))
                                          | _ :: _ => none

private theorem GDeltaSetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : GDeltaSetUp,
      gDeltaSetFromEventFlow (gDeltaSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P B S W O H C L N =>
      change
        some
          (GDeltaSetUp.mk
            (gDeltaSetDecodeBHist (gDeltaSetEncodeBHist P))
            (gDeltaSetDecodeBHist (gDeltaSetEncodeBHist B))
            (gDeltaSetDecodeBHist (gDeltaSetEncodeBHist S))
            (gDeltaSetDecodeBHist (gDeltaSetEncodeBHist W))
            (gDeltaSetDecodeBHist (gDeltaSetEncodeBHist O))
            (gDeltaSetDecodeBHist (gDeltaSetEncodeBHist H))
            (gDeltaSetDecodeBHist (gDeltaSetEncodeBHist C))
            (gDeltaSetDecodeBHist (gDeltaSetEncodeBHist L))
            (gDeltaSetDecodeBHist (gDeltaSetEncodeBHist N))) =
          some (GDeltaSetUp.mk P B S W O H C L N)
      rw [GDeltaSetTasteGate_single_carrier_alignment_decode_encode P,
        GDeltaSetTasteGate_single_carrier_alignment_decode_encode B,
        GDeltaSetTasteGate_single_carrier_alignment_decode_encode S,
        GDeltaSetTasteGate_single_carrier_alignment_decode_encode W,
        GDeltaSetTasteGate_single_carrier_alignment_decode_encode O,
        GDeltaSetTasteGate_single_carrier_alignment_decode_encode H,
        GDeltaSetTasteGate_single_carrier_alignment_decode_encode C,
        GDeltaSetTasteGate_single_carrier_alignment_decode_encode L,
        GDeltaSetTasteGate_single_carrier_alignment_decode_encode N]

private theorem GDeltaSetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GDeltaSetUp} :
    gDeltaSetToEventFlow x = gDeltaSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gDeltaSetFromEventFlow (gDeltaSetToEventFlow x) =
        gDeltaSetFromEventFlow (gDeltaSetToEventFlow y) :=
    congrArg gDeltaSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GDeltaSetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GDeltaSetTasteGate_single_carrier_alignment_round_trip y)))

instance gDeltaSetBHistCarrier : BHistCarrier GDeltaSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gDeltaSetToEventFlow
  fromEventFlow := gDeltaSetFromEventFlow

instance gDeltaSetChapterTasteGate : ChapterTasteGate GDeltaSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gDeltaSetFromEventFlow (gDeltaSetToEventFlow x) = some x
    exact GDeltaSetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GDeltaSetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem GDeltaSetTasteGate_single_carrier_alignment :
    (∀ h : BHist, gDeltaSetDecodeBHist (gDeltaSetEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier GDeltaSetUp) ∧
        Nonempty (ChapterTasteGate GDeltaSetUp) ∧
          gDeltaSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨GDeltaSetTasteGate_single_carrier_alignment_decode_encode,
      ⟨gDeltaSetBHistCarrier⟩,
      ⟨gDeltaSetChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.GDeltaSetUp
