import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedClosedIntervalFiniteNetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedClosedIntervalFiniteNetUp : Type where
  | mk (I M N D W R E H C P L : BHist) : LocatedClosedIntervalFiniteNetUp
  deriving DecidableEq

def locatedClosedIntervalFiniteNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedClosedIntervalFiniteNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedClosedIntervalFiniteNetEncodeBHist h

def locatedClosedIntervalFiniteNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedClosedIntervalFiniteNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedClosedIntervalFiniteNetDecodeBHist tail)

private theorem LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedClosedIntervalFiniteNetDecodeBHist
        (locatedClosedIntervalFiniteNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedClosedIntervalFiniteNetFields :
    LocatedClosedIntervalFiniteNetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedClosedIntervalFiniteNetUp.mk I M N D W R E H C P L =>
      [I, M, N, D, W, R, E, H, C, P, L]

def locatedClosedIntervalFiniteNetToEventFlow :
    LocatedClosedIntervalFiniteNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedClosedIntervalFiniteNetFields x).map
      locatedClosedIntervalFiniteNetEncodeBHist

private def LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_eventAt index rest

def locatedClosedIntervalFiniteNetFromEventFlow
    (ef : EventFlow) : Option LocatedClosedIntervalFiniteNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedClosedIntervalFiniteNetUp.mk
      (locatedClosedIntervalFiniteNetDecodeBHist
        (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_eventAt 0 ef))
      (locatedClosedIntervalFiniteNetDecodeBHist
        (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_eventAt 1 ef))
      (locatedClosedIntervalFiniteNetDecodeBHist
        (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_eventAt 2 ef))
      (locatedClosedIntervalFiniteNetDecodeBHist
        (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_eventAt 3 ef))
      (locatedClosedIntervalFiniteNetDecodeBHist
        (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_eventAt 4 ef))
      (locatedClosedIntervalFiniteNetDecodeBHist
        (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_eventAt 5 ef))
      (locatedClosedIntervalFiniteNetDecodeBHist
        (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_eventAt 6 ef))
      (locatedClosedIntervalFiniteNetDecodeBHist
        (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_eventAt 7 ef))
      (locatedClosedIntervalFiniteNetDecodeBHist
        (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_eventAt 8 ef))
      (locatedClosedIntervalFiniteNetDecodeBHist
        (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_eventAt 9 ef))
      (locatedClosedIntervalFiniteNetDecodeBHist
        (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_round_trip
    (x : LocatedClosedIntervalFiniteNetUp) :
    locatedClosedIntervalFiniteNetFromEventFlow
      (locatedClosedIntervalFiniteNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I M N D W R E H C P L =>
      change
        some
          (LocatedClosedIntervalFiniteNetUp.mk
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist I))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist M))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist N))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist D))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist W))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist R))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist E))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist H))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist C))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist P))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist L))) =
          some (LocatedClosedIntervalFiniteNetUp.mk I M N D W R E H C P L)
      rw [LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_decode_encode I,
        LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_decode_encode M,
        LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_decode_encode N,
        LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_decode_encode D,
        LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_decode_encode W,
        LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_decode_encode R,
        LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_decode_encode E,
        LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_decode_encode H,
        LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_decode_encode C,
        LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_decode_encode P,
        LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_decode_encode L]

private theorem LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedClosedIntervalFiniteNetUp} :
    locatedClosedIntervalFiniteNetToEventFlow x =
      locatedClosedIntervalFiniteNetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedClosedIntervalFiniteNetFromEventFlow
          (locatedClosedIntervalFiniteNetToEventFlow x) =
        locatedClosedIntervalFiniteNetFromEventFlow
          (locatedClosedIntervalFiniteNetToEventFlow y) :=
    congrArg locatedClosedIntervalFiniteNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LocatedClosedIntervalFiniteNetUp,
      locatedClosedIntervalFiniteNetFields x =
        locatedClosedIntervalFiniteNetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ M₁ N₁ D₁ W₁ R₁ E₁ H₁ C₁ P₁ L₁ =>
      cases y with
      | mk I₂ M₂ N₂ D₂ W₂ R₂ E₂ H₂ C₂ P₂ L₂ =>
          cases hfields
          rfl

instance locatedClosedIntervalFiniteNetBHistCarrier :
    BHistCarrier LocatedClosedIntervalFiniteNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedClosedIntervalFiniteNetToEventFlow
  fromEventFlow := locatedClosedIntervalFiniteNetFromEventFlow

instance locatedClosedIntervalFiniteNetChapterTasteGate :
    ChapterTasteGate LocatedClosedIntervalFiniteNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedClosedIntervalFiniteNetFromEventFlow
        (locatedClosedIntervalFiniteNetToEventFlow x) = some x
    exact LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance locatedClosedIntervalFiniteNetFieldFaithful :
    FieldFaithful LocatedClosedIntervalFiniteNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedClosedIntervalFiniteNetFields
  field_faithful :=
    LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_fields_faithful

instance locatedClosedIntervalFiniteNetNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LocatedClosedIntervalFiniteNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedClosedIntervalFiniteNetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      LocatedClosedIntervalFiniteNetUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedClosedIntervalFiniteNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedClosedIntervalFiniteNetChapterTasteGate

theorem LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedClosedIntervalFiniteNetUp) ∧
      Nonempty (FieldFaithful LocatedClosedIntervalFiniteNetUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedClosedIntervalFiniteNetUp) ∧
          (∀ h : BHist,
            locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist h) = h) ∧
            (∀ x : LocatedClosedIntervalFiniteNetUp,
              locatedClosedIntervalFiniteNetFromEventFlow
                (locatedClosedIntervalFiniteNetToEventFlow x) = some x) ∧
              (∀ x y : LocatedClosedIntervalFiniteNetUp,
                locatedClosedIntervalFiniteNetToEventFlow x =
                  locatedClosedIntervalFiniteNetToEventFlow y → x = y) ∧
                locatedClosedIntervalFiniteNetEncodeBHist BHist.Empty =
                  ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨locatedClosedIntervalFiniteNetChapterTasteGate⟩,
      ⟨locatedClosedIntervalFiniteNetFieldFaithful⟩,
      ⟨locatedClosedIntervalFiniteNetNontrivial⟩,
      LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_decode_encode,
      LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.LocatedClosedIntervalFiniteNetUp.TasteGate
