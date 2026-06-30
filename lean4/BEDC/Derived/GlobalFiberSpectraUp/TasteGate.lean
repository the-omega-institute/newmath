import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GlobalFiberSpectraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GlobalFiberSpectraUp : Type where
  | mk (F T E L R H C P N : BHist) : GlobalFiberSpectraUp

def globalFiberSpectraEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: globalFiberSpectraEncodeBHist h
  | BHist.e1 h => BMark.b1 :: globalFiberSpectraEncodeBHist h

def globalFiberSpectraDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (globalFiberSpectraDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (globalFiberSpectraDecodeBHist tail)

private theorem globalFiberSpectra_decode_encode_bhist :
    ∀ h : BHist, globalFiberSpectraDecodeBHist (globalFiberSpectraEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def globalFiberSpectraFields : GlobalFiberSpectraUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GlobalFiberSpectraUp.mk F T E L R H C P N => [F, T, E, L, R, H, C, P, N]

def globalFiberSpectraToEventFlow : GlobalFiberSpectraUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (globalFiberSpectraFields x).map globalFiberSpectraEncodeBHist

private def globalFiberSpectraEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => globalFiberSpectraEventAtDefault index rest

def globalFiberSpectraFromEventFlow (flow : EventFlow) : Option GlobalFiberSpectraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GlobalFiberSpectraUp.mk
      (globalFiberSpectraDecodeBHist (globalFiberSpectraEventAtDefault 0 flow))
      (globalFiberSpectraDecodeBHist (globalFiberSpectraEventAtDefault 1 flow))
      (globalFiberSpectraDecodeBHist (globalFiberSpectraEventAtDefault 2 flow))
      (globalFiberSpectraDecodeBHist (globalFiberSpectraEventAtDefault 3 flow))
      (globalFiberSpectraDecodeBHist (globalFiberSpectraEventAtDefault 4 flow))
      (globalFiberSpectraDecodeBHist (globalFiberSpectraEventAtDefault 5 flow))
      (globalFiberSpectraDecodeBHist (globalFiberSpectraEventAtDefault 6 flow))
      (globalFiberSpectraDecodeBHist (globalFiberSpectraEventAtDefault 7 flow))
      (globalFiberSpectraDecodeBHist (globalFiberSpectraEventAtDefault 8 flow)))

private theorem GlobalFiberSpectraCarrier_round_trip :
    ∀ x : GlobalFiberSpectraUp,
      globalFiberSpectraFromEventFlow (globalFiberSpectraToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F T E L R H C P N =>
      change
        some
          (GlobalFiberSpectraUp.mk
            (globalFiberSpectraDecodeBHist (globalFiberSpectraEncodeBHist F))
            (globalFiberSpectraDecodeBHist (globalFiberSpectraEncodeBHist T))
            (globalFiberSpectraDecodeBHist (globalFiberSpectraEncodeBHist E))
            (globalFiberSpectraDecodeBHist (globalFiberSpectraEncodeBHist L))
            (globalFiberSpectraDecodeBHist (globalFiberSpectraEncodeBHist R))
            (globalFiberSpectraDecodeBHist (globalFiberSpectraEncodeBHist H))
            (globalFiberSpectraDecodeBHist (globalFiberSpectraEncodeBHist C))
            (globalFiberSpectraDecodeBHist (globalFiberSpectraEncodeBHist P))
            (globalFiberSpectraDecodeBHist (globalFiberSpectraEncodeBHist N))) =
          some (GlobalFiberSpectraUp.mk F T E L R H C P N)
      rw [globalFiberSpectra_decode_encode_bhist F,
        globalFiberSpectra_decode_encode_bhist T,
        globalFiberSpectra_decode_encode_bhist E,
        globalFiberSpectra_decode_encode_bhist L,
        globalFiberSpectra_decode_encode_bhist R,
        globalFiberSpectra_decode_encode_bhist H,
        globalFiberSpectra_decode_encode_bhist C,
        globalFiberSpectra_decode_encode_bhist P,
        globalFiberSpectra_decode_encode_bhist N]

private theorem GlobalFiberSpectraCarrierToEventFlow_injective {x y : GlobalFiberSpectraUp} :
    globalFiberSpectraToEventFlow x = globalFiberSpectraToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      globalFiberSpectraFromEventFlow (globalFiberSpectraToEventFlow x) =
        globalFiberSpectraFromEventFlow (globalFiberSpectraToEventFlow y) :=
    congrArg globalFiberSpectraFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (GlobalFiberSpectraCarrier_round_trip x).symm
        (Eq.trans hread (GlobalFiberSpectraCarrier_round_trip y)))

private theorem GlobalFiberSpectraCarrier_fields_faithful :
    ∀ x y : GlobalFiberSpectraUp,
      globalFiberSpectraFields x = globalFiberSpectraFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 T1 E1 L1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 T2 E2 L2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance globalFiberSpectraBHistCarrier : BHistCarrier GlobalFiberSpectraUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := globalFiberSpectraToEventFlow
  fromEventFlow := globalFiberSpectraFromEventFlow

instance globalFiberSpectraChapterTasteGate : ChapterTasteGate GlobalFiberSpectraUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change globalFiberSpectraFromEventFlow (globalFiberSpectraToEventFlow x) = some x
    exact GlobalFiberSpectraCarrier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GlobalFiberSpectraCarrierToEventFlow_injective heq)

instance globalFiberSpectraFieldFaithful : FieldFaithful GlobalFiberSpectraUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := globalFiberSpectraFields
  field_faithful := GlobalFiberSpectraCarrier_fields_faithful

instance globalFiberSpectraNontrivial : Nontrivial GlobalFiberSpectraUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GlobalFiberSpectraUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GlobalFiberSpectraUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GlobalFiberSpectraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  globalFiberSpectraChapterTasteGate

def taste_gate_witness : FieldFaithful GlobalFiberSpectraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  globalFiberSpectraFieldFaithful

theorem GlobalFiberSpectraCarrier_event_flow_rows :
    ∃ x : GlobalFiberSpectraUp,
      BHistCarrier.toEventFlow x =
          [[BMark.b0], [BMark.b1], [BMark.b0], [BMark.b1], [BMark.b0],
            [BMark.b1], [BMark.b0], [BMark.b1], [BMark.b0]] ∧
        BHistCarrier.fromEventFlow
            [[BMark.b0], [BMark.b1], [BMark.b0], [BMark.b1], [BMark.b0],
              [BMark.b1], [BMark.b0], [BMark.b1], [BMark.b0]] = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  refine
    ⟨GlobalFiberSpectraUp.mk (BHist.e0 BHist.Empty) (BHist.e1 BHist.Empty)
      (BHist.e0 BHist.Empty) (BHist.e1 BHist.Empty) (BHist.e0 BHist.Empty)
      (BHist.e1 BHist.Empty) (BHist.e0 BHist.Empty) (BHist.e1 BHist.Empty)
      (BHist.e0 BHist.Empty), ?_⟩
  constructor <;> rfl

end BEDC.Derived.GlobalFiberSpectraUp
