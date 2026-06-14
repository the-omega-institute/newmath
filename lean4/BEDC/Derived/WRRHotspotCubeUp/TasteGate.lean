import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WRRHotspotCubeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WRRHotspotCubeUp : Type where
  | mk (V A L T M Q H C P N : BHist) : WRRHotspotCubeUp
  deriving DecidableEq

def wrrHotspotCubeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: wrrHotspotCubeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: wrrHotspotCubeEncodeBHist h

def wrrHotspotCubeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (wrrHotspotCubeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (wrrHotspotCubeDecodeBHist tail)

private theorem wrrHotspotCubeDecode_encode_bhist :
    ∀ h : BHist, wrrHotspotCubeDecodeBHist (wrrHotspotCubeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def wrrHotspotCubeFields : WRRHotspotCubeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WRRHotspotCubeUp.mk V A L T M Q H C P N => [V, A, L, T, M, Q, H, C, P, N]

def wrrHotspotCubeToEventFlow : WRRHotspotCubeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (wrrHotspotCubeFields x).map wrrHotspotCubeEncodeBHist

private def wrrHotspotCubeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => wrrHotspotCubeEventAtDefault index rest

def wrrHotspotCubeFromEventFlow (ef : EventFlow) : Option WRRHotspotCubeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WRRHotspotCubeUp.mk
      (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEventAtDefault 0 ef))
      (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEventAtDefault 1 ef))
      (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEventAtDefault 2 ef))
      (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEventAtDefault 3 ef))
      (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEventAtDefault 4 ef))
      (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEventAtDefault 5 ef))
      (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEventAtDefault 6 ef))
      (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEventAtDefault 7 ef))
      (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEventAtDefault 8 ef))
      (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEventAtDefault 9 ef)))

private theorem wrrHotspotCube_round_trip :
    ∀ x : WRRHotspotCubeUp, wrrHotspotCubeFromEventFlow (wrrHotspotCubeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V A L T M Q H C P N =>
      change
        some
          (WRRHotspotCubeUp.mk
            (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEncodeBHist V))
            (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEncodeBHist A))
            (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEncodeBHist L))
            (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEncodeBHist T))
            (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEncodeBHist M))
            (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEncodeBHist Q))
            (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEncodeBHist H))
            (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEncodeBHist C))
            (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEncodeBHist P))
            (wrrHotspotCubeDecodeBHist (wrrHotspotCubeEncodeBHist N))) =
          some (WRRHotspotCubeUp.mk V A L T M Q H C P N)
      rw [wrrHotspotCubeDecode_encode_bhist V, wrrHotspotCubeDecode_encode_bhist A,
        wrrHotspotCubeDecode_encode_bhist L, wrrHotspotCubeDecode_encode_bhist T,
        wrrHotspotCubeDecode_encode_bhist M, wrrHotspotCubeDecode_encode_bhist Q,
        wrrHotspotCubeDecode_encode_bhist H, wrrHotspotCubeDecode_encode_bhist C,
        wrrHotspotCubeDecode_encode_bhist P, wrrHotspotCubeDecode_encode_bhist N]

private theorem wrrHotspotCubeToEventFlow_injective {x y : WRRHotspotCubeUp} :
    wrrHotspotCubeToEventFlow x = wrrHotspotCubeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      wrrHotspotCubeFromEventFlow (wrrHotspotCubeToEventFlow x) =
        wrrHotspotCubeFromEventFlow (wrrHotspotCubeToEventFlow y) :=
    congrArg wrrHotspotCubeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (wrrHotspotCube_round_trip x).symm
      (Eq.trans hread (wrrHotspotCube_round_trip y)))

private theorem wrrHotspotCube_fields_faithful :
    ∀ x y : WRRHotspotCubeUp, wrrHotspotCubeFields x = wrrHotspotCubeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk V1 A1 L1 T1 M1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk V2 A2 L2 T2 M2 Q2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance wrrHotspotCubeBHistCarrier : BHistCarrier WRRHotspotCubeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := wrrHotspotCubeToEventFlow
  fromEventFlow := wrrHotspotCubeFromEventFlow

instance wrrHotspotCubeChapterTasteGate : ChapterTasteGate WRRHotspotCubeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change wrrHotspotCubeFromEventFlow (wrrHotspotCubeToEventFlow x) = some x
    exact wrrHotspotCube_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (wrrHotspotCubeToEventFlow_injective heq)

instance wrrHotspotCubeFieldFaithful : FieldFaithful WRRHotspotCubeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := wrrHotspotCubeFields
  field_faithful := wrrHotspotCube_fields_faithful

instance wrrHotspotCubeNontrivial : Nontrivial WRRHotspotCubeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WRRHotspotCubeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WRRHotspotCubeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate WRRHotspotCubeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  wrrHotspotCubeChapterTasteGate

def taste_gate_witness : FieldFaithful WRRHotspotCubeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  wrrHotspotCubeFieldFaithful

theorem WRRHotspotCubeTasteGate_single_carrier_alignment :
    (forall h : BHist, wrrHotspotCubeDecodeBHist (wrrHotspotCubeEncodeBHist h) = h) /\
      (forall x : WRRHotspotCubeUp,
        wrrHotspotCubeFromEventFlow (wrrHotspotCubeToEventFlow x) = some x) /\
        (forall x y : WRRHotspotCubeUp,
          wrrHotspotCubeToEventFlow x = wrrHotspotCubeToEventFlow y -> x = y) /\
          wrrHotspotCubeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨wrrHotspotCubeDecode_encode_bhist, wrrHotspotCube_round_trip,
      by
        intro x y heq
        exact wrrHotspotCubeToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.WRRHotspotCubeUp
