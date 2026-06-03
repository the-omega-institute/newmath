import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicGeodesicBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicGeodesicBoundaryUp : Type where
  | mk (D M T B J F A H C P N : BHist) : HyperbolicGeodesicBoundaryUp
  deriving DecidableEq

def hyperbolicGeodesicBoundaryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicGeodesicBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicGeodesicBoundaryEncodeBHist h

def hyperbolicGeodesicBoundaryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicGeodesicBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicGeodesicBoundaryDecodeBHist tail)

private theorem HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      hyperbolicGeodesicBoundaryDecodeBHist
          (hyperbolicGeodesicBoundaryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicGeodesicBoundaryFields :
    HyperbolicGeodesicBoundaryUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicGeodesicBoundaryUp.mk D M T B J F A H C P N =>
      [D, M, T, B, J, F, A, H, C, P, N]

def hyperbolicGeodesicBoundaryToEventFlow :
    HyperbolicGeodesicBoundaryUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperbolicGeodesicBoundaryFields x).map hyperbolicGeodesicBoundaryEncodeBHist

private def hyperbolicGeodesicBoundaryEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      hyperbolicGeodesicBoundaryEventAtDefault index rest

def hyperbolicGeodesicBoundaryFromEventFlow
    (ef : EventFlow) : Option HyperbolicGeodesicBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicGeodesicBoundaryUp.mk
      (hyperbolicGeodesicBoundaryDecodeBHist
        (hyperbolicGeodesicBoundaryEventAtDefault 0 ef))
      (hyperbolicGeodesicBoundaryDecodeBHist
        (hyperbolicGeodesicBoundaryEventAtDefault 1 ef))
      (hyperbolicGeodesicBoundaryDecodeBHist
        (hyperbolicGeodesicBoundaryEventAtDefault 2 ef))
      (hyperbolicGeodesicBoundaryDecodeBHist
        (hyperbolicGeodesicBoundaryEventAtDefault 3 ef))
      (hyperbolicGeodesicBoundaryDecodeBHist
        (hyperbolicGeodesicBoundaryEventAtDefault 4 ef))
      (hyperbolicGeodesicBoundaryDecodeBHist
        (hyperbolicGeodesicBoundaryEventAtDefault 5 ef))
      (hyperbolicGeodesicBoundaryDecodeBHist
        (hyperbolicGeodesicBoundaryEventAtDefault 6 ef))
      (hyperbolicGeodesicBoundaryDecodeBHist
        (hyperbolicGeodesicBoundaryEventAtDefault 7 ef))
      (hyperbolicGeodesicBoundaryDecodeBHist
        (hyperbolicGeodesicBoundaryEventAtDefault 8 ef))
      (hyperbolicGeodesicBoundaryDecodeBHist
        (hyperbolicGeodesicBoundaryEventAtDefault 9 ef))
      (hyperbolicGeodesicBoundaryDecodeBHist
        (hyperbolicGeodesicBoundaryEventAtDefault 10 ef)))

private theorem HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_round_trip
    (x : HyperbolicGeodesicBoundaryUp) :
    hyperbolicGeodesicBoundaryFromEventFlow
        (hyperbolicGeodesicBoundaryToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D M T B J F A H C P N =>
      change
        some
          (HyperbolicGeodesicBoundaryUp.mk
            (hyperbolicGeodesicBoundaryDecodeBHist
              (hyperbolicGeodesicBoundaryEncodeBHist D))
            (hyperbolicGeodesicBoundaryDecodeBHist
              (hyperbolicGeodesicBoundaryEncodeBHist M))
            (hyperbolicGeodesicBoundaryDecodeBHist
              (hyperbolicGeodesicBoundaryEncodeBHist T))
            (hyperbolicGeodesicBoundaryDecodeBHist
              (hyperbolicGeodesicBoundaryEncodeBHist B))
            (hyperbolicGeodesicBoundaryDecodeBHist
              (hyperbolicGeodesicBoundaryEncodeBHist J))
            (hyperbolicGeodesicBoundaryDecodeBHist
              (hyperbolicGeodesicBoundaryEncodeBHist F))
            (hyperbolicGeodesicBoundaryDecodeBHist
              (hyperbolicGeodesicBoundaryEncodeBHist A))
            (hyperbolicGeodesicBoundaryDecodeBHist
              (hyperbolicGeodesicBoundaryEncodeBHist H))
            (hyperbolicGeodesicBoundaryDecodeBHist
              (hyperbolicGeodesicBoundaryEncodeBHist C))
            (hyperbolicGeodesicBoundaryDecodeBHist
              (hyperbolicGeodesicBoundaryEncodeBHist P))
            (hyperbolicGeodesicBoundaryDecodeBHist
              (hyperbolicGeodesicBoundaryEncodeBHist N))) =
          some (HyperbolicGeodesicBoundaryUp.mk D M T B J F A H C P N)
      rw [HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_decode_encode D,
        HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_decode_encode M,
        HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_decode_encode T,
        HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_decode_encode B,
        HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_decode_encode J,
        HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_decode_encode F,
        HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_decode_encode A,
        HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_decode_encode H,
        HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_decode_encode C,
        HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_decode_encode P,
        HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_decode_encode N]

private theorem HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_injective
    {x y : HyperbolicGeodesicBoundaryUp} :
    hyperbolicGeodesicBoundaryToEventFlow x =
        hyperbolicGeodesicBoundaryToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicGeodesicBoundaryFromEventFlow
          (hyperbolicGeodesicBoundaryToEventFlow x) =
        hyperbolicGeodesicBoundaryFromEventFlow
          (hyperbolicGeodesicBoundaryToEventFlow y) :=
    congrArg hyperbolicGeodesicBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_round_trip y)))

private theorem HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_fields :
    forall x y : HyperbolicGeodesicBoundaryUp,
      hyperbolicGeodesicBoundaryFields x =
          hyperbolicGeodesicBoundaryFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 M1 T1 B1 J1 F1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 M2 T2 B2 J2 F2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hyperbolicGeodesicBoundaryBHistCarrier :
    BHistCarrier HyperbolicGeodesicBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicGeodesicBoundaryToEventFlow
  fromEventFlow := hyperbolicGeodesicBoundaryFromEventFlow

instance hyperbolicGeodesicBoundaryChapterTasteGate :
    ChapterTasteGate HyperbolicGeodesicBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicGeodesicBoundaryFromEventFlow
          (hyperbolicGeodesicBoundaryToEventFlow x) =
        some x
    exact HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_injective heq)

instance hyperbolicGeodesicBoundaryFieldFaithful :
    FieldFaithful HyperbolicGeodesicBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicGeodesicBoundaryFields
  field_faithful :=
    HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_fields

instance hyperbolicGeodesicBoundaryNontrivial :
    Nontrivial HyperbolicGeodesicBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicGeodesicBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      HyperbolicGeodesicBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate HyperbolicGeodesicBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicGeodesicBoundaryChapterTasteGate

theorem HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      hyperbolicGeodesicBoundaryDecodeBHist
          (hyperbolicGeodesicBoundaryEncodeBHist h) = h) ∧
      (forall x : HyperbolicGeodesicBoundaryUp,
        hyperbolicGeodesicBoundaryFromEventFlow
            (hyperbolicGeodesicBoundaryToEventFlow x) =
          some x) ∧
        (forall x y : HyperbolicGeodesicBoundaryUp,
          hyperbolicGeodesicBoundaryToEventFlow x =
              hyperbolicGeodesicBoundaryToEventFlow y ->
            x = y) ∧
          hyperbolicGeodesicBoundaryEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact HyperbolicGeodesicBoundaryTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.HyperbolicGeodesicBoundaryUp
