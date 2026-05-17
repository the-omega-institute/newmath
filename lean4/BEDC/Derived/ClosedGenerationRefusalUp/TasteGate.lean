import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedGenerationRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedGenerationRefusalUp : Type where
  | mk (P T G R I H C Q N : BHist) : ClosedGenerationRefusalUp
  deriving DecidableEq

def closedGenerationRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedGenerationRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedGenerationRefusalEncodeBHist h

def closedGenerationRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedGenerationRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedGenerationRefusalDecodeBHist tail)

private theorem closedGenerationRefusal_decode_encode_bhist :
    ∀ h : BHist,
      closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedGenerationRefusalToEventFlow :
    ClosedGenerationRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedGenerationRefusalUp.mk P T G R I H C Q N =>
      [[BMark.b0],
        closedGenerationRefusalEncodeBHist P,
        [BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedGenerationRefusalEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closedGenerationRefusalEncodeBHist N]

private def closedGenerationRefusalEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      closedGenerationRefusalEventAtDefault index rest

def closedGenerationRefusalFromEventFlow
    (ef : EventFlow) : Option ClosedGenerationRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedGenerationRefusalUp.mk
      (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEventAtDefault 1 ef))
      (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEventAtDefault 3 ef))
      (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEventAtDefault 5 ef))
      (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEventAtDefault 7 ef))
      (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEventAtDefault 9 ef))
      (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEventAtDefault 11 ef))
      (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEventAtDefault 13 ef))
      (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEventAtDefault 15 ef))
      (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEventAtDefault 17 ef)))

private theorem closedGenerationRefusal_round_trip :
    ∀ x : ClosedGenerationRefusalUp,
      closedGenerationRefusalFromEventFlow (closedGenerationRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P T G R I H C Q N =>
      change
        some
          (ClosedGenerationRefusalUp.mk
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist P))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist T))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist G))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist R))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist I))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist H))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist C))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist Q))
            (closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist N))) =
          some (ClosedGenerationRefusalUp.mk P T G R I H C Q N)
      rw [closedGenerationRefusal_decode_encode_bhist P,
        closedGenerationRefusal_decode_encode_bhist T,
        closedGenerationRefusal_decode_encode_bhist G,
        closedGenerationRefusal_decode_encode_bhist R,
        closedGenerationRefusal_decode_encode_bhist I,
        closedGenerationRefusal_decode_encode_bhist H,
        closedGenerationRefusal_decode_encode_bhist C,
        closedGenerationRefusal_decode_encode_bhist Q,
        closedGenerationRefusal_decode_encode_bhist N]

private theorem closedGenerationRefusalToEventFlow_injective
    {x y : ClosedGenerationRefusalUp} :
    closedGenerationRefusalToEventFlow x = closedGenerationRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedGenerationRefusalFromEventFlow (closedGenerationRefusalToEventFlow x) =
        closedGenerationRefusalFromEventFlow (closedGenerationRefusalToEventFlow y) :=
    congrArg closedGenerationRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedGenerationRefusal_round_trip x).symm
      (Eq.trans hread (closedGenerationRefusal_round_trip y)))

private def closedGenerationRefusalFields :
    ClosedGenerationRefusalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedGenerationRefusalUp.mk P T G R I H C Q N => [P, T, G, R, I, H, C, Q, N]

private theorem closedGenerationRefusal_field_faithful :
    ∀ x y : ClosedGenerationRefusalUp,
      closedGenerationRefusalFields x = closedGenerationRefusalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P1 T1 G1 R1 I1 H1 C1 Q1 N1 =>
      cases y with
      | mk P2 T2 G2 R2 I2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance closedGenerationRefusalBHistCarrier :
    BHistCarrier ClosedGenerationRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedGenerationRefusalToEventFlow
  fromEventFlow := closedGenerationRefusalFromEventFlow

instance closedGenerationRefusalChapterTasteGate :
    ChapterTasteGate ClosedGenerationRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedGenerationRefusalFromEventFlow (closedGenerationRefusalToEventFlow x) = some x
    exact closedGenerationRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedGenerationRefusalToEventFlow_injective heq)

instance closedGenerationRefusalFieldFaithful :
    FieldFaithful ClosedGenerationRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedGenerationRefusalFields
  field_faithful := closedGenerationRefusal_field_faithful

instance closedGenerationRefusalNontrivial :
    Nontrivial ClosedGenerationRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedGenerationRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedGenerationRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedGenerationRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedGenerationRefusalChapterTasteGate

theorem closedGenerationRefusalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedGenerationRefusalDecodeBHist (closedGenerationRefusalEncodeBHist h) = h) ∧
      (∀ x : ClosedGenerationRefusalUp,
        closedGenerationRefusalFromEventFlow (closedGenerationRefusalToEventFlow x) = some x) ∧
        (∀ x y : ClosedGenerationRefusalUp,
          closedGenerationRefusalToEventFlow x = closedGenerationRefusalToEventFlow y →
            x = y) ∧
          closedGenerationRefusalToEventFlow
              (ClosedGenerationRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ≠
            closedGenerationRefusalToEventFlow
              (ClosedGenerationRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨closedGenerationRefusal_decode_encode_bhist,
      closedGenerationRefusal_round_trip,
      (fun _ _ heq => closedGenerationRefusalToEventFlow_injective heq),
      by
        intro h
        cases h⟩

end BEDC.Derived.ClosedGenerationRefusalUp
