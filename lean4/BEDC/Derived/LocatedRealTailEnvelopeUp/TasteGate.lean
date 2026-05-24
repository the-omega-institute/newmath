import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealTailEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealTailEnvelopeUp : Type where
  | mk (R W D A L S H C P N : BHist) : LocatedRealTailEnvelopeUp
  deriving DecidableEq

def locatedRealTailEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealTailEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealTailEnvelopeEncodeBHist h

def locatedRealTailEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealTailEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealTailEnvelopeDecodeBHist tail)

private theorem locatedRealTailEnvelopeDecode_encode :
    ∀ h : BHist,
      locatedRealTailEnvelopeDecodeBHist (locatedRealTailEnvelopeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealTailEnvelopeToEventFlow : LocatedRealTailEnvelopeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealTailEnvelopeUp.mk R W D A L S H C P N =>
      [locatedRealTailEnvelopeEncodeBHist R,
        locatedRealTailEnvelopeEncodeBHist W,
        locatedRealTailEnvelopeEncodeBHist D,
        locatedRealTailEnvelopeEncodeBHist A,
        locatedRealTailEnvelopeEncodeBHist L,
        locatedRealTailEnvelopeEncodeBHist S,
        locatedRealTailEnvelopeEncodeBHist H,
        locatedRealTailEnvelopeEncodeBHist C,
        locatedRealTailEnvelopeEncodeBHist P,
        locatedRealTailEnvelopeEncodeBHist N]

def locatedRealTailEnvelopeFromEventFlow : EventFlow → Option LocatedRealTailEnvelopeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest =>
      match rest with
      | [] => none
      | W :: rest =>
          match rest with
          | [] => none
          | D :: rest =>
              match rest with
              | [] => none
              | A :: rest =>
                  match rest with
                  | [] => none
                  | L :: rest =>
                      match rest with
                      | [] => none
                      | S :: rest =>
                          match rest with
                          | [] => none
                          | H :: rest =>
                              match rest with
                              | [] => none
                              | C :: rest =>
                                  match rest with
                                  | [] => none
                                  | P :: rest =>
                                      match rest with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (LocatedRealTailEnvelopeUp.mk
                                                  (locatedRealTailEnvelopeDecodeBHist R)
                                                  (locatedRealTailEnvelopeDecodeBHist W)
                                                  (locatedRealTailEnvelopeDecodeBHist D)
                                                  (locatedRealTailEnvelopeDecodeBHist A)
                                                  (locatedRealTailEnvelopeDecodeBHist L)
                                                  (locatedRealTailEnvelopeDecodeBHist S)
                                                  (locatedRealTailEnvelopeDecodeBHist H)
                                                  (locatedRealTailEnvelopeDecodeBHist C)
                                                  (locatedRealTailEnvelopeDecodeBHist P)
                                                  (locatedRealTailEnvelopeDecodeBHist N))
                                          | _ :: _ => none

private theorem locatedRealTailEnvelope_round_trip :
    ∀ x : LocatedRealTailEnvelopeUp,
      locatedRealTailEnvelopeFromEventFlow
        (locatedRealTailEnvelopeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W D A L S H C P N =>
      rw [locatedRealTailEnvelopeToEventFlow, locatedRealTailEnvelopeFromEventFlow,
        locatedRealTailEnvelopeDecode_encode R,
        locatedRealTailEnvelopeDecode_encode W,
        locatedRealTailEnvelopeDecode_encode D,
        locatedRealTailEnvelopeDecode_encode A,
        locatedRealTailEnvelopeDecode_encode L,
        locatedRealTailEnvelopeDecode_encode S,
        locatedRealTailEnvelopeDecode_encode H,
        locatedRealTailEnvelopeDecode_encode C,
        locatedRealTailEnvelopeDecode_encode P,
        locatedRealTailEnvelopeDecode_encode N]

private theorem locatedRealTailEnvelopeToEventFlow_injective {x y : LocatedRealTailEnvelopeUp} :
    locatedRealTailEnvelopeToEventFlow x = locatedRealTailEnvelopeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealTailEnvelopeFromEventFlow (locatedRealTailEnvelopeToEventFlow x) =
        locatedRealTailEnvelopeFromEventFlow (locatedRealTailEnvelopeToEventFlow y) :=
    congrArg locatedRealTailEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedRealTailEnvelope_round_trip x).symm
      (Eq.trans hread (locatedRealTailEnvelope_round_trip y)))

def locatedRealTailEnvelopeFields : LocatedRealTailEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealTailEnvelopeUp.mk R W D A L S H C P N => [R, W, D, A, L, S, H, C, P, N]

private theorem locatedRealTailEnvelope_field_faithful :
    ∀ x y : LocatedRealTailEnvelopeUp,
      locatedRealTailEnvelopeFields x = locatedRealTailEnvelopeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 W1 D1 A1 L1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 W2 D2 A2 L2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedRealTailEnvelopeBHistCarrier :
    BHistCarrier LocatedRealTailEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealTailEnvelopeToEventFlow
  fromEventFlow := locatedRealTailEnvelopeFromEventFlow

instance locatedRealTailEnvelopeChapterTasteGate :
    ChapterTasteGate LocatedRealTailEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedRealTailEnvelopeFromEventFlow
        (locatedRealTailEnvelopeToEventFlow x) = some x
    exact locatedRealTailEnvelope_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealTailEnvelopeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedRealTailEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealTailEnvelopeChapterTasteGate

instance locatedRealTailEnvelopeFieldFaithful :
    FieldFaithful LocatedRealTailEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedRealTailEnvelopeFields
  field_faithful := locatedRealTailEnvelope_field_faithful

instance locatedRealTailEnvelopeNontrivial :
    Nontrivial LocatedRealTailEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedRealTailEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedRealTailEnvelopeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LocatedRealTailEnvelopeUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedRealTailEnvelopeDecodeBHist (locatedRealTailEnvelopeEncodeBHist h) = h) ∧
      (∀ x : LocatedRealTailEnvelopeUp,
        locatedRealTailEnvelopeFromEventFlow
          (locatedRealTailEnvelopeToEventFlow x) = some x) ∧
      (∀ x y : LocatedRealTailEnvelopeUp,
        locatedRealTailEnvelopeToEventFlow x =
          locatedRealTailEnvelopeToEventFlow y → x = y) ∧
      locatedRealTailEnvelopeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨locatedRealTailEnvelopeDecode_encode,
      locatedRealTailEnvelope_round_trip,
      fun _ _ heq => locatedRealTailEnvelopeToEventFlow_injective heq,
      rfl⟩

theorem LocatedRealTailEnvelopeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedRealTailEnvelopeUp) ∧
      Nonempty (FieldFaithful LocatedRealTailEnvelopeUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedRealTailEnvelopeUp) ∧
      (∀ h : BHist,
        locatedRealTailEnvelopeDecodeBHist (locatedRealTailEnvelopeEncodeBHist h) = h) ∧
      (∀ x : LocatedRealTailEnvelopeUp,
        locatedRealTailEnvelopeFromEventFlow
          (locatedRealTailEnvelopeToEventFlow x) = some x) ∧
      (∀ x y : LocatedRealTailEnvelopeUp,
        locatedRealTailEnvelopeToEventFlow x =
          locatedRealTailEnvelopeToEventFlow y → x = y) ∧
      locatedRealTailEnvelopeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨Nonempty.intro locatedRealTailEnvelopeChapterTasteGate,
      Nonempty.intro locatedRealTailEnvelopeFieldFaithful,
      Nonempty.intro locatedRealTailEnvelopeNontrivial,
      locatedRealTailEnvelopeDecode_encode,
      locatedRealTailEnvelope_round_trip,
      fun _ _ heq => locatedRealTailEnvelopeToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocatedRealTailEnvelopeUp
