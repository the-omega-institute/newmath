import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteUltrametricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteUltrametricUp : Type where
  | mk (M U C L H R P N : BHist) : CompleteUltrametricUp
  deriving DecidableEq

def completeUltrametricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeUltrametricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeUltrametricEncodeBHist h

def completeUltrametricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeUltrametricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeUltrametricDecodeBHist tail)

private theorem completeUltrametric_decode_encode_bhist :
    ∀ h : BHist,
      completeUltrametricDecodeBHist (completeUltrametricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def completeUltrametricFields : CompleteUltrametricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteUltrametricUp.mk M U C L H R P N => [M, U, C, L, H, R, P, N]

def completeUltrametricToEventFlow : CompleteUltrametricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteUltrametricUp.mk M U C L H R P N =>
      [completeUltrametricEncodeBHist M,
        completeUltrametricEncodeBHist U,
        completeUltrametricEncodeBHist C,
        completeUltrametricEncodeBHist L,
        completeUltrametricEncodeBHist H,
        completeUltrametricEncodeBHist R,
        completeUltrametricEncodeBHist P,
        completeUltrametricEncodeBHist N]

private def completeUltrametricRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => completeUltrametricRawAt n rest

def completeUltrametricFromEventFlow (ef : EventFlow) : Option CompleteUltrametricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompleteUltrametricUp.mk
      (completeUltrametricDecodeBHist (completeUltrametricRawAt 0 ef))
      (completeUltrametricDecodeBHist (completeUltrametricRawAt 1 ef))
      (completeUltrametricDecodeBHist (completeUltrametricRawAt 2 ef))
      (completeUltrametricDecodeBHist (completeUltrametricRawAt 3 ef))
      (completeUltrametricDecodeBHist (completeUltrametricRawAt 4 ef))
      (completeUltrametricDecodeBHist (completeUltrametricRawAt 5 ef))
      (completeUltrametricDecodeBHist (completeUltrametricRawAt 6 ef))
      (completeUltrametricDecodeBHist (completeUltrametricRawAt 7 ef)))

private theorem completeUltrametric_round_trip :
    ∀ x : CompleteUltrametricUp,
      completeUltrametricFromEventFlow (completeUltrametricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M U C L H R P N =>
      change
        some
          (CompleteUltrametricUp.mk
            (completeUltrametricDecodeBHist (completeUltrametricEncodeBHist M))
            (completeUltrametricDecodeBHist (completeUltrametricEncodeBHist U))
            (completeUltrametricDecodeBHist (completeUltrametricEncodeBHist C))
            (completeUltrametricDecodeBHist (completeUltrametricEncodeBHist L))
            (completeUltrametricDecodeBHist (completeUltrametricEncodeBHist H))
            (completeUltrametricDecodeBHist (completeUltrametricEncodeBHist R))
            (completeUltrametricDecodeBHist (completeUltrametricEncodeBHist P))
            (completeUltrametricDecodeBHist (completeUltrametricEncodeBHist N))) =
          some (CompleteUltrametricUp.mk M U C L H R P N)
      rw [completeUltrametric_decode_encode_bhist M,
        completeUltrametric_decode_encode_bhist U,
        completeUltrametric_decode_encode_bhist C,
        completeUltrametric_decode_encode_bhist L,
        completeUltrametric_decode_encode_bhist H,
        completeUltrametric_decode_encode_bhist R,
        completeUltrametric_decode_encode_bhist P,
        completeUltrametric_decode_encode_bhist N]

private theorem completeUltrametricToEventFlow_injective
    {x y : CompleteUltrametricUp} :
    completeUltrametricToEventFlow x = completeUltrametricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeUltrametricFromEventFlow (completeUltrametricToEventFlow x) =
        completeUltrametricFromEventFlow (completeUltrametricToEventFlow y) :=
    congrArg completeUltrametricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completeUltrametric_round_trip x).symm
      (Eq.trans hread (completeUltrametric_round_trip y)))

private theorem completeUltrametric_field_faithful :
    ∀ x y : CompleteUltrametricUp,
      completeUltrametricFields x = completeUltrametricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 U1 C1 L1 H1 R1 P1 N1 =>
      cases y with
      | mk M2 U2 C2 L2 H2 R2 P2 N2 =>
          cases hfields
          rfl

instance completeUltrametricBHistCarrier : BHistCarrier CompleteUltrametricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeUltrametricToEventFlow
  fromEventFlow := completeUltrametricFromEventFlow

instance completeUltrametricChapterTasteGate :
    ChapterTasteGate CompleteUltrametricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completeUltrametricFromEventFlow (completeUltrametricToEventFlow x) = some x
    exact completeUltrametric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (completeUltrametricToEventFlow_injective heq)

instance completeUltrametricFieldFaithful :
    FieldFaithful CompleteUltrametricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completeUltrametricFields
  field_faithful := completeUltrametric_field_faithful

instance completeUltrametricNontrivial :
    Nontrivial CompleteUltrametricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompleteUltrametricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CompleteUltrametricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompleteUltrametricTasteGate_single_carrier_alignment :
    completeUltrametricEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      completeUltrametricEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
      (∀ h : BHist, completeUltrametricDecodeBHist (completeUltrametricEncodeBHist h) = h) ∧
      (∀ x : CompleteUltrametricUp,
        completeUltrametricFromEventFlow (completeUltrametricToEventFlow x) = some x) ∧
      (∀ x y : CompleteUltrametricUp,
        completeUltrametricToEventFlow x = completeUltrametricToEventFlow y → x = y) ∧
      Nonempty (FieldFaithful CompleteUltrametricUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨rfl, rfl, completeUltrametric_decode_encode_bhist, completeUltrametric_round_trip,
      (fun _ _ heq => completeUltrametricToEventFlow_injective heq),
      ⟨completeUltrametricFieldFaithful⟩⟩

end BEDC.Derived.CompleteUltrametricUp
