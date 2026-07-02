import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformContractionRealCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformContractionRealCompletionUp : Type where
  | mk
      (space contraction modulus cauchyIterate contractionLedger limitCandidate
        realSeal H C P N : BHist) : UniformContractionRealCompletionUp
  deriving DecidableEq

private def uniformContractionRealCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformContractionRealCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformContractionRealCompletionEncodeBHist h

private def uniformContractionRealCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformContractionRealCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformContractionRealCompletionDecodeBHist tail)

private theorem UniformContractionRealCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      uniformContractionRealCompletionDecodeBHist
        (uniformContractionRealCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def uniformContractionRealCompletionFields :
    UniformContractionRealCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformContractionRealCompletionUp.mk space contraction modulus cauchyIterate
      contractionLedger limitCandidate realSeal H C P N =>
        [space, contraction, modulus, cauchyIterate, contractionLedger, limitCandidate,
          realSeal, H, C, P, N]

private def uniformContractionRealCompletionToEventFlow :
    UniformContractionRealCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformContractionRealCompletionFields x).map
      uniformContractionRealCompletionEncodeBHist

private def uniformContractionRealCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformContractionRealCompletionEventAtDefault index rest

private def uniformContractionRealCompletionFromEventFlow (ef : EventFlow) :
    Option UniformContractionRealCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformContractionRealCompletionUp.mk
      (uniformContractionRealCompletionDecodeBHist
        (uniformContractionRealCompletionEventAtDefault 0 ef))
      (uniformContractionRealCompletionDecodeBHist
        (uniformContractionRealCompletionEventAtDefault 1 ef))
      (uniformContractionRealCompletionDecodeBHist
        (uniformContractionRealCompletionEventAtDefault 2 ef))
      (uniformContractionRealCompletionDecodeBHist
        (uniformContractionRealCompletionEventAtDefault 3 ef))
      (uniformContractionRealCompletionDecodeBHist
        (uniformContractionRealCompletionEventAtDefault 4 ef))
      (uniformContractionRealCompletionDecodeBHist
        (uniformContractionRealCompletionEventAtDefault 5 ef))
      (uniformContractionRealCompletionDecodeBHist
        (uniformContractionRealCompletionEventAtDefault 6 ef))
      (uniformContractionRealCompletionDecodeBHist
        (uniformContractionRealCompletionEventAtDefault 7 ef))
      (uniformContractionRealCompletionDecodeBHist
        (uniformContractionRealCompletionEventAtDefault 8 ef))
      (uniformContractionRealCompletionDecodeBHist
        (uniformContractionRealCompletionEventAtDefault 9 ef))
      (uniformContractionRealCompletionDecodeBHist
        (uniformContractionRealCompletionEventAtDefault 10 ef)))

private theorem UniformContractionRealCompletionTasteGate_single_carrier_alignment_round_trip
    (x : UniformContractionRealCompletionUp) :
    uniformContractionRealCompletionFromEventFlow
      (uniformContractionRealCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk space contraction modulus cauchyIterate contractionLedger limitCandidate
      realSeal H C P N =>
      change
        some
          (UniformContractionRealCompletionUp.mk
            (uniformContractionRealCompletionDecodeBHist
              (uniformContractionRealCompletionEncodeBHist space))
            (uniformContractionRealCompletionDecodeBHist
              (uniformContractionRealCompletionEncodeBHist contraction))
            (uniformContractionRealCompletionDecodeBHist
              (uniformContractionRealCompletionEncodeBHist modulus))
            (uniformContractionRealCompletionDecodeBHist
              (uniformContractionRealCompletionEncodeBHist cauchyIterate))
            (uniformContractionRealCompletionDecodeBHist
              (uniformContractionRealCompletionEncodeBHist contractionLedger))
            (uniformContractionRealCompletionDecodeBHist
              (uniformContractionRealCompletionEncodeBHist limitCandidate))
            (uniformContractionRealCompletionDecodeBHist
              (uniformContractionRealCompletionEncodeBHist realSeal))
            (uniformContractionRealCompletionDecodeBHist
              (uniformContractionRealCompletionEncodeBHist H))
            (uniformContractionRealCompletionDecodeBHist
              (uniformContractionRealCompletionEncodeBHist C))
            (uniformContractionRealCompletionDecodeBHist
              (uniformContractionRealCompletionEncodeBHist P))
            (uniformContractionRealCompletionDecodeBHist
              (uniformContractionRealCompletionEncodeBHist N))) =
          some
            (UniformContractionRealCompletionUp.mk space contraction modulus cauchyIterate
              contractionLedger limitCandidate realSeal H C P N)
      rw [UniformContractionRealCompletionTasteGate_single_carrier_alignment_decode_encode space,
        UniformContractionRealCompletionTasteGate_single_carrier_alignment_decode_encode contraction,
        UniformContractionRealCompletionTasteGate_single_carrier_alignment_decode_encode modulus,
        UniformContractionRealCompletionTasteGate_single_carrier_alignment_decode_encode cauchyIterate,
        UniformContractionRealCompletionTasteGate_single_carrier_alignment_decode_encode contractionLedger,
        UniformContractionRealCompletionTasteGate_single_carrier_alignment_decode_encode limitCandidate,
        UniformContractionRealCompletionTasteGate_single_carrier_alignment_decode_encode realSeal,
        UniformContractionRealCompletionTasteGate_single_carrier_alignment_decode_encode H,
        UniformContractionRealCompletionTasteGate_single_carrier_alignment_decode_encode C,
        UniformContractionRealCompletionTasteGate_single_carrier_alignment_decode_encode P,
        UniformContractionRealCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem UniformContractionRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformContractionRealCompletionUp} :
    uniformContractionRealCompletionToEventFlow x =
      uniformContractionRealCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformContractionRealCompletionFromEventFlow
          (uniformContractionRealCompletionToEventFlow x) =
        uniformContractionRealCompletionFromEventFlow
          (uniformContractionRealCompletionToEventFlow y) :=
    congrArg uniformContractionRealCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformContractionRealCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformContractionRealCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformContractionRealCompletionTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : UniformContractionRealCompletionUp,
      uniformContractionRealCompletionFields x = uniformContractionRealCompletionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk space1 contraction1 modulus1 cauchyIterate1 contractionLedger1 limitCandidate1
      realSeal1 H1 C1 P1 N1 =>
      cases y with
      | mk space2 contraction2 modulus2 cauchyIterate2 contractionLedger2 limitCandidate2
          realSeal2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformContractionRealCompletionBHistCarrier :
    BHistCarrier UniformContractionRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformContractionRealCompletionToEventFlow
  fromEventFlow := uniformContractionRealCompletionFromEventFlow

instance uniformContractionRealCompletionChapterTasteGate :
    ChapterTasteGate UniformContractionRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformContractionRealCompletionFromEventFlow
        (uniformContractionRealCompletionToEventFlow x) = some x
    exact UniformContractionRealCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformContractionRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate UniformContractionRealCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformContractionRealCompletionChapterTasteGate

instance uniformContractionRealCompletionFieldFaithful :
    FieldFaithful UniformContractionRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformContractionRealCompletionFields
  field_faithful :=
    UniformContractionRealCompletionTasteGate_single_carrier_alignment_field_faithful

instance uniformContractionRealCompletionNontrivial :
    Nontrivial UniformContractionRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformContractionRealCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      UniformContractionRealCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UniformContractionRealCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformContractionRealCompletionDecodeBHist
        (uniformContractionRealCompletionEncodeBHist h) = h) ∧
      (∀ x : UniformContractionRealCompletionUp,
        uniformContractionRealCompletionFromEventFlow
          (uniformContractionRealCompletionToEventFlow x) = some x) ∧
        (∀ x y : UniformContractionRealCompletionUp,
          uniformContractionRealCompletionToEventFlow x =
            uniformContractionRealCompletionToEventFlow y → x = y) ∧
          uniformContractionRealCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨UniformContractionRealCompletionTasteGate_single_carrier_alignment_decode_encode,
      UniformContractionRealCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformContractionRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformContractionRealCompletionUp
