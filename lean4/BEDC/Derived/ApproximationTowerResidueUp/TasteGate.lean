import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApproximationTowerResidueUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApproximationTowerResidueUp : Type where
  | mk :
      (source tower classifier ledger failure recovery descent transport replay provenance
        localName : BHist) →
      ApproximationTowerResidueUp
  deriving DecidableEq

def approximationTowerResidueEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: approximationTowerResidueEncodeBHist h
  | BHist.e1 h => BMark.b1 :: approximationTowerResidueEncodeBHist h

def approximationTowerResidueDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (approximationTowerResidueDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (approximationTowerResidueDecodeBHist tail)

private theorem ApproximationTowerResidueTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      approximationTowerResidueDecodeBHist (approximationTowerResidueEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def approximationTowerResidueFields : ApproximationTowerResidueUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApproximationTowerResidueUp.mk source tower classifier ledger failure recovery descent
      transport replay provenance localName =>
      [source, tower, classifier, ledger, failure, recovery, descent, transport, replay,
        provenance, localName]

def approximationTowerResidueToEventFlow : ApproximationTowerResidueUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ApproximationTowerResidueUp.mk source tower classifier ledger failure recovery descent
      transport replay provenance localName =>
      [[BMark.b0],
        approximationTowerResidueEncodeBHist source,
        [BMark.b1, BMark.b0],
        approximationTowerResidueEncodeBHist tower,
        [BMark.b1, BMark.b1, BMark.b0],
        approximationTowerResidueEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        approximationTowerResidueEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        approximationTowerResidueEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        approximationTowerResidueEncodeBHist recovery,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        approximationTowerResidueEncodeBHist descent,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        approximationTowerResidueEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        approximationTowerResidueEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        approximationTowerResidueEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        approximationTowerResidueEncodeBHist localName]

private def approximationTowerResidueEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ n, [] => approximationTowerResidueEventAtDefault n []
  | Nat.succ n, _event :: rest => approximationTowerResidueEventAtDefault n rest

def approximationTowerResidueFromEventFlow :
    EventFlow → Option ApproximationTowerResidueUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ApproximationTowerResidueUp.mk
          (approximationTowerResidueDecodeBHist
            (approximationTowerResidueEventAtDefault 1 ef))
          (approximationTowerResidueDecodeBHist
            (approximationTowerResidueEventAtDefault 3 ef))
          (approximationTowerResidueDecodeBHist
            (approximationTowerResidueEventAtDefault 5 ef))
          (approximationTowerResidueDecodeBHist
            (approximationTowerResidueEventAtDefault 7 ef))
          (approximationTowerResidueDecodeBHist
            (approximationTowerResidueEventAtDefault 9 ef))
          (approximationTowerResidueDecodeBHist
            (approximationTowerResidueEventAtDefault 11 ef))
          (approximationTowerResidueDecodeBHist
            (approximationTowerResidueEventAtDefault 13 ef))
          (approximationTowerResidueDecodeBHist
            (approximationTowerResidueEventAtDefault 15 ef))
          (approximationTowerResidueDecodeBHist
            (approximationTowerResidueEventAtDefault 17 ef))
          (approximationTowerResidueDecodeBHist
            (approximationTowerResidueEventAtDefault 19 ef))
          (approximationTowerResidueDecodeBHist
            (approximationTowerResidueEventAtDefault 21 ef)))

private theorem ApproximationTowerResidueTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ApproximationTowerResidueUp,
      approximationTowerResidueFromEventFlow
        (approximationTowerResidueToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source tower classifier ledger failure recovery descent transport replay provenance
      localName =>
      change
        some
          (ApproximationTowerResidueUp.mk
            (approximationTowerResidueDecodeBHist
              (approximationTowerResidueEncodeBHist source))
            (approximationTowerResidueDecodeBHist
              (approximationTowerResidueEncodeBHist tower))
            (approximationTowerResidueDecodeBHist
              (approximationTowerResidueEncodeBHist classifier))
            (approximationTowerResidueDecodeBHist
              (approximationTowerResidueEncodeBHist ledger))
            (approximationTowerResidueDecodeBHist
              (approximationTowerResidueEncodeBHist failure))
            (approximationTowerResidueDecodeBHist
              (approximationTowerResidueEncodeBHist recovery))
            (approximationTowerResidueDecodeBHist
              (approximationTowerResidueEncodeBHist descent))
            (approximationTowerResidueDecodeBHist
              (approximationTowerResidueEncodeBHist transport))
            (approximationTowerResidueDecodeBHist
              (approximationTowerResidueEncodeBHist replay))
            (approximationTowerResidueDecodeBHist
              (approximationTowerResidueEncodeBHist provenance))
            (approximationTowerResidueDecodeBHist
              (approximationTowerResidueEncodeBHist localName))) =
          some
            (ApproximationTowerResidueUp.mk source tower classifier ledger failure recovery
              descent transport replay provenance localName)
      rw [ApproximationTowerResidueTasteGate_single_carrier_alignment_decode source,
        ApproximationTowerResidueTasteGate_single_carrier_alignment_decode tower,
        ApproximationTowerResidueTasteGate_single_carrier_alignment_decode classifier,
        ApproximationTowerResidueTasteGate_single_carrier_alignment_decode ledger,
        ApproximationTowerResidueTasteGate_single_carrier_alignment_decode failure,
        ApproximationTowerResidueTasteGate_single_carrier_alignment_decode recovery,
        ApproximationTowerResidueTasteGate_single_carrier_alignment_decode descent,
        ApproximationTowerResidueTasteGate_single_carrier_alignment_decode transport,
        ApproximationTowerResidueTasteGate_single_carrier_alignment_decode replay,
        ApproximationTowerResidueTasteGate_single_carrier_alignment_decode provenance,
        ApproximationTowerResidueTasteGate_single_carrier_alignment_decode localName]

private theorem ApproximationTowerResidueToEventFlow_injective
    {x y : ApproximationTowerResidueUp} :
    approximationTowerResidueToEventFlow x =
      approximationTowerResidueToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      approximationTowerResidueFromEventFlow (approximationTowerResidueToEventFlow x) =
        approximationTowerResidueFromEventFlow (approximationTowerResidueToEventFlow y) :=
    congrArg approximationTowerResidueFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ApproximationTowerResidueTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ApproximationTowerResidueTasteGate_single_carrier_alignment_round_trip y)))

private theorem ApproximationTowerResidueTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : ApproximationTowerResidueUp,
      approximationTowerResidueFields x = approximationTowerResidueFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source tower classifier ledger failure recovery descent transport replay provenance
      localName =>
      cases y with
      | mk source' tower' classifier' ledger' failure' recovery' descent' transport'
          replay' provenance' localName' =>
          cases hfields
          rfl

instance approximationTowerResidueBHistCarrier :
    BHistCarrier ApproximationTowerResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := approximationTowerResidueToEventFlow
  fromEventFlow := approximationTowerResidueFromEventFlow

instance approximationTowerResidueChapterTasteGate :
    ChapterTasteGate ApproximationTowerResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      approximationTowerResidueFromEventFlow
        (approximationTowerResidueToEventFlow x) = some x
    exact ApproximationTowerResidueTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ApproximationTowerResidueToEventFlow_injective heq)

instance approximationTowerResidueFieldFaithful :
    FieldFaithful ApproximationTowerResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := approximationTowerResidueFields
  field_faithful := ApproximationTowerResidueTasteGate_single_carrier_alignment_field_faithful

instance approximationTowerResidueNontrivial :
    Nontrivial ApproximationTowerResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ApproximationTowerResidueUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ApproximationTowerResidueUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ApproximationTowerResidueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  approximationTowerResidueChapterTasteGate

theorem ApproximationTowerResidueTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        approximationTowerResidueDecodeBHist (approximationTowerResidueEncodeBHist h) = h) ∧
      (∀ x : ApproximationTowerResidueUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
        (∀ x y : ApproximationTowerResidueUp,
          BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y) ∧
          BHistCarrier.toEventFlow
              (ApproximationTowerResidueUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty) ≠
            BHistCarrier.toEventFlow
              (ApproximationTowerResidueUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ApproximationTowerResidueTasteGate_single_carrier_alignment_decode
  · constructor
    · intro x
      change
        approximationTowerResidueFromEventFlow
          (approximationTowerResidueToEventFlow x) = some x
      exact ApproximationTowerResidueTasteGate_single_carrier_alignment_round_trip x
    · constructor
      · intro x y heq
        exact ApproximationTowerResidueToEventFlow_injective heq
      · intro heq
        have hxy :=
          ApproximationTowerResidueToEventFlow_injective
            (x := ApproximationTowerResidueUp.mk BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty)
            (y := ApproximationTowerResidueUp.mk (BHist.e0 BHist.Empty) BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty)
            heq
        cases hxy

end BEDC.Derived.ApproximationTowerResidueUp
