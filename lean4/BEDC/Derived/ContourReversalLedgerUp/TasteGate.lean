import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContourReversalLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContourReversalLedgerUp : Type where
  | mk :
      (source reversed operation negated transport route provenance nameCert : BHist) →
        ContourReversalLedgerUp
  deriving DecidableEq

def contourReversalLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contourReversalLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contourReversalLedgerEncodeBHist h

def contourReversalLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contourReversalLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contourReversalLedgerDecodeBHist tail)

private theorem contourReversalLedger_decode_encode_bhist :
    ∀ h : BHist,
      contourReversalLedgerDecodeBHist (contourReversalLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def contourReversalLedgerToEventFlow : ContourReversalLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ContourReversalLedgerUp.mk source reversed operation negated transport route provenance
      nameCert =>
      [[BMark.b0],
        contourReversalLedgerEncodeBHist source,
        [BMark.b1, BMark.b0],
        contourReversalLedgerEncodeBHist reversed,
        [BMark.b1, BMark.b1, BMark.b0],
        contourReversalLedgerEncodeBHist operation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        contourReversalLedgerEncodeBHist negated,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        contourReversalLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        contourReversalLedgerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        contourReversalLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        contourReversalLedgerEncodeBHist nameCert]

private def contourReversalLedgerRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => contourReversalLedgerRawAt n rest

private def contourReversalLedgerLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => contourReversalLedgerLengthEq n rest

def contourReversalLedgerFromEventFlow : EventFlow → Option ContourReversalLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match contourReversalLedgerLengthEq 16 flow with
      | true =>
          some
            (ContourReversalLedgerUp.mk
              (contourReversalLedgerDecodeBHist (contourReversalLedgerRawAt 1 flow))
              (contourReversalLedgerDecodeBHist (contourReversalLedgerRawAt 3 flow))
              (contourReversalLedgerDecodeBHist (contourReversalLedgerRawAt 5 flow))
              (contourReversalLedgerDecodeBHist (contourReversalLedgerRawAt 7 flow))
              (contourReversalLedgerDecodeBHist (contourReversalLedgerRawAt 9 flow))
              (contourReversalLedgerDecodeBHist (contourReversalLedgerRawAt 11 flow))
              (contourReversalLedgerDecodeBHist (contourReversalLedgerRawAt 13 flow))
              (contourReversalLedgerDecodeBHist (contourReversalLedgerRawAt 15 flow)))
      | false => none

private theorem contourReversalLedger_round_trip :
    ∀ x : ContourReversalLedgerUp,
      contourReversalLedgerFromEventFlow (contourReversalLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source reversed operation negated transport route provenance nameCert =>
      change
        some
          (ContourReversalLedgerUp.mk
            (contourReversalLedgerDecodeBHist
              (contourReversalLedgerEncodeBHist source))
            (contourReversalLedgerDecodeBHist
              (contourReversalLedgerEncodeBHist reversed))
            (contourReversalLedgerDecodeBHist
              (contourReversalLedgerEncodeBHist operation))
            (contourReversalLedgerDecodeBHist
              (contourReversalLedgerEncodeBHist negated))
            (contourReversalLedgerDecodeBHist
              (contourReversalLedgerEncodeBHist transport))
            (contourReversalLedgerDecodeBHist (contourReversalLedgerEncodeBHist route))
            (contourReversalLedgerDecodeBHist
              (contourReversalLedgerEncodeBHist provenance))
            (contourReversalLedgerDecodeBHist
              (contourReversalLedgerEncodeBHist nameCert))) =
          some
            (ContourReversalLedgerUp.mk source reversed operation negated transport route
              provenance nameCert)
      rw [contourReversalLedger_decode_encode_bhist source,
        contourReversalLedger_decode_encode_bhist reversed,
        contourReversalLedger_decode_encode_bhist operation,
        contourReversalLedger_decode_encode_bhist negated,
        contourReversalLedger_decode_encode_bhist transport,
        contourReversalLedger_decode_encode_bhist route,
        contourReversalLedger_decode_encode_bhist provenance,
        contourReversalLedger_decode_encode_bhist nameCert]

private theorem contourReversalLedgerToEventFlow_injective
    {x y : ContourReversalLedgerUp} :
    contourReversalLedgerToEventFlow x = contourReversalLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contourReversalLedgerFromEventFlow (contourReversalLedgerToEventFlow x) =
        contourReversalLedgerFromEventFlow (contourReversalLedgerToEventFlow y) :=
    congrArg contourReversalLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (contourReversalLedger_round_trip x).symm
      (Eq.trans hread (contourReversalLedger_round_trip y)))

instance contourReversalLedgerBHistCarrier : BHistCarrier ContourReversalLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contourReversalLedgerToEventFlow
  fromEventFlow := contourReversalLedgerFromEventFlow

instance contourReversalLedgerChapterTasteGate :
    ChapterTasteGate ContourReversalLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      contourReversalLedgerFromEventFlow (contourReversalLedgerToEventFlow x) =
        some x
    exact contourReversalLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (contourReversalLedgerToEventFlow_injective heq)

instance contourReversalLedgerFieldFaithful : FieldFaithful ContourReversalLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ContourReversalLedgerUp.mk source reversed operation negated transport route provenance
        nameCert =>
        [source, reversed, operation, negated, transport, route, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk source1 reversed1 operation1 negated1 transport1 route1 provenance1 nameCert1 =>
        cases y with
        | mk source2 reversed2 operation2 negated2 transport2 route2 provenance2 nameCert2 =>
            cases h
            rfl

instance contourReversalLedgerNontrivial : Nontrivial ContourReversalLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContourReversalLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ContourReversalLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ContourReversalLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  contourReversalLedgerChapterTasteGate

theorem ContourReversalLedgerTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ContourReversalLedgerUp) ∧
      Nonempty (FieldFaithful ContourReversalLedgerUp) ∧
        Nonempty (Nontrivial ContourReversalLedgerUp) ∧
          (∀ h : BHist,
            contourReversalLedgerDecodeBHist (contourReversalLedgerEncodeBHist h) = h) ∧
            contourReversalLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨contourReversalLedgerChapterTasteGate⟩,
      ⟨contourReversalLedgerFieldFaithful⟩,
      ⟨contourReversalLedgerNontrivial⟩,
      contourReversalLedger_decode_encode_bhist,
      rfl⟩

end BEDC.Derived.ContourReversalLedgerUp
