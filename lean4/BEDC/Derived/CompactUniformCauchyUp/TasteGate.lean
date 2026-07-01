import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformCauchyUp : Type where
  | mk
      (compactSource family tailWindow regularReadback dyadicTolerance uniformTail realSeal
        transport replay provenance localName : BHist) :
      CompactUniformCauchyUp
  deriving DecidableEq

def compactUniformCauchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformCauchyEncodeBHist h

def compactUniformCauchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformCauchyDecodeBHist tail)

private theorem compactUniformCauchyDecode_encode_bhist :
    ∀ h : BHist, compactUniformCauchyDecodeBHist
      (compactUniformCauchyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformCauchyFields : CompactUniformCauchyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformCauchyUp.mk compactSource family tailWindow regularReadback
      dyadicTolerance uniformTail realSeal transport replay provenance localName =>
      [compactSource, family, tailWindow, regularReadback, dyadicTolerance, uniformTail,
        realSeal, transport, replay, provenance, localName]

def compactUniformCauchyToEventFlow : CompactUniformCauchyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactUniformCauchyFields x).map compactUniformCauchyEncodeBHist

private def compactUniformCauchyEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactUniformCauchyEventAt index rest

def compactUniformCauchyFromEventFlow (ef : EventFlow) : Option CompactUniformCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformCauchyUp.mk
      (compactUniformCauchyDecodeBHist (compactUniformCauchyEventAt 0 ef))
      (compactUniformCauchyDecodeBHist (compactUniformCauchyEventAt 1 ef))
      (compactUniformCauchyDecodeBHist (compactUniformCauchyEventAt 2 ef))
      (compactUniformCauchyDecodeBHist (compactUniformCauchyEventAt 3 ef))
      (compactUniformCauchyDecodeBHist (compactUniformCauchyEventAt 4 ef))
      (compactUniformCauchyDecodeBHist (compactUniformCauchyEventAt 5 ef))
      (compactUniformCauchyDecodeBHist (compactUniformCauchyEventAt 6 ef))
      (compactUniformCauchyDecodeBHist (compactUniformCauchyEventAt 7 ef))
      (compactUniformCauchyDecodeBHist (compactUniformCauchyEventAt 8 ef))
      (compactUniformCauchyDecodeBHist (compactUniformCauchyEventAt 9 ef))
      (compactUniformCauchyDecodeBHist (compactUniformCauchyEventAt 10 ef)))

private theorem compactUniformCauchy_round_trip (x : CompactUniformCauchyUp) :
    compactUniformCauchyFromEventFlow (compactUniformCauchyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk compactSource family tailWindow regularReadback dyadicTolerance uniformTail realSeal
      transport replay provenance localName =>
      change
        some
          (CompactUniformCauchyUp.mk
            (compactUniformCauchyDecodeBHist
              (compactUniformCauchyEncodeBHist compactSource))
            (compactUniformCauchyDecodeBHist (compactUniformCauchyEncodeBHist family))
            (compactUniformCauchyDecodeBHist
              (compactUniformCauchyEncodeBHist tailWindow))
            (compactUniformCauchyDecodeBHist
              (compactUniformCauchyEncodeBHist regularReadback))
            (compactUniformCauchyDecodeBHist
              (compactUniformCauchyEncodeBHist dyadicTolerance))
            (compactUniformCauchyDecodeBHist
              (compactUniformCauchyEncodeBHist uniformTail))
            (compactUniformCauchyDecodeBHist (compactUniformCauchyEncodeBHist realSeal))
            (compactUniformCauchyDecodeBHist
              (compactUniformCauchyEncodeBHist transport))
            (compactUniformCauchyDecodeBHist (compactUniformCauchyEncodeBHist replay))
            (compactUniformCauchyDecodeBHist
              (compactUniformCauchyEncodeBHist provenance))
            (compactUniformCauchyDecodeBHist
              (compactUniformCauchyEncodeBHist localName))) =
          some
            (CompactUniformCauchyUp.mk compactSource family tailWindow regularReadback
              dyadicTolerance uniformTail realSeal transport replay provenance localName)
      rw [compactUniformCauchyDecode_encode_bhist compactSource,
        compactUniformCauchyDecode_encode_bhist family,
        compactUniformCauchyDecode_encode_bhist tailWindow,
        compactUniformCauchyDecode_encode_bhist regularReadback,
        compactUniformCauchyDecode_encode_bhist dyadicTolerance,
        compactUniformCauchyDecode_encode_bhist uniformTail,
        compactUniformCauchyDecode_encode_bhist realSeal,
        compactUniformCauchyDecode_encode_bhist transport,
        compactUniformCauchyDecode_encode_bhist replay,
        compactUniformCauchyDecode_encode_bhist provenance,
        compactUniformCauchyDecode_encode_bhist localName]

private theorem compactUniformCauchyToEventFlow_injective
    {x y : CompactUniformCauchyUp} :
    compactUniformCauchyToEventFlow x = compactUniformCauchyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformCauchyFromEventFlow (compactUniformCauchyToEventFlow x) =
        compactUniformCauchyFromEventFlow (compactUniformCauchyToEventFlow y) :=
    congrArg compactUniformCauchyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactUniformCauchy_round_trip x).symm
      (Eq.trans hread (compactUniformCauchy_round_trip y)))

instance compactUniformCauchyBHistCarrier : BHistCarrier CompactUniformCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformCauchyToEventFlow
  fromEventFlow := compactUniformCauchyFromEventFlow

instance compactUniformCauchyChapterTasteGate :
    ChapterTasteGate CompactUniformCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactUniformCauchyFromEventFlow (compactUniformCauchyToEventFlow x) = some x
    exact compactUniformCauchy_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactUniformCauchyToEventFlow_injective heq)

theorem CompactUniformCauchyTasteGate_single_carrier_alignment :
    (∀ h : BHist, compactUniformCauchyDecodeBHist
        (compactUniformCauchyEncodeBHist h) = h) ∧
      (∀ x : CompactUniformCauchyUp,
        compactUniformCauchyFromEventFlow (compactUniformCauchyToEventFlow x) = some x) ∧
        (∀ x y : CompactUniformCauchyUp,
          compactUniformCauchyToEventFlow x = compactUniformCauchyToEventFlow y →
            x = y) ∧
          compactUniformCauchyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨compactUniformCauchyDecode_encode_bhist,
      compactUniformCauchy_round_trip,
      (fun _ _ heq => compactUniformCauchyToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactUniformCauchyUp
