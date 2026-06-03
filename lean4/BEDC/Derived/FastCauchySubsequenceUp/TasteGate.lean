import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FastCauchySubsequenceUp : Type where
  | mk
      (source modulus selector fast regular readback real transport replay provenance
        localName : BHist) : FastCauchySubsequenceUp
  deriving DecidableEq

def fastCauchySubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fastCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fastCauchySubsequenceEncodeBHist h

def fastCauchySubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fastCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fastCauchySubsequenceDecodeBHist tail)

private theorem FastCauchySubsequenceUp_decode :
    ∀ h : BHist,
      fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fastCauchySubsequenceFields : FastCauchySubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FastCauchySubsequenceUp.mk source modulus selector fast regular readback real transport
      replay provenance localName =>
      [source, modulus, selector, fast, regular, readback, real, transport, replay,
        provenance, localName]

def fastCauchySubsequenceToEventFlow : FastCauchySubsequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (fastCauchySubsequenceFields x).map fastCauchySubsequenceEncodeBHist

private def fastCauchySubsequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fastCauchySubsequenceEventAtDefault index rest

def fastCauchySubsequenceFromEventFlow
    (ef : EventFlow) : Option FastCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FastCauchySubsequenceUp.mk
      (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEventAtDefault 0 ef))
      (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEventAtDefault 1 ef))
      (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEventAtDefault 2 ef))
      (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEventAtDefault 3 ef))
      (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEventAtDefault 4 ef))
      (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEventAtDefault 5 ef))
      (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEventAtDefault 6 ef))
      (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEventAtDefault 7 ef))
      (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEventAtDefault 8 ef))
      (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEventAtDefault 9 ef))
      (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEventAtDefault 10 ef)))

private theorem FastCauchySubsequenceUp_round_trip (x : FastCauchySubsequenceUp) :
    fastCauchySubsequenceFromEventFlow (fastCauchySubsequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk source modulus selector fast regular readback real transport replay provenance localName =>
      change
        some
          (FastCauchySubsequenceUp.mk
            (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEncodeBHist source))
            (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEncodeBHist modulus))
            (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEncodeBHist selector))
            (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEncodeBHist fast))
            (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEncodeBHist regular))
            (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEncodeBHist readback))
            (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEncodeBHist real))
            (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEncodeBHist transport))
            (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEncodeBHist replay))
            (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEncodeBHist provenance))
            (fastCauchySubsequenceDecodeBHist (fastCauchySubsequenceEncodeBHist localName))) =
          some
            (FastCauchySubsequenceUp.mk source modulus selector fast regular readback real
              transport replay provenance localName)
      rw [FastCauchySubsequenceUp_decode source, FastCauchySubsequenceUp_decode modulus,
        FastCauchySubsequenceUp_decode selector, FastCauchySubsequenceUp_decode fast,
        FastCauchySubsequenceUp_decode regular, FastCauchySubsequenceUp_decode readback,
        FastCauchySubsequenceUp_decode real, FastCauchySubsequenceUp_decode transport,
        FastCauchySubsequenceUp_decode replay, FastCauchySubsequenceUp_decode provenance,
        FastCauchySubsequenceUp_decode localName]

private theorem FastCauchySubsequenceUp_toEventFlow_injective
    {x y : FastCauchySubsequenceUp} :
    fastCauchySubsequenceToEventFlow x = fastCauchySubsequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fastCauchySubsequenceFromEventFlow (fastCauchySubsequenceToEventFlow x) =
        fastCauchySubsequenceFromEventFlow (fastCauchySubsequenceToEventFlow y) :=
    congrArg fastCauchySubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FastCauchySubsequenceUp_round_trip x).symm
      (Eq.trans hread (FastCauchySubsequenceUp_round_trip y)))

private theorem FastCauchySubsequenceUp_fields :
    ∀ x y : FastCauchySubsequenceUp,
      fastCauchySubsequenceFields x = fastCauchySubsequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk s1 m1 q1 f1 r1 w1 e1 h1 c1 p1 n1 =>
      cases y with
      | mk s2 m2 q2 f2 r2 w2 e2 h2 c2 p2 n2 =>
          cases hfields
          rfl

instance fastCauchySubsequenceBHistCarrier :
    BHistCarrier FastCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fastCauchySubsequenceToEventFlow
  fromEventFlow := fastCauchySubsequenceFromEventFlow

instance fastCauchySubsequenceChapterTasteGate :
    ChapterTasteGate FastCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fastCauchySubsequenceFromEventFlow (fastCauchySubsequenceToEventFlow x) = some x
    exact FastCauchySubsequenceUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FastCauchySubsequenceUp_toEventFlow_injective heq)

instance fastCauchySubsequenceFieldFaithful :
    FieldFaithful FastCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fastCauchySubsequenceFields
  field_faithful := FastCauchySubsequenceUp_fields

def taste_gate : ChapterTasteGate FastCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fastCauchySubsequenceChapterTasteGate

theorem FastCauchySubsequenceTasteGate_single_carrier_alignment
    (x : FastCauchySubsequenceUp) :
    (∃ source modulus selector fast regular readback real transport replay provenance
        localName : BHist,
      x =
        FastCauchySubsequenceUp.mk source modulus selector fast regular readback real
          transport replay provenance localName ∧
        fastCauchySubsequenceFields x =
          [source, modulus, selector, fast, regular, readback, real, transport, replay,
            provenance, localName]) ∧
      fastCauchySubsequenceFromEventFlow (fastCauchySubsequenceToEventFlow x) = some x ∧
        fastCauchySubsequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk source modulus selector fast regular readback real transport replay provenance
      localName =>
      exact
        ⟨⟨source, modulus, selector, fast, regular, readback, real, transport, replay,
            provenance, localName, rfl, rfl⟩,
          FastCauchySubsequenceUp_round_trip
            (FastCauchySubsequenceUp.mk source modulus selector fast regular readback real
              transport replay provenance localName),
          rfl⟩

end BEDC.Derived.FastCauchySubsequenceUp
