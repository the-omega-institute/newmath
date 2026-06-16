import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealComparisonModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealComparisonModulusUp : Type where
  | mk (left right apartness modulus transport replay provenance localName : BHist) :
      LocatedRealComparisonModulusUp
  deriving DecidableEq

def locatedRealComparisonModulusEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealComparisonModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealComparisonModulusEncodeBHist h

def locatedRealComparisonModulusDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealComparisonModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealComparisonModulusDecodeBHist tail)

private theorem locatedRealComparisonModulusDecodeEncode :
    ∀ h : BHist,
      locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealComparisonModulusFields :
    LocatedRealComparisonModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealComparisonModulusUp.mk left right apartness modulus transport replay provenance
      localName =>
      [left, right, apartness, modulus, transport, replay, provenance, localName]

def locatedRealComparisonModulusToEventFlow :
    LocatedRealComparisonModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (locatedRealComparisonModulusFields x).map locatedRealComparisonModulusEncodeBHist

private def locatedRealComparisonModulusEventAtDefault :
    Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      locatedRealComparisonModulusEventAtDefault index rest

def locatedRealComparisonModulusFromEventFlow
    (ef : EventFlow) : Option LocatedRealComparisonModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRealComparisonModulusUp.mk
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAtDefault 0 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAtDefault 1 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAtDefault 2 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAtDefault 3 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAtDefault 4 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAtDefault 5 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAtDefault 6 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAtDefault 7 ef)))

private theorem locatedRealComparisonModulusRoundTrip :
    ∀ x : LocatedRealComparisonModulusUp,
      locatedRealComparisonModulusFromEventFlow
        (locatedRealComparisonModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk left right apartness modulus transport replay provenance localName =>
      change
        some
          (LocatedRealComparisonModulusUp.mk
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist left))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist right))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist apartness))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist modulus))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist transport))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist replay))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist provenance))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist localName))) =
          some
            (LocatedRealComparisonModulusUp.mk left right apartness modulus transport replay
              provenance localName)
      rw [locatedRealComparisonModulusDecodeEncode left,
        locatedRealComparisonModulusDecodeEncode right,
        locatedRealComparisonModulusDecodeEncode apartness,
        locatedRealComparisonModulusDecodeEncode modulus,
        locatedRealComparisonModulusDecodeEncode transport,
        locatedRealComparisonModulusDecodeEncode replay,
        locatedRealComparisonModulusDecodeEncode provenance,
        locatedRealComparisonModulusDecodeEncode localName]

private theorem locatedRealComparisonModulusToEventFlow_injective
    {x y : LocatedRealComparisonModulusUp} :
    locatedRealComparisonModulusToEventFlow x =
      locatedRealComparisonModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealComparisonModulusFromEventFlow
          (locatedRealComparisonModulusToEventFlow x) =
        locatedRealComparisonModulusFromEventFlow
          (locatedRealComparisonModulusToEventFlow y) :=
    congrArg locatedRealComparisonModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedRealComparisonModulusRoundTrip x).symm
      (Eq.trans hread (locatedRealComparisonModulusRoundTrip y)))

instance locatedRealComparisonModulusBHistCarrier :
    BHistCarrier LocatedRealComparisonModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealComparisonModulusToEventFlow
  fromEventFlow := locatedRealComparisonModulusFromEventFlow

instance locatedRealComparisonModulusChapterTasteGate :
    ChapterTasteGate LocatedRealComparisonModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRealComparisonModulusFromEventFlow
      (locatedRealComparisonModulusToEventFlow x) = some x
    exact locatedRealComparisonModulusRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealComparisonModulusToEventFlow_injective heq)

theorem LocatedRealComparisonModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedRealComparisonModulusUp) ∧
        Nonempty (ChapterTasteGate LocatedRealComparisonModulusUp) ∧
          locatedRealComparisonModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locatedRealComparisonModulusDecodeEncode,
      ⟨locatedRealComparisonModulusBHistCarrier⟩,
      ⟨locatedRealComparisonModulusChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedRealComparisonModulusUp.TasteGate
