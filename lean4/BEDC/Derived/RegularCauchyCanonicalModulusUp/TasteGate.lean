import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCanonicalModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCanonicalModulusUp : Type where
  | mk
      (dyadic stream regular modulus endpoint transport replay provenance
        localName : BHist) : RegularCauchyCanonicalModulusUp
  deriving DecidableEq

def regularCauchyCanonicalModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCanonicalModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCanonicalModulusEncodeBHist h

def regularCauchyCanonicalModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCanonicalModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCanonicalModulusDecodeBHist tail)

private theorem RegularCauchyCanonicalModulusUp_decode :
    ∀ h : BHist,
      regularCauchyCanonicalModulusDecodeBHist
          (regularCauchyCanonicalModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCanonicalModulusFields :
    RegularCauchyCanonicalModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCanonicalModulusUp.mk dyadic stream regular modulus endpoint transport
      replay provenance localName =>
      [dyadic, stream, regular, modulus, endpoint, transport, replay, provenance, localName]

def regularCauchyCanonicalModulusToEventFlow :
    RegularCauchyCanonicalModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyCanonicalModulusFields x).map
      regularCauchyCanonicalModulusEncodeBHist

private def regularCauchyCanonicalModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyCanonicalModulusEventAtDefault index rest

def regularCauchyCanonicalModulusFromEventFlow
    (ef : EventFlow) : Option RegularCauchyCanonicalModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyCanonicalModulusUp.mk
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 0 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 1 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 2 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 3 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 4 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 5 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 6 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 7 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 8 ef)))

private theorem RegularCauchyCanonicalModulusUp_round_trip
    (x : RegularCauchyCanonicalModulusUp) :
    regularCauchyCanonicalModulusFromEventFlow
        (regularCauchyCanonicalModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk dyadic stream regular modulus endpoint transport replay provenance localName =>
      change
        some
          (RegularCauchyCanonicalModulusUp.mk
            (regularCauchyCanonicalModulusDecodeBHist
              (regularCauchyCanonicalModulusEncodeBHist dyadic))
            (regularCauchyCanonicalModulusDecodeBHist
              (regularCauchyCanonicalModulusEncodeBHist stream))
            (regularCauchyCanonicalModulusDecodeBHist
              (regularCauchyCanonicalModulusEncodeBHist regular))
            (regularCauchyCanonicalModulusDecodeBHist
              (regularCauchyCanonicalModulusEncodeBHist modulus))
            (regularCauchyCanonicalModulusDecodeBHist
              (regularCauchyCanonicalModulusEncodeBHist endpoint))
            (regularCauchyCanonicalModulusDecodeBHist
              (regularCauchyCanonicalModulusEncodeBHist transport))
            (regularCauchyCanonicalModulusDecodeBHist
              (regularCauchyCanonicalModulusEncodeBHist replay))
            (regularCauchyCanonicalModulusDecodeBHist
              (regularCauchyCanonicalModulusEncodeBHist provenance))
            (regularCauchyCanonicalModulusDecodeBHist
              (regularCauchyCanonicalModulusEncodeBHist localName))) =
          some
            (RegularCauchyCanonicalModulusUp.mk dyadic stream regular modulus endpoint
              transport replay provenance localName)
      rw [RegularCauchyCanonicalModulusUp_decode dyadic,
        RegularCauchyCanonicalModulusUp_decode stream,
        RegularCauchyCanonicalModulusUp_decode regular,
        RegularCauchyCanonicalModulusUp_decode modulus,
        RegularCauchyCanonicalModulusUp_decode endpoint,
        RegularCauchyCanonicalModulusUp_decode transport,
        RegularCauchyCanonicalModulusUp_decode replay,
        RegularCauchyCanonicalModulusUp_decode provenance,
        RegularCauchyCanonicalModulusUp_decode localName]

private theorem RegularCauchyCanonicalModulusUp_toEventFlow_injective
    {x y : RegularCauchyCanonicalModulusUp} :
    regularCauchyCanonicalModulusToEventFlow x =
        regularCauchyCanonicalModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCanonicalModulusFromEventFlow
          (regularCauchyCanonicalModulusToEventFlow x) =
        regularCauchyCanonicalModulusFromEventFlow
          (regularCauchyCanonicalModulusToEventFlow y) :=
    congrArg regularCauchyCanonicalModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyCanonicalModulusUp_round_trip x).symm
      (Eq.trans hread (RegularCauchyCanonicalModulusUp_round_trip y)))

instance regularCauchyCanonicalModulusBHistCarrier :
    BHistCarrier RegularCauchyCanonicalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCanonicalModulusToEventFlow
  fromEventFlow := regularCauchyCanonicalModulusFromEventFlow

instance regularCauchyCanonicalModulusChapterTasteGate :
    ChapterTasteGate RegularCauchyCanonicalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCanonicalModulusFromEventFlow
          (regularCauchyCanonicalModulusToEventFlow x) = some x
    exact RegularCauchyCanonicalModulusUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyCanonicalModulusUp_toEventFlow_injective heq)

theorem RegularCauchyCanonicalModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyCanonicalModulusDecodeBHist
          (regularCauchyCanonicalModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyCanonicalModulusUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyCanonicalModulusUp) ∧
          regularCauchyCanonicalModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyCanonicalModulusUp_decode,
      ⟨regularCauchyCanonicalModulusBHistCarrier⟩,
      ⟨regularCauchyCanonicalModulusChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyCanonicalModulusUp
