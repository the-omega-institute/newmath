import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularModulusUp : Type where
  | mk (source modulus dyadic window transport replay provenance localName : BHist) :
      RegularModulusUp
  deriving DecidableEq

def regularModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularModulusEncodeBHist h

def regularModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularModulusDecodeBHist tail)

private theorem regularModulusDecode_encode :
    ∀ h : BHist, regularModulusDecodeBHist (regularModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularModulusFields : RegularModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularModulusUp.mk source modulus dyadic window transport replay provenance localName =>
      [source, modulus, dyadic, window, transport, replay, provenance, localName]

def regularModulusToEventFlow : RegularModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularModulusFields x).map regularModulusEncodeBHist

private def regularModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularModulusEventAtDefault index rest

def regularModulusFromEventFlow (ef : EventFlow) : Option RegularModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularModulusUp.mk
      (regularModulusDecodeBHist (regularModulusEventAtDefault 0 ef))
      (regularModulusDecodeBHist (regularModulusEventAtDefault 1 ef))
      (regularModulusDecodeBHist (regularModulusEventAtDefault 2 ef))
      (regularModulusDecodeBHist (regularModulusEventAtDefault 3 ef))
      (regularModulusDecodeBHist (regularModulusEventAtDefault 4 ef))
      (regularModulusDecodeBHist (regularModulusEventAtDefault 5 ef))
      (regularModulusDecodeBHist (regularModulusEventAtDefault 6 ef))
      (regularModulusDecodeBHist (regularModulusEventAtDefault 7 ef)))

private theorem RegularModulusUp_round_trip (x : RegularModulusUp) :
    regularModulusFromEventFlow (regularModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk source modulus dyadic window transport replay provenance localName =>
      change
        some
          (RegularModulusUp.mk
            (regularModulusDecodeBHist (regularModulusEncodeBHist source))
            (regularModulusDecodeBHist (regularModulusEncodeBHist modulus))
            (regularModulusDecodeBHist (regularModulusEncodeBHist dyadic))
            (regularModulusDecodeBHist (regularModulusEncodeBHist window))
            (regularModulusDecodeBHist (regularModulusEncodeBHist transport))
            (regularModulusDecodeBHist (regularModulusEncodeBHist replay))
            (regularModulusDecodeBHist (regularModulusEncodeBHist provenance))
            (regularModulusDecodeBHist (regularModulusEncodeBHist localName))) =
          some
            (RegularModulusUp.mk source modulus dyadic window transport replay provenance
              localName)
      rw [regularModulusDecode_encode source, regularModulusDecode_encode modulus,
        regularModulusDecode_encode dyadic, regularModulusDecode_encode window,
        regularModulusDecode_encode transport, regularModulusDecode_encode replay,
        regularModulusDecode_encode provenance, regularModulusDecode_encode localName]

private theorem RegularModulusUp_toEventFlow_injective {x y : RegularModulusUp} :
    regularModulusToEventFlow x = regularModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularModulusFromEventFlow (regularModulusToEventFlow x) =
        regularModulusFromEventFlow (regularModulusToEventFlow y) :=
    congrArg regularModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularModulusUp_round_trip x).symm
      (Eq.trans hread (RegularModulusUp_round_trip y)))

private theorem RegularModulusUp_fields :
    ∀ x y : RegularModulusUp, regularModulusFields x = regularModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source1 modulus1 dyadic1 window1 transport1 replay1 provenance1 localName1 =>
      cases y with
      | mk source2 modulus2 dyadic2 window2 transport2 replay2 provenance2 localName2 =>
          cases hfields
          rfl

instance regularModulusBHistCarrier : BHistCarrier RegularModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularModulusToEventFlow
  fromEventFlow := regularModulusFromEventFlow

instance regularModulusChapterTasteGate : ChapterTasteGate RegularModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularModulusFromEventFlow (regularModulusToEventFlow x) = some x
    exact RegularModulusUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularModulusUp_toEventFlow_injective heq)

instance regularModulusFieldFaithful : FieldFaithful RegularModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularModulusFields
  field_faithful := RegularModulusUp_fields

def taste_gate : ChapterTasteGate RegularModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularModulusChapterTasteGate

theorem RegularModulusTasteGate_single_carrier_alignment (x : RegularModulusUp) :
    (∃ S μ D W H C P N : BHist,
      x = RegularModulusUp.mk S μ D W H C P N ∧
        regularModulusFields x = [S, μ, D, W, H, C, P, N]) ∧
      regularModulusFromEventFlow (regularModulusToEventFlow x) = some x ∧
        regularModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S μ D W H C P N =>
      exact
        ⟨⟨S, μ, D, W, H, C, P, N, rfl, rfl⟩,
          RegularModulusUp_round_trip (RegularModulusUp.mk S μ D W H C P N),
          rfl⟩

end BEDC.Derived.RegularModulusUp
