import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HadamardFinitePartUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HadamardFinitePartUp : Type where
  | mk (I S K A B R D E V H C P N : BHist) : HadamardFinitePartUp
  deriving DecidableEq

def hadamardFinitePartEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hadamardFinitePartEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hadamardFinitePartEncodeBHist h

def hadamardFinitePartDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hadamardFinitePartDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hadamardFinitePartDecodeBHist tail)

private theorem hadamardFinitePartDecode_encode_bhist :
    ∀ h : BHist, hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hadamardFinitePartFields : HadamardFinitePartUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HadamardFinitePartUp.mk I S K A B R D E V H C P N =>
      [I, S, K, A, B, R, D, E, V, H, C, P, N]

def hadamardFinitePartToEventFlow : HadamardFinitePartUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hadamardFinitePartFields x).map hadamardFinitePartEncodeBHist

private def hadamardFinitePartEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hadamardFinitePartEventAtDefault index rest

def hadamardFinitePartFromEventFlow (ef : EventFlow) : Option HadamardFinitePartUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HadamardFinitePartUp.mk
      (hadamardFinitePartDecodeBHist (hadamardFinitePartEventAtDefault 0 ef))
      (hadamardFinitePartDecodeBHist (hadamardFinitePartEventAtDefault 1 ef))
      (hadamardFinitePartDecodeBHist (hadamardFinitePartEventAtDefault 2 ef))
      (hadamardFinitePartDecodeBHist (hadamardFinitePartEventAtDefault 3 ef))
      (hadamardFinitePartDecodeBHist (hadamardFinitePartEventAtDefault 4 ef))
      (hadamardFinitePartDecodeBHist (hadamardFinitePartEventAtDefault 5 ef))
      (hadamardFinitePartDecodeBHist (hadamardFinitePartEventAtDefault 6 ef))
      (hadamardFinitePartDecodeBHist (hadamardFinitePartEventAtDefault 7 ef))
      (hadamardFinitePartDecodeBHist (hadamardFinitePartEventAtDefault 8 ef))
      (hadamardFinitePartDecodeBHist (hadamardFinitePartEventAtDefault 9 ef))
      (hadamardFinitePartDecodeBHist (hadamardFinitePartEventAtDefault 10 ef))
      (hadamardFinitePartDecodeBHist (hadamardFinitePartEventAtDefault 11 ef))
      (hadamardFinitePartDecodeBHist (hadamardFinitePartEventAtDefault 12 ef)))

private theorem hadamardFinitePart_round_trip :
    ∀ x : HadamardFinitePartUp,
      hadamardFinitePartFromEventFlow (hadamardFinitePartToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I S K A B R D E V H C P N =>
      change
        some
          (HadamardFinitePartUp.mk
            (hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist I))
            (hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist S))
            (hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist K))
            (hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist A))
            (hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist B))
            (hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist R))
            (hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist D))
            (hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist E))
            (hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist V))
            (hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist H))
            (hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist C))
            (hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist P))
            (hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist N))) =
          some (HadamardFinitePartUp.mk I S K A B R D E V H C P N)
      rw [hadamardFinitePartDecode_encode_bhist I, hadamardFinitePartDecode_encode_bhist S,
        hadamardFinitePartDecode_encode_bhist K, hadamardFinitePartDecode_encode_bhist A,
        hadamardFinitePartDecode_encode_bhist B, hadamardFinitePartDecode_encode_bhist R,
        hadamardFinitePartDecode_encode_bhist D, hadamardFinitePartDecode_encode_bhist E,
        hadamardFinitePartDecode_encode_bhist V, hadamardFinitePartDecode_encode_bhist H,
        hadamardFinitePartDecode_encode_bhist C, hadamardFinitePartDecode_encode_bhist P,
        hadamardFinitePartDecode_encode_bhist N]

private theorem hadamardFinitePartToEventFlow_injective {x y : HadamardFinitePartUp} :
    hadamardFinitePartToEventFlow x = hadamardFinitePartToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hadamardFinitePartFromEventFlow (hadamardFinitePartToEventFlow x) =
        hadamardFinitePartFromEventFlow (hadamardFinitePartToEventFlow y) :=
    congrArg hadamardFinitePartFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hadamardFinitePart_round_trip x).symm
      (Eq.trans hread (hadamardFinitePart_round_trip y)))

private theorem hadamardFinitePart_fields_faithful :
    ∀ x y : HadamardFinitePartUp, hadamardFinitePartFields x = hadamardFinitePartFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 S1 K1 A1 B1 R1 D1 E1 V1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 S2 K2 A2 B2 R2 D2 E2 V2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hadamardFinitePartBHistCarrier : BHistCarrier HadamardFinitePartUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hadamardFinitePartToEventFlow
  fromEventFlow := hadamardFinitePartFromEventFlow

instance hadamardFinitePartChapterTasteGate : ChapterTasteGate HadamardFinitePartUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hadamardFinitePartFromEventFlow (hadamardFinitePartToEventFlow x) = some x
    exact hadamardFinitePart_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hadamardFinitePartToEventFlow_injective heq)

instance hadamardFinitePartFieldFaithful : FieldFaithful HadamardFinitePartUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hadamardFinitePartFields
  field_faithful := hadamardFinitePart_fields_faithful

def taste_gate : ChapterTasteGate HadamardFinitePartUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hadamardFinitePartChapterTasteGate

theorem HadamardFinitePartTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HadamardFinitePartUp) ∧
      Nonempty (BHistCarrier HadamardFinitePartUp) ∧
        (∀ h : BHist,
          hadamardFinitePartDecodeBHist (hadamardFinitePartEncodeBHist h) = h) ∧
          hadamardFinitePartEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate BHistCarrier
  exact
    ⟨⟨hadamardFinitePartChapterTasteGate⟩, ⟨hadamardFinitePartBHistCarrier⟩,
      hadamardFinitePartDecode_encode_bhist, rfl⟩

end BEDC.Derived.HadamardFinitePartUp
