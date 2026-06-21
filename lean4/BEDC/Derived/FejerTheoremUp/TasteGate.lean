import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FejerTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FejerTheoremUp : Type where
  | mk (F K S I U A L H C P N : BHist) : FejerTheoremUp

def fejerTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fejerTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fejerTheoremEncodeBHist h

def fejerTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fejerTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fejerTheoremDecodeBHist tail)

private theorem fejerTheoremDecode_encode_bhist :
    ∀ h : BHist, fejerTheoremDecodeBHist (fejerTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fejerTheoremFields : FejerTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FejerTheoremUp.mk F K S I U A L H C P N => [F, K, S, I, U, A, L, H, C, P, N]

def fejerTheoremToEventFlow : FejerTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fejerTheoremFields x).map fejerTheoremEncodeBHist

def fejerTheoremFromEventFlow : EventFlow → Option FejerTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: K :: S :: I :: U :: A :: L :: H :: C :: P :: N :: [] =>
      some
        (FejerTheoremUp.mk
          (fejerTheoremDecodeBHist F)
          (fejerTheoremDecodeBHist K)
          (fejerTheoremDecodeBHist S)
          (fejerTheoremDecodeBHist I)
          (fejerTheoremDecodeBHist U)
          (fejerTheoremDecodeBHist A)
          (fejerTheoremDecodeBHist L)
          (fejerTheoremDecodeBHist H)
          (fejerTheoremDecodeBHist C)
          (fejerTheoremDecodeBHist P)
          (fejerTheoremDecodeBHist N))
  | _ => none

private theorem fejerTheorem_round_trip :
    ∀ x : FejerTheoremUp, fejerTheoremFromEventFlow (fejerTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F K S I U A L H C P N =>
      change
        some
          (FejerTheoremUp.mk
            (fejerTheoremDecodeBHist (fejerTheoremEncodeBHist F))
            (fejerTheoremDecodeBHist (fejerTheoremEncodeBHist K))
            (fejerTheoremDecodeBHist (fejerTheoremEncodeBHist S))
            (fejerTheoremDecodeBHist (fejerTheoremEncodeBHist I))
            (fejerTheoremDecodeBHist (fejerTheoremEncodeBHist U))
            (fejerTheoremDecodeBHist (fejerTheoremEncodeBHist A))
            (fejerTheoremDecodeBHist (fejerTheoremEncodeBHist L))
            (fejerTheoremDecodeBHist (fejerTheoremEncodeBHist H))
            (fejerTheoremDecodeBHist (fejerTheoremEncodeBHist C))
            (fejerTheoremDecodeBHist (fejerTheoremEncodeBHist P))
            (fejerTheoremDecodeBHist (fejerTheoremEncodeBHist N))) =
          some (FejerTheoremUp.mk F K S I U A L H C P N)
      rw [fejerTheoremDecode_encode_bhist F, fejerTheoremDecode_encode_bhist K,
        fejerTheoremDecode_encode_bhist S, fejerTheoremDecode_encode_bhist I,
        fejerTheoremDecode_encode_bhist U, fejerTheoremDecode_encode_bhist A,
        fejerTheoremDecode_encode_bhist L, fejerTheoremDecode_encode_bhist H,
        fejerTheoremDecode_encode_bhist C, fejerTheoremDecode_encode_bhist P,
        fejerTheoremDecode_encode_bhist N]

private theorem fejerTheoremToEventFlow_injective {x y : FejerTheoremUp} :
    fejerTheoremToEventFlow x = fejerTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fejerTheoremFromEventFlow (fejerTheoremToEventFlow x) =
        fejerTheoremFromEventFlow (fejerTheoremToEventFlow y) :=
    congrArg fejerTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fejerTheorem_round_trip x).symm
      (Eq.trans hread (fejerTheorem_round_trip y)))

private theorem fejerTheorem_fields_faithful :
    ∀ x y : FejerTheoremUp, fejerTheoremFields x = fejerTheoremFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 K1 S1 I1 U1 A1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 K2 S2 I2 U2 A2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance fejerTheoremBHistCarrier : BHistCarrier FejerTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fejerTheoremToEventFlow
  fromEventFlow := fejerTheoremFromEventFlow

instance fejerTheoremChapterTasteGate : ChapterTasteGate FejerTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fejerTheoremFromEventFlow (fejerTheoremToEventFlow x) = some x
    exact fejerTheorem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fejerTheoremToEventFlow_injective heq)

instance fejerTheoremFieldFaithful : FieldFaithful FejerTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fejerTheoremFields
  field_faithful := fejerTheorem_fields_faithful

theorem FejerTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, fejerTheoremDecodeBHist (fejerTheoremEncodeBHist h) = h) ∧
      (∀ x y : FejerTheoremUp, fejerTheoremFields x = fejerTheoremFields y → x = y) ∧
        fejerTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate BHistCarrier
  exact
    ⟨fejerTheoremDecode_encode_bhist,
      fejerTheorem_fields_faithful,
      rfl⟩

end BEDC.Derived.FejerTheoremUp
