import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusPullbackUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusPullbackUp : Type where
  | mk (S I K M D R E H C P N : BHist) : CauchyModulusPullbackUp
  deriving DecidableEq

def cauchyModulusPullbackEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusPullbackEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusPullbackEncodeBHist h

def cauchyModulusPullbackDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusPullbackDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusPullbackDecodeBHist tail)

private theorem cauchyModulusPullbackDecode_encode_bhist :
    ∀ h : BHist,
      cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyModulusPullbackFields : CauchyModulusPullbackUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusPullbackUp.mk S I K M D R E H C P N => [S, I, K, M, D, R, E, H, C, P, N]

def cauchyModulusPullbackToEventFlow : CauchyModulusPullbackUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusPullbackUp.mk S I K M D R E H C P N =>
      [[BMark.b1, BMark.b0, BMark.b1, BMark.b0],
        cauchyModulusPullbackEncodeBHist S,
        cauchyModulusPullbackEncodeBHist I,
        cauchyModulusPullbackEncodeBHist K,
        cauchyModulusPullbackEncodeBHist M,
        cauchyModulusPullbackEncodeBHist D,
        cauchyModulusPullbackEncodeBHist R,
        cauchyModulusPullbackEncodeBHist E,
        cauchyModulusPullbackEncodeBHist H,
        cauchyModulusPullbackEncodeBHist C,
        cauchyModulusPullbackEncodeBHist P,
        cauchyModulusPullbackEncodeBHist N]

def cauchyModulusPullbackFromEventFlow : EventFlow → Option CauchyModulusPullbackUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag, S, I, K, M, D, R, E, H, C, P, N] =>
      some
        (CauchyModulusPullbackUp.mk
          (cauchyModulusPullbackDecodeBHist S)
          (cauchyModulusPullbackDecodeBHist I)
          (cauchyModulusPullbackDecodeBHist K)
          (cauchyModulusPullbackDecodeBHist M)
          (cauchyModulusPullbackDecodeBHist D)
          (cauchyModulusPullbackDecodeBHist R)
          (cauchyModulusPullbackDecodeBHist E)
          (cauchyModulusPullbackDecodeBHist H)
          (cauchyModulusPullbackDecodeBHist C)
          (cauchyModulusPullbackDecodeBHist P)
          (cauchyModulusPullbackDecodeBHist N))
  | _ => none

private theorem cauchyModulusPullback_round_trip :
    ∀ x : CauchyModulusPullbackUp,
      cauchyModulusPullbackFromEventFlow (cauchyModulusPullbackToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S I K M D R E H C P N =>
      change
        some
          (CauchyModulusPullbackUp.mk
            (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEncodeBHist S))
            (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEncodeBHist I))
            (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEncodeBHist K))
            (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEncodeBHist M))
            (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEncodeBHist D))
            (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEncodeBHist R))
            (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEncodeBHist E))
            (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEncodeBHist H))
            (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEncodeBHist C))
            (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEncodeBHist P))
            (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEncodeBHist N))) =
          some (CauchyModulusPullbackUp.mk S I K M D R E H C P N)
      rw [cauchyModulusPullbackDecode_encode_bhist S,
        cauchyModulusPullbackDecode_encode_bhist I,
        cauchyModulusPullbackDecode_encode_bhist K,
        cauchyModulusPullbackDecode_encode_bhist M,
        cauchyModulusPullbackDecode_encode_bhist D,
        cauchyModulusPullbackDecode_encode_bhist R,
        cauchyModulusPullbackDecode_encode_bhist E,
        cauchyModulusPullbackDecode_encode_bhist H,
        cauchyModulusPullbackDecode_encode_bhist C,
        cauchyModulusPullbackDecode_encode_bhist P,
        cauchyModulusPullbackDecode_encode_bhist N]

private theorem cauchyModulusPullbackToEventFlow_injective {x y : CauchyModulusPullbackUp} :
    cauchyModulusPullbackToEventFlow x = cauchyModulusPullbackToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusPullbackFromEventFlow (cauchyModulusPullbackToEventFlow x) =
        cauchyModulusPullbackFromEventFlow (cauchyModulusPullbackToEventFlow y) :=
    congrArg cauchyModulusPullbackFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyModulusPullback_round_trip x).symm
      (Eq.trans hread (cauchyModulusPullback_round_trip y)))

private theorem cauchyModulusPullback_fields_faithful :
    ∀ x y : CauchyModulusPullbackUp,
      cauchyModulusPullbackFields x = cauchyModulusPullbackFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 I1 K1 M1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 I2 K2 M2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyModulusPullbackBHistCarrier : BHistCarrier CauchyModulusPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusPullbackToEventFlow
  fromEventFlow := cauchyModulusPullbackFromEventFlow

instance cauchyModulusPullbackChapterTasteGate :
    ChapterTasteGate CauchyModulusPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyModulusPullbackFromEventFlow (cauchyModulusPullbackToEventFlow x) = some x
    exact cauchyModulusPullback_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusPullbackToEventFlow_injective heq)

instance cauchyModulusPullbackFieldFaithful : FieldFaithful CauchyModulusPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyModulusPullbackFields
  field_faithful := cauchyModulusPullback_fields_faithful

def taste_gate : ChapterTasteGate CauchyModulusPullbackUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusPullbackChapterTasteGate

theorem CauchyModulusPullbackTasteGate_single_carrier_alignment :
    (forall h : BHist,
        cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEncodeBHist h) = h) ∧
      cauchyModulusPullbackFields
          (CauchyModulusPullbackUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
      cauchyModulusPullbackToEventFlow
          (CauchyModulusPullbackUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [[BMark.b1, BMark.b0, BMark.b1, BMark.b0], [], [], [], [], [], [], [], [], [], [],
          []] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact ⟨cauchyModulusPullbackDecode_encode_bhist, rfl, rfl⟩

end BEDC.Derived.CauchyModulusPullbackUp.TasteGate
