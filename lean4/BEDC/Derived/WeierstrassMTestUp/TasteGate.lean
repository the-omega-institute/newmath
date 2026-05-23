import BEDC.Derived.WeierstrassMTestUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WeierstrassMTestUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WeierstrassMTestUp : Type where
  | mk (F M B T R E H C P N : BHist) : WeierstrassMTestUp

def weierstrassMTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: weierstrassMTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: weierstrassMTestEncodeBHist h

def weierstrassMTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (weierstrassMTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (weierstrassMTestDecodeBHist tail)

private theorem weierstrassMTest_decode_encode_bhist :
    ∀ h : BHist, weierstrassMTestDecodeBHist (weierstrassMTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def weierstrassMTestFields :
    WeierstrassMTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WeierstrassMTestUp.mk F M B T R E H C P N => [F, M, B, T, R, E, H, C, P, N]

def weierstrassMTestToEventFlow :
    WeierstrassMTestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | WeierstrassMTestUp.mk F M B T R E H C P N =>
      [weierstrassMTestEncodeBHist F,
        weierstrassMTestEncodeBHist M,
        weierstrassMTestEncodeBHist B,
        weierstrassMTestEncodeBHist T,
        weierstrassMTestEncodeBHist R,
        weierstrassMTestEncodeBHist E,
        weierstrassMTestEncodeBHist H,
        weierstrassMTestEncodeBHist C,
        weierstrassMTestEncodeBHist P,
        weierstrassMTestEncodeBHist N]

def weierstrassMTestFromEventFlow :
    EventFlow → Option WeierstrassMTestUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: M :: B :: T :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (WeierstrassMTestUp.mk
          (weierstrassMTestDecodeBHist F)
          (weierstrassMTestDecodeBHist M)
          (weierstrassMTestDecodeBHist B)
          (weierstrassMTestDecodeBHist T)
          (weierstrassMTestDecodeBHist R)
          (weierstrassMTestDecodeBHist E)
          (weierstrassMTestDecodeBHist H)
          (weierstrassMTestDecodeBHist C)
          (weierstrassMTestDecodeBHist P)
          (weierstrassMTestDecodeBHist N))
  | _ => none

private theorem weierstrassMTest_round_trip :
    ∀ x : WeierstrassMTestUp,
      weierstrassMTestFromEventFlow (weierstrassMTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F M B T R E H C P N =>
      change
        some
            (WeierstrassMTestUp.mk
              (weierstrassMTestDecodeBHist (weierstrassMTestEncodeBHist F))
              (weierstrassMTestDecodeBHist (weierstrassMTestEncodeBHist M))
              (weierstrassMTestDecodeBHist (weierstrassMTestEncodeBHist B))
              (weierstrassMTestDecodeBHist (weierstrassMTestEncodeBHist T))
              (weierstrassMTestDecodeBHist (weierstrassMTestEncodeBHist R))
              (weierstrassMTestDecodeBHist (weierstrassMTestEncodeBHist E))
              (weierstrassMTestDecodeBHist (weierstrassMTestEncodeBHist H))
              (weierstrassMTestDecodeBHist (weierstrassMTestEncodeBHist C))
              (weierstrassMTestDecodeBHist (weierstrassMTestEncodeBHist P))
              (weierstrassMTestDecodeBHist (weierstrassMTestEncodeBHist N))) =
          some (WeierstrassMTestUp.mk F M B T R E H C P N)
      rw [weierstrassMTest_decode_encode_bhist F,
        weierstrassMTest_decode_encode_bhist M,
        weierstrassMTest_decode_encode_bhist B,
        weierstrassMTest_decode_encode_bhist T,
        weierstrassMTest_decode_encode_bhist R,
        weierstrassMTest_decode_encode_bhist E,
        weierstrassMTest_decode_encode_bhist H,
        weierstrassMTest_decode_encode_bhist C,
        weierstrassMTest_decode_encode_bhist P,
        weierstrassMTest_decode_encode_bhist N]

private theorem weierstrassMTestToEventFlow_injective
    {x y : WeierstrassMTestUp}
    (h : weierstrassMTestToEventFlow x = weierstrassMTestToEventFlow y) :
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  have hread :
      weierstrassMTestFromEventFlow (weierstrassMTestToEventFlow x) =
        weierstrassMTestFromEventFlow (weierstrassMTestToEventFlow y) :=
    congrArg weierstrassMTestFromEventFlow h
  exact Option.some.inj
    (Eq.trans (weierstrassMTest_round_trip x).symm
      (Eq.trans hread (weierstrassMTest_round_trip y)))

private theorem weierstrassMTest_fields_faithful :
    ∀ x y : WeierstrassMTestUp, weierstrassMTestFields x = weierstrassMTestFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F M B T R E H C P N =>
      cases y with
      | mk F' M' B' T' R' E' H' C' P' N' =>
          cases hfields
          rfl

instance weierstrassMTestBHistCarrier : BHistCarrier WeierstrassMTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := weierstrassMTestToEventFlow
  fromEventFlow := weierstrassMTestFromEventFlow

instance weierstrassMTestChapterTasteGate : ChapterTasteGate WeierstrassMTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change weierstrassMTestFromEventFlow (weierstrassMTestToEventFlow x) = some x
    exact weierstrassMTest_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (weierstrassMTestToEventFlow_injective heq)

instance weierstrassMTestFieldFaithful : FieldFaithful WeierstrassMTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := weierstrassMTestFields
  field_faithful := weierstrassMTest_fields_faithful

instance weierstrassMTestNontrivial : BEDC.Meta.TasteGate.Nontrivial WeierstrassMTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WeierstrassMTestUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WeierstrassMTestUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate WeierstrassMTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  weierstrassMTestChapterTasteGate

theorem WeierstrassMTestTasteGate_single_carrier_alignment :
    (∀ h : BHist, weierstrassMTestDecodeBHist (weierstrassMTestEncodeBHist h) = h) /\
      (∀ F M B T R E H C P N : BHist,
        weierstrassMTestToEventFlow (WeierstrassMTestUp.mk F M B T R E H C P N) =
          [weierstrassMTestEncodeBHist F,
            weierstrassMTestEncodeBHist M,
            weierstrassMTestEncodeBHist B,
            weierstrassMTestEncodeBHist T,
            weierstrassMTestEncodeBHist R,
            weierstrassMTestEncodeBHist E,
            weierstrassMTestEncodeBHist H,
            weierstrassMTestEncodeBHist C,
            weierstrassMTestEncodeBHist P,
            weierstrassMTestEncodeBHist N]) /\
          (∀ x y : WeierstrassMTestUp,
            weierstrassMTestFields x = weierstrassMTestFields y → x = y) /\
            (∃ x y : WeierstrassMTestUp, x ≠ y) /\
              weierstrassMTestEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · intro F M B T R E H C P N
      rfl
    · constructor
      · intro x y hfields
        cases x with
        | mk F M B T R E H C P N =>
            cases y with
            | mk F' M' B' T' R' E' H' C' P' N' =>
                cases hfields
                rfl
      · constructor
        · exact
            ⟨WeierstrassMTestUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
              WeierstrassMTestUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty,
              by
                intro h
                cases h⟩
        · rfl

end TasteGate
end BEDC.Derived.WeierstrassMTestUp
