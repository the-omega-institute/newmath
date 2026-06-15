import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.JordanCurveUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive JordanCurveUp : Type where
  | mk (S F P W O I E H C Q N : BHist) : JordanCurveUp
  deriving DecidableEq

def jordanCurveEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: jordanCurveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: jordanCurveEncodeBHist h

def jordanCurveDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (jordanCurveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (jordanCurveDecodeBHist tail)

private theorem jordanCurve_decode_encode_bhist :
    ∀ h : BHist, jordanCurveDecodeBHist (jordanCurveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def jordanCurveFields : JordanCurveUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | JordanCurveUp.mk S F P W O I E H C Q N => [S, F, P, W, O, I, E, H, C, Q, N]

def jordanCurveToEventFlow : JordanCurveUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (jordanCurveFields x).map jordanCurveEncodeBHist

def jordanCurveSplitEventFlow :
    EventFlow →
      Option
        (RawEvent × RawEvent × RawEvent × RawEvent × RawEvent × RawEvent × RawEvent ×
          RawEvent × RawEvent × RawEvent × RawEvent)
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | s :: r0 =>
    match r0 with
    | [] => none
    | f :: r1 =>
      match r1 with
      | [] => none
      | p :: r2 =>
        match r2 with
        | [] => none
        | w :: r3 =>
          match r3 with
          | [] => none
          | o :: r4 =>
            match r4 with
            | [] => none
            | i :: r5 =>
              match r5 with
              | [] => none
              | e :: r6 =>
                match r6 with
                | [] => none
                | h :: r7 =>
                  match r7 with
                  | [] => none
                  | c :: r8 =>
                    match r8 with
                    | [] => none
                    | q :: r9 =>
                      match r9 with
                      | [] => none
                      | n :: r10 =>
                        match r10 with
                        | [] =>
                            some (s, f, p, w, o, i, e, h, c, q, n)
                        | _ :: _ => none

def jordanCurveFromEventFlow (ef : EventFlow) : Option JordanCurveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match jordanCurveSplitEventFlow ef with
  | some (s, f, p, w, o, i, e, h, c, q, n) =>
      some
        (JordanCurveUp.mk
          (jordanCurveDecodeBHist s)
          (jordanCurveDecodeBHist f)
          (jordanCurveDecodeBHist p)
          (jordanCurveDecodeBHist w)
          (jordanCurveDecodeBHist o)
          (jordanCurveDecodeBHist i)
          (jordanCurveDecodeBHist e)
          (jordanCurveDecodeBHist h)
          (jordanCurveDecodeBHist c)
          (jordanCurveDecodeBHist q)
          (jordanCurveDecodeBHist n))
  | none => none

private theorem jordanCurve_round_trip :
    ∀ x : JordanCurveUp, jordanCurveFromEventFlow (jordanCurveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S F P W O I E H C Q N =>
      change
        some
          (JordanCurveUp.mk
            (jordanCurveDecodeBHist (jordanCurveEncodeBHist S))
            (jordanCurveDecodeBHist (jordanCurveEncodeBHist F))
            (jordanCurveDecodeBHist (jordanCurveEncodeBHist P))
            (jordanCurveDecodeBHist (jordanCurveEncodeBHist W))
            (jordanCurveDecodeBHist (jordanCurveEncodeBHist O))
            (jordanCurveDecodeBHist (jordanCurveEncodeBHist I))
            (jordanCurveDecodeBHist (jordanCurveEncodeBHist E))
            (jordanCurveDecodeBHist (jordanCurveEncodeBHist H))
            (jordanCurveDecodeBHist (jordanCurveEncodeBHist C))
            (jordanCurveDecodeBHist (jordanCurveEncodeBHist Q))
            (jordanCurveDecodeBHist (jordanCurveEncodeBHist N))) =
          some (JordanCurveUp.mk S F P W O I E H C Q N)
      rw [jordanCurve_decode_encode_bhist S, jordanCurve_decode_encode_bhist F,
        jordanCurve_decode_encode_bhist P, jordanCurve_decode_encode_bhist W,
        jordanCurve_decode_encode_bhist O, jordanCurve_decode_encode_bhist I,
        jordanCurve_decode_encode_bhist E, jordanCurve_decode_encode_bhist H,
        jordanCurve_decode_encode_bhist C, jordanCurve_decode_encode_bhist Q,
        jordanCurve_decode_encode_bhist N]

private theorem jordanCurveToEventFlow_injective {x y : JordanCurveUp} :
    jordanCurveToEventFlow x = jordanCurveToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      jordanCurveFromEventFlow (jordanCurveToEventFlow x) =
        jordanCurveFromEventFlow (jordanCurveToEventFlow y) :=
    congrArg jordanCurveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (jordanCurve_round_trip x).symm (Eq.trans hread (jordanCurve_round_trip y)))

private theorem jordanCurve_fields_faithful :
    ∀ x y : JordanCurveUp, jordanCurveFields x = jordanCurveFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 F1 P1 W1 O1 I1 E1 H1 C1 Q1 N1 =>
      cases y with
      | mk S2 F2 P2 W2 O2 I2 E2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance jordanCurveBHistCarrier : BHistCarrier JordanCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := jordanCurveToEventFlow
  fromEventFlow := jordanCurveFromEventFlow

instance jordanCurveChapterTasteGate : ChapterTasteGate JordanCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change jordanCurveFromEventFlow (jordanCurveToEventFlow x) = some x
    exact jordanCurve_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (jordanCurveToEventFlow_injective heq)

instance jordanCurveFieldFaithful : FieldFaithful JordanCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := jordanCurveFields
  field_faithful := jordanCurve_fields_faithful

instance jordanCurveNontrivial : BEDC.Meta.TasteGate.Nontrivial JordanCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨JordanCurveUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      JordanCurveUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem JordanCurveTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate JordanCurveUp) ∧ Nonempty (FieldFaithful JordanCurveUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial JordanCurveUp) ∧
        (∀ h : BHist, jordanCurveDecodeBHist (jordanCurveEncodeBHist h) = h) ∧
          (∀ x : JordanCurveUp, jordanCurveFromEventFlow (jordanCurveToEventFlow x) = some x) ∧
            (∀ x y : JordanCurveUp, jordanCurveToEventFlow x = jordanCurveToEventFlow y →
              x = y) ∧
              jordanCurveEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨jordanCurveChapterTasteGate⟩
  · constructor
    · exact ⟨jordanCurveFieldFaithful⟩
    · constructor
      · exact ⟨jordanCurveNontrivial⟩
      · constructor
        · exact jordanCurve_decode_encode_bhist
        · constructor
          · exact jordanCurve_round_trip
          · constructor
            · intro x y heq
              exact jordanCurveToEventFlow_injective heq
            · rfl

end BEDC.Derived.JordanCurveUp
