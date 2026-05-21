import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionFunctorUp : Type where
  | mk :
      (metric regular «seal» «monad» universal classifier transport provenance name : BHist) →
        CauchyCompletionFunctorUp

def cauchyCompletionFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionFunctorEncodeBHist h

def cauchyCompletionFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionFunctorDecodeBHist tail)

private theorem cauchyCompletionFunctorDecode_encode_bhist :
    ∀ h : BHist,
      cauchyCompletionFunctorDecodeBHist (cauchyCompletionFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyCompletionFunctorToEventFlow :
    CauchyCompletionFunctorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | CauchyCompletionFunctorUp.mk metric regular «seal» «monad» universal classifier transport
      provenance name =>
      [[BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionFunctorEncodeBHist metric,
        cauchyCompletionFunctorEncodeBHist regular,
        cauchyCompletionFunctorEncodeBHist «seal»,
        cauchyCompletionFunctorEncodeBHist «monad»,
        cauchyCompletionFunctorEncodeBHist universal,
        cauchyCompletionFunctorEncodeBHist classifier,
        cauchyCompletionFunctorEncodeBHist transport,
        cauchyCompletionFunctorEncodeBHist provenance,
        cauchyCompletionFunctorEncodeBHist name]

def cauchyCompletionFunctorFromEventFlow : EventFlow → Option CauchyCompletionFunctorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | metric :: rest1 =>
          match rest1 with
          | [] => none
          | regular :: rest2 =>
              match rest2 with
              | [] => none
              | sealRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | monadRow :: rest4 =>
                      match rest4 with
                      | [] => none
                      | universal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | classifier :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | name :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CauchyCompletionFunctorUp.mk
                                                  (cauchyCompletionFunctorDecodeBHist metric)
                                                  (cauchyCompletionFunctorDecodeBHist regular)
                                                  (cauchyCompletionFunctorDecodeBHist sealRow)
                                                  (cauchyCompletionFunctorDecodeBHist monadRow)
                                                  (cauchyCompletionFunctorDecodeBHist universal)
                                                  (cauchyCompletionFunctorDecodeBHist classifier)
                                                  (cauchyCompletionFunctorDecodeBHist transport)
                                                  (cauchyCompletionFunctorDecodeBHist provenance)
                                                  (cauchyCompletionFunctorDecodeBHist name))
                                          | _ :: _ => none

private theorem cauchyCompletionFunctor_round_trip :
    ∀ x : CauchyCompletionFunctorUp,
      cauchyCompletionFunctorFromEventFlow (cauchyCompletionFunctorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric regular sealRow monadRow universal classifier transport provenance name =>
      change
        some
            (CauchyCompletionFunctorUp.mk
              (cauchyCompletionFunctorDecodeBHist
                (cauchyCompletionFunctorEncodeBHist metric))
              (cauchyCompletionFunctorDecodeBHist
                (cauchyCompletionFunctorEncodeBHist regular))
              (cauchyCompletionFunctorDecodeBHist
                (cauchyCompletionFunctorEncodeBHist sealRow))
              (cauchyCompletionFunctorDecodeBHist
                (cauchyCompletionFunctorEncodeBHist monadRow))
              (cauchyCompletionFunctorDecodeBHist
                (cauchyCompletionFunctorEncodeBHist universal))
              (cauchyCompletionFunctorDecodeBHist
                (cauchyCompletionFunctorEncodeBHist classifier))
              (cauchyCompletionFunctorDecodeBHist
                (cauchyCompletionFunctorEncodeBHist transport))
              (cauchyCompletionFunctorDecodeBHist
                (cauchyCompletionFunctorEncodeBHist provenance))
              (cauchyCompletionFunctorDecodeBHist
                (cauchyCompletionFunctorEncodeBHist name))) =
          some
            (CauchyCompletionFunctorUp.mk metric regular sealRow monadRow universal classifier
              transport provenance name)
      rw [cauchyCompletionFunctorDecode_encode_bhist metric,
        cauchyCompletionFunctorDecode_encode_bhist regular,
        cauchyCompletionFunctorDecode_encode_bhist sealRow,
        cauchyCompletionFunctorDecode_encode_bhist monadRow,
        cauchyCompletionFunctorDecode_encode_bhist universal,
        cauchyCompletionFunctorDecode_encode_bhist classifier,
        cauchyCompletionFunctorDecode_encode_bhist transport,
        cauchyCompletionFunctorDecode_encode_bhist provenance,
        cauchyCompletionFunctorDecode_encode_bhist name]

private theorem cauchyCompletionFunctorToEventFlow_injective
    {x y : CauchyCompletionFunctorUp} :
    cauchyCompletionFunctorToEventFlow x = cauchyCompletionFunctorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          cauchyCompletionFunctorFromEventFlow (cauchyCompletionFunctorToEventFlow x) :=
        (cauchyCompletionFunctor_round_trip x).symm
      _ =
          cauchyCompletionFunctorFromEventFlow (cauchyCompletionFunctorToEventFlow y) :=
        congrArg cauchyCompletionFunctorFromEventFlow hxy
      _ = some y := cauchyCompletionFunctor_round_trip y
  exact Option.some.inj optionEq

instance cauchyCompletionFunctorBHistCarrier :
    BHistCarrier CauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionFunctorToEventFlow
  fromEventFlow := cauchyCompletionFunctorFromEventFlow

instance cauchyCompletionFunctorChapterTasteGate :
    ChapterTasteGate CauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionFunctorFromEventFlow (cauchyCompletionFunctorToEventFlow x) =
        some x
    exact cauchyCompletionFunctor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionFunctorToEventFlow_injective heq)

theorem CauchyCompletionFunctorTasteGate_single_carrier_alignment :
    Nonempty (BEDC.Meta.TasteGate.BHistCarrier CauchyCompletionFunctorUp) ∧
      Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate CauchyCompletionFunctorUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨⟨cauchyCompletionFunctorBHistCarrier⟩, ⟨cauchyCompletionFunctorChapterTasteGate⟩⟩

end BEDC.Derived.CauchyCompletionFunctorUp
