import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCondensationTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCondensationTestUp : Type where
  | mk (A B I D M R E H C P N : BHist) : CauchyCondensationTestUp
  deriving DecidableEq

def cauchyCondensationTestEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCondensationTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCondensationTestEncodeBHist h

def cauchyCondensationTestDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCondensationTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCondensationTestDecodeBHist tail)

private theorem CauchyCondensationTestTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      cauchyCondensationTestDecodeBHist (cauchyCondensationTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCondensationTestToEventFlow : CauchyCondensationTestUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCondensationTestUp.mk A B I D M R E H C P N =>
      [cauchyCondensationTestEncodeBHist A,
        cauchyCondensationTestEncodeBHist B,
        cauchyCondensationTestEncodeBHist I,
        cauchyCondensationTestEncodeBHist D,
        cauchyCondensationTestEncodeBHist M,
        cauchyCondensationTestEncodeBHist R,
        cauchyCondensationTestEncodeBHist E,
        cauchyCondensationTestEncodeBHist H,
        cauchyCondensationTestEncodeBHist C,
        cauchyCondensationTestEncodeBHist P,
        cauchyCondensationTestEncodeBHist N]

def cauchyCondensationTestFromEventFlow : EventFlow -> Option CauchyCondensationTestUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | I :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | M :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CauchyCondensationTestUp.mk
                                                      (cauchyCondensationTestDecodeBHist A)
                                                      (cauchyCondensationTestDecodeBHist B)
                                                      (cauchyCondensationTestDecodeBHist I)
                                                      (cauchyCondensationTestDecodeBHist D)
                                                      (cauchyCondensationTestDecodeBHist M)
                                                      (cauchyCondensationTestDecodeBHist R)
                                                      (cauchyCondensationTestDecodeBHist E)
                                                      (cauchyCondensationTestDecodeBHist H)
                                                      (cauchyCondensationTestDecodeBHist C)
                                                      (cauchyCondensationTestDecodeBHist P)
                                                      (cauchyCondensationTestDecodeBHist N))
                                              | _ :: _ => none

private theorem CauchyCondensationTestTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyCondensationTestUp,
      cauchyCondensationTestFromEventFlow (cauchyCondensationTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B I D M R E H C P N =>
      change
        some
          (CauchyCondensationTestUp.mk
            (cauchyCondensationTestDecodeBHist (cauchyCondensationTestEncodeBHist A))
            (cauchyCondensationTestDecodeBHist (cauchyCondensationTestEncodeBHist B))
            (cauchyCondensationTestDecodeBHist (cauchyCondensationTestEncodeBHist I))
            (cauchyCondensationTestDecodeBHist (cauchyCondensationTestEncodeBHist D))
            (cauchyCondensationTestDecodeBHist (cauchyCondensationTestEncodeBHist M))
            (cauchyCondensationTestDecodeBHist (cauchyCondensationTestEncodeBHist R))
            (cauchyCondensationTestDecodeBHist (cauchyCondensationTestEncodeBHist E))
            (cauchyCondensationTestDecodeBHist (cauchyCondensationTestEncodeBHist H))
            (cauchyCondensationTestDecodeBHist (cauchyCondensationTestEncodeBHist C))
            (cauchyCondensationTestDecodeBHist (cauchyCondensationTestEncodeBHist P))
            (cauchyCondensationTestDecodeBHist (cauchyCondensationTestEncodeBHist N))) =
          some (CauchyCondensationTestUp.mk A B I D M R E H C P N)
      rw [CauchyCondensationTestTasteGate_single_carrier_alignment_decode A,
        CauchyCondensationTestTasteGate_single_carrier_alignment_decode B,
        CauchyCondensationTestTasteGate_single_carrier_alignment_decode I,
        CauchyCondensationTestTasteGate_single_carrier_alignment_decode D,
        CauchyCondensationTestTasteGate_single_carrier_alignment_decode M,
        CauchyCondensationTestTasteGate_single_carrier_alignment_decode R,
        CauchyCondensationTestTasteGate_single_carrier_alignment_decode E,
        CauchyCondensationTestTasteGate_single_carrier_alignment_decode H,
        CauchyCondensationTestTasteGate_single_carrier_alignment_decode C,
        CauchyCondensationTestTasteGate_single_carrier_alignment_decode P,
        CauchyCondensationTestTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCondensationTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCondensationTestUp} :
    cauchyCondensationTestToEventFlow x = cauchyCondensationTestToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCondensationTestFromEventFlow (cauchyCondensationTestToEventFlow x) =
        cauchyCondensationTestFromEventFlow (cauchyCondensationTestToEventFlow y) :=
    congrArg cauchyCondensationTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCondensationTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCondensationTestTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCondensationTestBHistCarrier : BHistCarrier CauchyCondensationTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCondensationTestToEventFlow
  fromEventFlow := cauchyCondensationTestFromEventFlow

instance cauchyCondensationTestChapterTasteGate : ChapterTasteGate CauchyCondensationTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCondensationTestFromEventFlow (cauchyCondensationTestToEventFlow x) = some x
    exact CauchyCondensationTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCondensationTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCondensationTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCondensationTestChapterTasteGate

theorem CauchyCondensationTestTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyCondensationTestDecodeBHist (cauchyCondensationTestEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCondensationTestUp) ∧
        Nonempty (ChapterTasteGate CauchyCondensationTestUp) ∧
          cauchyCondensationTestEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyCondensationTestTasteGate_single_carrier_alignment_decode,
      ⟨cauchyCondensationTestBHistCarrier⟩,
      ⟨cauchyCondensationTestChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyCondensationTestUp
