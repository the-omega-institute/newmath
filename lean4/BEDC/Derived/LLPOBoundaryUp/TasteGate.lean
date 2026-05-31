import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LLPOBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LLPOBoundaryUp : Type where
  | mk (Z0 Z1 S R D E W H C P N : BHist) : LLPOBoundaryUp

def llpoBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: llpoBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: llpoBoundaryEncodeBHist h

def llpoBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (llpoBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (llpoBoundaryDecodeBHist tail)

private theorem LLPOBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def llpoBoundaryToEventFlow : LLPOBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LLPOBoundaryUp.mk Z0 Z1 S R D E W H C P N =>
      [llpoBoundaryEncodeBHist Z0,
        llpoBoundaryEncodeBHist Z1,
        llpoBoundaryEncodeBHist S,
        llpoBoundaryEncodeBHist R,
        llpoBoundaryEncodeBHist D,
        llpoBoundaryEncodeBHist E,
        llpoBoundaryEncodeBHist W,
        llpoBoundaryEncodeBHist H,
        llpoBoundaryEncodeBHist C,
        llpoBoundaryEncodeBHist P,
        llpoBoundaryEncodeBHist N]

def llpoBoundaryFromEventFlow : EventFlow → Option LLPOBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | Z0 :: rest0 =>
      match rest0 with
      | [] => none
      | Z1 :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | W :: rest6 =>
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
                                                    (LLPOBoundaryUp.mk
                                                      (llpoBoundaryDecodeBHist Z0)
                                                      (llpoBoundaryDecodeBHist Z1)
                                                      (llpoBoundaryDecodeBHist S)
                                                      (llpoBoundaryDecodeBHist R)
                                                      (llpoBoundaryDecodeBHist D)
                                                      (llpoBoundaryDecodeBHist E)
                                                      (llpoBoundaryDecodeBHist W)
                                                      (llpoBoundaryDecodeBHist H)
                                                      (llpoBoundaryDecodeBHist C)
                                                      (llpoBoundaryDecodeBHist P)
                                                      (llpoBoundaryDecodeBHist N))
                                              | _extra :: _rest => none

private theorem llpoBoundary_round_trip :
    ∀ x : LLPOBoundaryUp,
      llpoBoundaryFromEventFlow (llpoBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Z0 Z1 S R D E W H C P N =>
      change
        some
          (LLPOBoundaryUp.mk
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist Z0))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist Z1))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist S))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist R))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist D))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist E))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist W))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist H))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist C))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist P))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist N))) =
          some (LLPOBoundaryUp.mk Z0 Z1 S R D E W H C P N)
      rw [LLPOBoundaryTasteGate_single_carrier_alignment_decode Z0,
        LLPOBoundaryTasteGate_single_carrier_alignment_decode Z1,
        LLPOBoundaryTasteGate_single_carrier_alignment_decode S,
        LLPOBoundaryTasteGate_single_carrier_alignment_decode R,
        LLPOBoundaryTasteGate_single_carrier_alignment_decode D,
        LLPOBoundaryTasteGate_single_carrier_alignment_decode E,
        LLPOBoundaryTasteGate_single_carrier_alignment_decode W,
        LLPOBoundaryTasteGate_single_carrier_alignment_decode H,
        LLPOBoundaryTasteGate_single_carrier_alignment_decode C,
        LLPOBoundaryTasteGate_single_carrier_alignment_decode P,
        LLPOBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem llpoBoundaryToEventFlow_injective {x y : LLPOBoundaryUp} :
    llpoBoundaryToEventFlow x = llpoBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      llpoBoundaryFromEventFlow (llpoBoundaryToEventFlow x) =
        llpoBoundaryFromEventFlow (llpoBoundaryToEventFlow y) :=
    congrArg llpoBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (llpoBoundary_round_trip x).symm
      (Eq.trans hread (llpoBoundary_round_trip y)))

instance llpoBoundaryBHistCarrier : BHistCarrier LLPOBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := llpoBoundaryToEventFlow
  fromEventFlow := llpoBoundaryFromEventFlow

instance llpoBoundaryChapterTasteGate : ChapterTasteGate LLPOBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change llpoBoundaryFromEventFlow (llpoBoundaryToEventFlow x) = some x
    exact llpoBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (llpoBoundaryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LLPOBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  llpoBoundaryChapterTasteGate

theorem LLPOBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LLPOBoundaryUp) ∧
        Nonempty (ChapterTasteGate LLPOBoundaryUp) ∧
          llpoBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LLPOBoundaryTasteGate_single_carrier_alignment_decode,
      ⟨llpoBoundaryBHistCarrier⟩,
      ⟨llpoBoundaryChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LLPOBoundaryUp
