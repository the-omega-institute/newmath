import BEDC.Derived.RealModulusFusionUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealModulusFusionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealModulusFusionUp : Type where
  | mk (X M T W R S E H C P N : BHist) : RealModulusFusionUp
  deriving DecidableEq

def realModulusFusionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realModulusFusionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realModulusFusionEncodeBHist h

def realModulusFusionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realModulusFusionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realModulusFusionDecodeBHist tail)

private theorem realModulusFusionDecode_encode_bhist :
    ∀ h : BHist, realModulusFusionDecodeBHist (realModulusFusionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realModulusFusionFields : RealModulusFusionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealModulusFusionUp.mk X M T W R S E H C P N =>
      [X, M, T, W, R, S, E, H, C, P, N]

def realModulusFusionToEventFlow : RealModulusFusionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realModulusFusionFields x).map realModulusFusionEncodeBHist

def realModulusFusionFromEventFlow : EventFlow → Option RealModulusFusionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | T :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
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
                                                    (RealModulusFusionUp.mk
                                                      (realModulusFusionDecodeBHist X)
                                                      (realModulusFusionDecodeBHist M)
                                                      (realModulusFusionDecodeBHist T)
                                                      (realModulusFusionDecodeBHist W)
                                                      (realModulusFusionDecodeBHist R)
                                                      (realModulusFusionDecodeBHist S)
                                                      (realModulusFusionDecodeBHist E)
                                                      (realModulusFusionDecodeBHist H)
                                                      (realModulusFusionDecodeBHist C)
                                                      (realModulusFusionDecodeBHist P)
                                                      (realModulusFusionDecodeBHist N))
                                              | _ :: _ => none

private theorem realModulusFusion_round_trip :
    ∀ x : RealModulusFusionUp,
      realModulusFusionFromEventFlow (realModulusFusionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X M T W R S E H C P N =>
      change
        some
          (RealModulusFusionUp.mk
            (realModulusFusionDecodeBHist (realModulusFusionEncodeBHist X))
            (realModulusFusionDecodeBHist (realModulusFusionEncodeBHist M))
            (realModulusFusionDecodeBHist (realModulusFusionEncodeBHist T))
            (realModulusFusionDecodeBHist (realModulusFusionEncodeBHist W))
            (realModulusFusionDecodeBHist (realModulusFusionEncodeBHist R))
            (realModulusFusionDecodeBHist (realModulusFusionEncodeBHist S))
            (realModulusFusionDecodeBHist (realModulusFusionEncodeBHist E))
            (realModulusFusionDecodeBHist (realModulusFusionEncodeBHist H))
            (realModulusFusionDecodeBHist (realModulusFusionEncodeBHist C))
            (realModulusFusionDecodeBHist (realModulusFusionEncodeBHist P))
            (realModulusFusionDecodeBHist (realModulusFusionEncodeBHist N))) =
          some (RealModulusFusionUp.mk X M T W R S E H C P N)
      rw [realModulusFusionDecode_encode_bhist X,
        realModulusFusionDecode_encode_bhist M,
        realModulusFusionDecode_encode_bhist T,
        realModulusFusionDecode_encode_bhist W,
        realModulusFusionDecode_encode_bhist R,
        realModulusFusionDecode_encode_bhist S,
        realModulusFusionDecode_encode_bhist E,
        realModulusFusionDecode_encode_bhist H,
        realModulusFusionDecode_encode_bhist C,
        realModulusFusionDecode_encode_bhist P,
        realModulusFusionDecode_encode_bhist N]

private theorem realModulusFusionToEventFlow_injective
    {x y : RealModulusFusionUp} :
    realModulusFusionToEventFlow x = realModulusFusionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have readback :
      realModulusFusionFromEventFlow (realModulusFusionToEventFlow x) =
        realModulusFusionFromEventFlow (realModulusFusionToEventFlow y) :=
    congrArg realModulusFusionFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (realModulusFusion_round_trip x).symm
        (Eq.trans readback (realModulusFusion_round_trip y)))

instance realModulusFusionBHistCarrier : BHistCarrier RealModulusFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realModulusFusionToEventFlow
  fromEventFlow := realModulusFusionFromEventFlow

instance realModulusFusionChapterTasteGate :
    ChapterTasteGate RealModulusFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realModulusFusionFromEventFlow (realModulusFusionToEventFlow x) = some x
    exact realModulusFusion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realModulusFusionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealModulusFusionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realModulusFusionChapterTasteGate

theorem RealModulusFusionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RealModulusFusionUp) ∧
      Nonempty (ChapterTasteGate RealModulusFusionUp) ∧
        (∀ h : BHist, realModulusFusionDecodeBHist (realModulusFusionEncodeBHist h) = h) ∧
          (∀ x : RealModulusFusionUp,
            realModulusFusionFromEventFlow (realModulusFusionToEventFlow x) = some x) ∧
            (∀ x y : RealModulusFusionUp,
              realModulusFusionToEventFlow x = realModulusFusionToEventFlow y → x = y) ∧
              realModulusFusionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨realModulusFusionBHistCarrier⟩
  · constructor
    · exact ⟨realModulusFusionChapterTasteGate⟩
    · constructor
      · exact realModulusFusionDecode_encode_bhist
      · constructor
        · exact realModulusFusion_round_trip
        · constructor
          · intro x y heq
            exact realModulusFusionToEventFlow_injective heq
          · rfl

end BEDC.Derived.RealModulusFusionUp
