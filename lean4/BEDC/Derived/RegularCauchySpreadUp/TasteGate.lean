import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySpreadUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySpreadUp : Type where
  | mk : (S W T R L H C P N : BHist) → RegularCauchySpreadUp
  deriving DecidableEq

def regularCauchySpreadEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySpreadEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySpreadEncodeBHist h

def regularCauchySpreadDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySpreadDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySpreadDecodeBHist tail)

private theorem regularCauchySpreadDecode_encode_bhist :
    ∀ h : BHist, regularCauchySpreadDecodeBHist (regularCauchySpreadEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchySpreadToEventFlow : RegularCauchySpreadUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySpreadUp.mk S W T R L H C P N =>
      [regularCauchySpreadEncodeBHist S,
        regularCauchySpreadEncodeBHist W,
        regularCauchySpreadEncodeBHist T,
        regularCauchySpreadEncodeBHist R,
        regularCauchySpreadEncodeBHist L,
        regularCauchySpreadEncodeBHist H,
        regularCauchySpreadEncodeBHist C,
        regularCauchySpreadEncodeBHist P,
        regularCauchySpreadEncodeBHist N]

def regularCauchySpreadFromEventFlow : EventFlow → Option RegularCauchySpreadUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | T :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (RegularCauchySpreadUp.mk
                                              (regularCauchySpreadDecodeBHist S)
                                              (regularCauchySpreadDecodeBHist W)
                                              (regularCauchySpreadDecodeBHist T)
                                              (regularCauchySpreadDecodeBHist R)
                                              (regularCauchySpreadDecodeBHist L)
                                              (regularCauchySpreadDecodeBHist H)
                                              (regularCauchySpreadDecodeBHist C)
                                              (regularCauchySpreadDecodeBHist P)
                                              (regularCauchySpreadDecodeBHist N))
                                      | _ :: _ => none

private theorem regularCauchySpread_round_trip :
    ∀ x : RegularCauchySpreadUp,
      regularCauchySpreadFromEventFlow (regularCauchySpreadToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W T R L H C P N =>
      change
        some
          (RegularCauchySpreadUp.mk
            (regularCauchySpreadDecodeBHist (regularCauchySpreadEncodeBHist S))
            (regularCauchySpreadDecodeBHist (regularCauchySpreadEncodeBHist W))
            (regularCauchySpreadDecodeBHist (regularCauchySpreadEncodeBHist T))
            (regularCauchySpreadDecodeBHist (regularCauchySpreadEncodeBHist R))
            (regularCauchySpreadDecodeBHist (regularCauchySpreadEncodeBHist L))
            (regularCauchySpreadDecodeBHist (regularCauchySpreadEncodeBHist H))
            (regularCauchySpreadDecodeBHist (regularCauchySpreadEncodeBHist C))
            (regularCauchySpreadDecodeBHist (regularCauchySpreadEncodeBHist P))
            (regularCauchySpreadDecodeBHist (regularCauchySpreadEncodeBHist N))) =
          some (RegularCauchySpreadUp.mk S W T R L H C P N)
      rw [regularCauchySpreadDecode_encode_bhist S,
        regularCauchySpreadDecode_encode_bhist W,
        regularCauchySpreadDecode_encode_bhist T,
        regularCauchySpreadDecode_encode_bhist R,
        regularCauchySpreadDecode_encode_bhist L,
        regularCauchySpreadDecode_encode_bhist H,
        regularCauchySpreadDecode_encode_bhist C,
        regularCauchySpreadDecode_encode_bhist P,
        regularCauchySpreadDecode_encode_bhist N]

private theorem regularCauchySpreadToEventFlow_injective {x y : RegularCauchySpreadUp} :
    regularCauchySpreadToEventFlow x = regularCauchySpreadToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySpreadFromEventFlow (regularCauchySpreadToEventFlow x) =
        regularCauchySpreadFromEventFlow (regularCauchySpreadToEventFlow y) :=
    congrArg regularCauchySpreadFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySpread_round_trip x).symm
      (Eq.trans hread (regularCauchySpread_round_trip y)))

instance regularCauchySpreadBHistCarrier : BHistCarrier RegularCauchySpreadUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySpreadToEventFlow
  fromEventFlow := regularCauchySpreadFromEventFlow

instance regularCauchySpreadChapterTasteGate : ChapterTasteGate RegularCauchySpreadUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchySpreadFromEventFlow (regularCauchySpreadToEventFlow x) = some x
    exact regularCauchySpread_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySpreadToEventFlow_injective heq)

instance regularCauchySpreadNontrivial : Nontrivial RegularCauchySpreadUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchySpreadUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchySpreadUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchySpreadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySpreadChapterTasteGate

theorem RegularCauchySpreadTasteGate_single_carrier_alignment :
    (forall h : BHist, regularCauchySpreadDecodeBHist (regularCauchySpreadEncodeBHist h) = h) ∧
      (forall x : RegularCauchySpreadUp,
        regularCauchySpreadFromEventFlow (regularCauchySpreadToEventFlow x) = some x) ∧
        (forall x y : RegularCauchySpreadUp,
          regularCauchySpreadToEventFlow x = regularCauchySpreadToEventFlow y -> x = y) ∧
          regularCauchySpreadEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchySpreadDecode_encode_bhist, regularCauchySpread_round_trip,
      (fun _ _ heq => regularCauchySpreadToEventFlow_injective heq), rfl⟩

end BEDC.Derived.RegularCauchySpreadUp
