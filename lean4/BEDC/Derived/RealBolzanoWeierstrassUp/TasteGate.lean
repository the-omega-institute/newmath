import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealBolzanoWeierstrassUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealBolzanoWeierstrassUp : Type where
  | mk (S D I L R E Q H C P N : BHist) : RealBolzanoWeierstrassUp
  deriving DecidableEq

def realBolzanoWeierstrassEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realBolzanoWeierstrassEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realBolzanoWeierstrassEncodeBHist h

def realBolzanoWeierstrassDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realBolzanoWeierstrassDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realBolzanoWeierstrassDecodeBHist tail)

private theorem realBolzanoWeierstrassDecode_encode_bhist :
    ∀ h : BHist,
      realBolzanoWeierstrassDecodeBHist
        (realBolzanoWeierstrassEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realBolzanoWeierstrassToEventFlow : RealBolzanoWeierstrassUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealBolzanoWeierstrassUp.mk S D I L R E Q H C P N =>
      [realBolzanoWeierstrassEncodeBHist S,
        realBolzanoWeierstrassEncodeBHist D,
        realBolzanoWeierstrassEncodeBHist I,
        realBolzanoWeierstrassEncodeBHist L,
        realBolzanoWeierstrassEncodeBHist R,
        realBolzanoWeierstrassEncodeBHist E,
        realBolzanoWeierstrassEncodeBHist Q,
        realBolzanoWeierstrassEncodeBHist H,
        realBolzanoWeierstrassEncodeBHist C,
        realBolzanoWeierstrassEncodeBHist P,
        realBolzanoWeierstrassEncodeBHist N]

def realBolzanoWeierstrassFromEventFlow :
    EventFlow → Option RealBolzanoWeierstrassUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | I :: rest2 =>
              match rest2 with
              | [] => none
              | L :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | Q :: rest6 =>
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
                                                    (RealBolzanoWeierstrassUp.mk
                                                      (realBolzanoWeierstrassDecodeBHist S)
                                                      (realBolzanoWeierstrassDecodeBHist D)
                                                      (realBolzanoWeierstrassDecodeBHist I)
                                                      (realBolzanoWeierstrassDecodeBHist L)
                                                      (realBolzanoWeierstrassDecodeBHist R)
                                                      (realBolzanoWeierstrassDecodeBHist E)
                                                      (realBolzanoWeierstrassDecodeBHist Q)
                                                      (realBolzanoWeierstrassDecodeBHist H)
                                                      (realBolzanoWeierstrassDecodeBHist C)
                                                      (realBolzanoWeierstrassDecodeBHist P)
                                                      (realBolzanoWeierstrassDecodeBHist N))
                                              | _ :: _ => none

private theorem realBolzanoWeierstrass_round_trip :
    ∀ x : RealBolzanoWeierstrassUp,
      realBolzanoWeierstrassFromEventFlow
        (realBolzanoWeierstrassToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D I L R E Q H C P N =>
      change
        some
          (RealBolzanoWeierstrassUp.mk
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist S))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist D))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist I))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist L))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist R))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist E))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist Q))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist H))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist C))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist P))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist N))) =
          some (RealBolzanoWeierstrassUp.mk S D I L R E Q H C P N)
      rw [realBolzanoWeierstrassDecode_encode_bhist S,
        realBolzanoWeierstrassDecode_encode_bhist D,
        realBolzanoWeierstrassDecode_encode_bhist I,
        realBolzanoWeierstrassDecode_encode_bhist L,
        realBolzanoWeierstrassDecode_encode_bhist R,
        realBolzanoWeierstrassDecode_encode_bhist E,
        realBolzanoWeierstrassDecode_encode_bhist Q,
        realBolzanoWeierstrassDecode_encode_bhist H,
        realBolzanoWeierstrassDecode_encode_bhist C,
        realBolzanoWeierstrassDecode_encode_bhist P,
        realBolzanoWeierstrassDecode_encode_bhist N]

private theorem realBolzanoWeierstrassToEventFlow_injective
    {x y : RealBolzanoWeierstrassUp} :
    realBolzanoWeierstrassToEventFlow x =
      realBolzanoWeierstrassToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realBolzanoWeierstrassFromEventFlow
          (realBolzanoWeierstrassToEventFlow x) =
        realBolzanoWeierstrassFromEventFlow
          (realBolzanoWeierstrassToEventFlow y) :=
    congrArg realBolzanoWeierstrassFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realBolzanoWeierstrass_round_trip x).symm
      (Eq.trans hread (realBolzanoWeierstrass_round_trip y)))

instance realBolzanoWeierstrassBHistCarrier :
    BHistCarrier RealBolzanoWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realBolzanoWeierstrassToEventFlow
  fromEventFlow := realBolzanoWeierstrassFromEventFlow

instance realBolzanoWeierstrassChapterTasteGate :
    ChapterTasteGate RealBolzanoWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realBolzanoWeierstrassFromEventFlow
        (realBolzanoWeierstrassToEventFlow x) = some x
    exact realBolzanoWeierstrass_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realBolzanoWeierstrassToEventFlow_injective heq)

instance realBolzanoWeierstrassNontrivial :
    Nontrivial RealBolzanoWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealBolzanoWeierstrassUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RealBolzanoWeierstrassUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealBolzanoWeierstrassUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realBolzanoWeierstrassChapterTasteGate

theorem RealBolzanoWeierstrassTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realBolzanoWeierstrassDecodeBHist
        (realBolzanoWeierstrassEncodeBHist h) = h) ∧
      (∀ x : RealBolzanoWeierstrassUp,
        realBolzanoWeierstrassFromEventFlow
          (realBolzanoWeierstrassToEventFlow x) = some x) ∧
        (∀ x y : RealBolzanoWeierstrassUp,
          realBolzanoWeierstrassToEventFlow x =
            realBolzanoWeierstrassToEventFlow y → x = y) ∧
          realBolzanoWeierstrassEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∃ x y : RealBolzanoWeierstrassUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark Nontrivial
  exact
    ⟨realBolzanoWeierstrassDecode_encode_bhist,
      realBolzanoWeierstrass_round_trip,
      (fun _ _ heq => realBolzanoWeierstrassToEventFlow_injective heq),
      rfl,
      ⟨RealBolzanoWeierstrassUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        RealBolzanoWeierstrassUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.RealBolzanoWeierstrassUp
