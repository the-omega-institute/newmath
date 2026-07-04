import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusDiagonalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusDiagonalUp : Type where
  | mk (F S Q E M T W H C P N : BHist) : CauchyModulusDiagonalUp
  deriving DecidableEq

def cauchyModulusDiagonalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusDiagonalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusDiagonalEncodeBHist h

def cauchyModulusDiagonalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusDiagonalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusDiagonalDecodeBHist tail)

private theorem cauchyModulusDiagonal_decode_encode_bhist :
    ∀ h : BHist, cauchyModulusDiagonalDecodeBHist (cauchyModulusDiagonalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusDiagonalFields : CauchyModulusDiagonalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusDiagonalUp.mk F S Q E M T W H C P N => [F, S, Q, E, M, T, W, H, C, P, N]

def cauchyModulusDiagonalToEventFlow : CauchyModulusDiagonalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyModulusDiagonalFields x).map cauchyModulusDiagonalEncodeBHist

def cauchyModulusDiagonalFromEventFlow : EventFlow → Option CauchyModulusDiagonalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | F :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | Q :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | M :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
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
                                                    (CauchyModulusDiagonalUp.mk
                                                      (cauchyModulusDiagonalDecodeBHist F)
                                                      (cauchyModulusDiagonalDecodeBHist S)
                                                      (cauchyModulusDiagonalDecodeBHist Q)
                                                      (cauchyModulusDiagonalDecodeBHist E)
                                                      (cauchyModulusDiagonalDecodeBHist M)
                                                      (cauchyModulusDiagonalDecodeBHist T)
                                                      (cauchyModulusDiagonalDecodeBHist W)
                                                      (cauchyModulusDiagonalDecodeBHist H)
                                                      (cauchyModulusDiagonalDecodeBHist C)
                                                      (cauchyModulusDiagonalDecodeBHist P)
                                                      (cauchyModulusDiagonalDecodeBHist N))
                                              | _ :: _ => none

private theorem cauchyModulusDiagonal_round_trip :
    ∀ x : CauchyModulusDiagonalUp,
      cauchyModulusDiagonalFromEventFlow (cauchyModulusDiagonalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F S Q E M T W H C P N =>
      change
        some
          (CauchyModulusDiagonalUp.mk
            (cauchyModulusDiagonalDecodeBHist (cauchyModulusDiagonalEncodeBHist F))
            (cauchyModulusDiagonalDecodeBHist (cauchyModulusDiagonalEncodeBHist S))
            (cauchyModulusDiagonalDecodeBHist (cauchyModulusDiagonalEncodeBHist Q))
            (cauchyModulusDiagonalDecodeBHist (cauchyModulusDiagonalEncodeBHist E))
            (cauchyModulusDiagonalDecodeBHist (cauchyModulusDiagonalEncodeBHist M))
            (cauchyModulusDiagonalDecodeBHist (cauchyModulusDiagonalEncodeBHist T))
            (cauchyModulusDiagonalDecodeBHist (cauchyModulusDiagonalEncodeBHist W))
            (cauchyModulusDiagonalDecodeBHist (cauchyModulusDiagonalEncodeBHist H))
            (cauchyModulusDiagonalDecodeBHist (cauchyModulusDiagonalEncodeBHist C))
            (cauchyModulusDiagonalDecodeBHist (cauchyModulusDiagonalEncodeBHist P))
            (cauchyModulusDiagonalDecodeBHist (cauchyModulusDiagonalEncodeBHist N))) =
          some (CauchyModulusDiagonalUp.mk F S Q E M T W H C P N)
      rw [cauchyModulusDiagonal_decode_encode_bhist F,
        cauchyModulusDiagonal_decode_encode_bhist S,
        cauchyModulusDiagonal_decode_encode_bhist Q,
        cauchyModulusDiagonal_decode_encode_bhist E,
        cauchyModulusDiagonal_decode_encode_bhist M,
        cauchyModulusDiagonal_decode_encode_bhist T,
        cauchyModulusDiagonal_decode_encode_bhist W,
        cauchyModulusDiagonal_decode_encode_bhist H,
        cauchyModulusDiagonal_decode_encode_bhist C,
        cauchyModulusDiagonal_decode_encode_bhist P,
        cauchyModulusDiagonal_decode_encode_bhist N]

private theorem cauchyModulusDiagonalToEventFlow_injective
    {x y : CauchyModulusDiagonalUp} :
    cauchyModulusDiagonalToEventFlow x = cauchyModulusDiagonalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusDiagonalFromEventFlow (cauchyModulusDiagonalToEventFlow x) =
        cauchyModulusDiagonalFromEventFlow (cauchyModulusDiagonalToEventFlow y) :=
    congrArg cauchyModulusDiagonalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyModulusDiagonal_round_trip x).symm
      (Eq.trans hread (cauchyModulusDiagonal_round_trip y)))

instance cauchyModulusDiagonalBHistCarrier : BHistCarrier CauchyModulusDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusDiagonalToEventFlow
  fromEventFlow := cauchyModulusDiagonalFromEventFlow

instance cauchyModulusDiagonalChapterTasteGate : ChapterTasteGate CauchyModulusDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyModulusDiagonalFromEventFlow (cauchyModulusDiagonalToEventFlow x) = some x
    exact cauchyModulusDiagonal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusDiagonalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyModulusDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusDiagonalChapterTasteGate

theorem CauchyModulusDiagonalTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyModulusDiagonalDecodeBHist (cauchyModulusDiagonalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyModulusDiagonalUp) ∧
        Nonempty (ChapterTasteGate CauchyModulusDiagonalUp) ∧
          cauchyModulusDiagonalFields
              (CauchyModulusDiagonalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyModulusDiagonal_decode_encode_bhist, ⟨cauchyModulusDiagonalBHistCarrier⟩,
      ⟨cauchyModulusDiagonalChapterTasteGate⟩, rfl⟩

end BEDC.Derived.CauchyModulusDiagonalUp
