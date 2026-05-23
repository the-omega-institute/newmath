import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialContinuityUp : Type where
  | mk (MX MY F S L WX WY RX RY EX EY H C P N : BHist) : SequentialContinuityUp
  deriving DecidableEq

def sequentialContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialContinuityEncodeBHist h

def sequentialContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialContinuityDecodeBHist tail)

private theorem sequentialContinuityDecode_encode_bhist :
    ∀ h : BHist,
      sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem sequentialContinuity_mk_congr
    {MX MX' MY MY' F F' S S' L L' WX WX' WY WY' RX RX' RY RY' EX EX' EY EY'
      H H' C C' P P' N N' : BHist}
    (hMX : MX' = MX)
    (hMY : MY' = MY)
    (hF : F' = F)
    (hS : S' = S)
    (hL : L' = L)
    (hWX : WX' = WX)
    (hWY : WY' = WY)
    (hRX : RX' = RX)
    (hRY : RY' = RY)
    (hEX : EX' = EX)
    (hEY : EY' = EY)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    SequentialContinuityUp.mk MX' MY' F' S' L' WX' WY' RX' RY' EX' EY' H' C' P' N' =
      SequentialContinuityUp.mk MX MY F S L WX WY RX RY EX EY H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMX
  cases hMY
  cases hF
  cases hS
  cases hL
  cases hWX
  cases hWY
  cases hRX
  cases hRY
  cases hEX
  cases hEY
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def sequentialContinuityToEventFlow : SequentialContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialContinuityUp.mk MX MY F S L WX WY RX RY EX EY H C P N =>
      [sequentialContinuityEncodeBHist MX,
        sequentialContinuityEncodeBHist MY,
        sequentialContinuityEncodeBHist F,
        sequentialContinuityEncodeBHist S,
        sequentialContinuityEncodeBHist L,
        sequentialContinuityEncodeBHist WX,
        sequentialContinuityEncodeBHist WY,
        sequentialContinuityEncodeBHist RX,
        sequentialContinuityEncodeBHist RY,
        sequentialContinuityEncodeBHist EX,
        sequentialContinuityEncodeBHist EY,
        sequentialContinuityEncodeBHist H,
        sequentialContinuityEncodeBHist C,
        sequentialContinuityEncodeBHist P,
        sequentialContinuityEncodeBHist N]

def sequentialContinuityFromEventFlow : EventFlow → Option SequentialContinuityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | MX :: rest0 =>
      match rest0 with
      | [] => none
      | MY :: rest1 =>
          match rest1 with
          | [] => none
          | F :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | WX :: rest5 =>
                          match rest5 with
                          | [] => none
                          | WY :: rest6 =>
                              match rest6 with
                              | [] => none
                              | RX :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | RY :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | EX :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | EY :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | C :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | P :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | N :: rest14 =>
                                                              match rest14 with
                                                              | [] =>
                                                                  some
                                                                    (SequentialContinuityUp.mk
                                                                      (sequentialContinuityDecodeBHist MX)
                                                                      (sequentialContinuityDecodeBHist MY)
                                                                      (sequentialContinuityDecodeBHist F)
                                                                      (sequentialContinuityDecodeBHist S)
                                                                      (sequentialContinuityDecodeBHist L)
                                                                      (sequentialContinuityDecodeBHist WX)
                                                                      (sequentialContinuityDecodeBHist WY)
                                                                      (sequentialContinuityDecodeBHist RX)
                                                                      (sequentialContinuityDecodeBHist RY)
                                                                      (sequentialContinuityDecodeBHist EX)
                                                                      (sequentialContinuityDecodeBHist EY)
                                                                      (sequentialContinuityDecodeBHist H)
                                                                      (sequentialContinuityDecodeBHist C)
                                                                      (sequentialContinuityDecodeBHist P)
                                                                      (sequentialContinuityDecodeBHist N))
                                                              | _ :: _ => none

private theorem sequentialContinuity_round_trip :
    ∀ x : SequentialContinuityUp,
      sequentialContinuityFromEventFlow (sequentialContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk MX MY F S L WX WY RX RY EX EY H C P N =>
      change
        some
          (SequentialContinuityUp.mk
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist MX))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist MY))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist F))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist S))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist L))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist WX))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist WY))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist RX))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist RY))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist EX))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist EY))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist H))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist C))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist P))
            (sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist N))) =
          some (SequentialContinuityUp.mk MX MY F S L WX WY RX RY EX EY H C P N)
      exact
        congrArg some
          (sequentialContinuity_mk_congr
            (sequentialContinuityDecode_encode_bhist MX)
            (sequentialContinuityDecode_encode_bhist MY)
            (sequentialContinuityDecode_encode_bhist F)
            (sequentialContinuityDecode_encode_bhist S)
            (sequentialContinuityDecode_encode_bhist L)
            (sequentialContinuityDecode_encode_bhist WX)
            (sequentialContinuityDecode_encode_bhist WY)
            (sequentialContinuityDecode_encode_bhist RX)
            (sequentialContinuityDecode_encode_bhist RY)
            (sequentialContinuityDecode_encode_bhist EX)
            (sequentialContinuityDecode_encode_bhist EY)
            (sequentialContinuityDecode_encode_bhist H)
            (sequentialContinuityDecode_encode_bhist C)
            (sequentialContinuityDecode_encode_bhist P)
            (sequentialContinuityDecode_encode_bhist N))

private theorem sequentialContinuityToEventFlow_injective
    {x y : SequentialContinuityUp} :
    sequentialContinuityToEventFlow x = sequentialContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialContinuityFromEventFlow (sequentialContinuityToEventFlow x) =
        sequentialContinuityFromEventFlow (sequentialContinuityToEventFlow y) :=
    congrArg sequentialContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sequentialContinuity_round_trip x).symm
      (Eq.trans hread (sequentialContinuity_round_trip y)))

instance sequentialContinuityBHistCarrier : BHistCarrier SequentialContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialContinuityToEventFlow
  fromEventFlow := sequentialContinuityFromEventFlow

instance sequentialContinuityChapterTasteGate : ChapterTasteGate SequentialContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sequentialContinuityFromEventFlow (sequentialContinuityToEventFlow x) = some x
    exact sequentialContinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sequentialContinuityToEventFlow_injective heq)

theorem SequentialContinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      sequentialContinuityDecodeBHist (sequentialContinuityEncodeBHist h) = h) ∧
      (∀ (x : SequentialContinuityUp) w m,
        List.Mem w (sequentialContinuityToEventFlow x) → List.Mem m w →
          m = BMark.b0 ∨ m = BMark.b1) ∧
        sequentialContinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact sequentialContinuityDecode_encode_bhist
  · constructor
    · intro x w m _hmFlow hm
      cases m with
      | b0 =>
          exact Or.inl rfl
      | b1 =>
          exact Or.inr rfl
    · rfl

end BEDC.Derived.SequentialContinuityUp
