import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MinimalTriggerHomologyCoreUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MinimalTriggerHomologyCoreUp : Type where
  | mk (Q F N R B K T H C P L : BHist) : MinimalTriggerHomologyCoreUp
  deriving DecidableEq

def minimalTriggerHomologyCoreEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: minimalTriggerHomologyCoreEncodeBHist h
  | BHist.e1 h => BMark.b1 :: minimalTriggerHomologyCoreEncodeBHist h

def minimalTriggerHomologyCoreDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (minimalTriggerHomologyCoreDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (minimalTriggerHomologyCoreDecodeBHist tail)

theorem MinimalTriggerHomologyCoreNamecertObligations_decode_encode_bhist :
    ∀ h : BHist,
      minimalTriggerHomologyCoreDecodeBHist
          (minimalTriggerHomologyCoreEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem minimalTriggerHomologyCore_mk_congr
    {Q Q' F F' N N' R R' B B' K K' T T' H H' C C' P P' L L' : BHist}
    (hQ : Q' = Q) (hF : F' = F) (hN : N' = N) (hR : R' = R) (hB : B' = B)
    (hK : K' = K) (hT : T' = T) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hL : L' = L) :
    MinimalTriggerHomologyCoreUp.mk Q' F' N' R' B' K' T' H' C' P' L' =
      MinimalTriggerHomologyCoreUp.mk Q F N R B K T H C P L := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hF
  cases hN
  cases hR
  cases hB
  cases hK
  cases hT
  cases hH
  cases hC
  cases hP
  cases hL
  rfl

def minimalTriggerHomologyCoreFields : MinimalTriggerHomologyCoreUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MinimalTriggerHomologyCoreUp.mk Q F N R B K T H C P L =>
      [Q, F, N, R, B, K, T, H, C, P, L]

def minimalTriggerHomologyCoreToEventFlow : MinimalTriggerHomologyCoreUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MinimalTriggerHomologyCoreUp.mk Q F N R B K T H C P L =>
      [[BMark.b0],
        minimalTriggerHomologyCoreEncodeBHist Q,
        [BMark.b1, BMark.b0],
        minimalTriggerHomologyCoreEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b0],
        minimalTriggerHomologyCoreEncodeBHist N,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        minimalTriggerHomologyCoreEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        minimalTriggerHomologyCoreEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        minimalTriggerHomologyCoreEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        minimalTriggerHomologyCoreEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        minimalTriggerHomologyCoreEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        minimalTriggerHomologyCoreEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        minimalTriggerHomologyCoreEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        minimalTriggerHomologyCoreEncodeBHist L]

private def minimalTriggerHomologyCoreEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => minimalTriggerHomologyCoreEventAtDefault index rest

def minimalTriggerHomologyCoreFromEventFlow (ef : EventFlow) : Option MinimalTriggerHomologyCoreUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MinimalTriggerHomologyCoreUp.mk
      (minimalTriggerHomologyCoreDecodeBHist (minimalTriggerHomologyCoreEventAtDefault 1 ef))
      (minimalTriggerHomologyCoreDecodeBHist (minimalTriggerHomologyCoreEventAtDefault 3 ef))
      (minimalTriggerHomologyCoreDecodeBHist (minimalTriggerHomologyCoreEventAtDefault 5 ef))
      (minimalTriggerHomologyCoreDecodeBHist (minimalTriggerHomologyCoreEventAtDefault 7 ef))
      (minimalTriggerHomologyCoreDecodeBHist (minimalTriggerHomologyCoreEventAtDefault 9 ef))
      (minimalTriggerHomologyCoreDecodeBHist (minimalTriggerHomologyCoreEventAtDefault 11 ef))
      (minimalTriggerHomologyCoreDecodeBHist (minimalTriggerHomologyCoreEventAtDefault 13 ef))
      (minimalTriggerHomologyCoreDecodeBHist (minimalTriggerHomologyCoreEventAtDefault 15 ef))
      (minimalTriggerHomologyCoreDecodeBHist (minimalTriggerHomologyCoreEventAtDefault 17 ef))
      (minimalTriggerHomologyCoreDecodeBHist (minimalTriggerHomologyCoreEventAtDefault 19 ef))
      (minimalTriggerHomologyCoreDecodeBHist (minimalTriggerHomologyCoreEventAtDefault 21 ef)))

theorem MinimalTriggerHomologyCoreNamecertObligations_round_trip
    (x : MinimalTriggerHomologyCoreUp) :
    minimalTriggerHomologyCoreFromEventFlow
        (minimalTriggerHomologyCoreToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q F N R B K T H C P L =>
      exact
        congrArg some
          (minimalTriggerHomologyCore_mk_congr
            (MinimalTriggerHomologyCoreNamecertObligations_decode_encode_bhist Q)
            (MinimalTriggerHomologyCoreNamecertObligations_decode_encode_bhist F)
            (MinimalTriggerHomologyCoreNamecertObligations_decode_encode_bhist N)
            (MinimalTriggerHomologyCoreNamecertObligations_decode_encode_bhist R)
            (MinimalTriggerHomologyCoreNamecertObligations_decode_encode_bhist B)
            (MinimalTriggerHomologyCoreNamecertObligations_decode_encode_bhist K)
            (MinimalTriggerHomologyCoreNamecertObligations_decode_encode_bhist T)
            (MinimalTriggerHomologyCoreNamecertObligations_decode_encode_bhist H)
            (MinimalTriggerHomologyCoreNamecertObligations_decode_encode_bhist C)
            (MinimalTriggerHomologyCoreNamecertObligations_decode_encode_bhist P)
            (MinimalTriggerHomologyCoreNamecertObligations_decode_encode_bhist L))

theorem MinimalTriggerHomologyCoreNamecertObligations_toEventFlow_injective
    {x y : MinimalTriggerHomologyCoreUp} :
    minimalTriggerHomologyCoreToEventFlow x = minimalTriggerHomologyCoreToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      minimalTriggerHomologyCoreFromEventFlow (minimalTriggerHomologyCoreToEventFlow x) =
        minimalTriggerHomologyCoreFromEventFlow (minimalTriggerHomologyCoreToEventFlow y) :=
    congrArg minimalTriggerHomologyCoreFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MinimalTriggerHomologyCoreNamecertObligations_round_trip x).symm
      (Eq.trans hread (MinimalTriggerHomologyCoreNamecertObligations_round_trip y)))

theorem MinimalTriggerHomologyCoreNamecertObligations_field_faithful
    (x y : MinimalTriggerHomologyCoreUp) :
    minimalTriggerHomologyCoreFields x = minimalTriggerHomologyCoreFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  cases x with
  | mk Q F N R B K T H C P L =>
      cases y with
      | mk Q' F' N' R' B' K' T' H' C' P' L' =>
          cases hfields
          rfl

instance minimalTriggerHomologyCoreBHistCarrier : BHistCarrier MinimalTriggerHomologyCoreUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := minimalTriggerHomologyCoreToEventFlow
  fromEventFlow := minimalTriggerHomologyCoreFromEventFlow

instance minimalTriggerHomologyCoreChapterTasteGate :
    ChapterTasteGate MinimalTriggerHomologyCoreUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      minimalTriggerHomologyCoreFromEventFlow (minimalTriggerHomologyCoreToEventFlow x) =
        some x
    exact MinimalTriggerHomologyCoreNamecertObligations_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MinimalTriggerHomologyCoreNamecertObligations_toEventFlow_injective heq)

instance minimalTriggerHomologyCoreFieldFaithful :
    FieldFaithful MinimalTriggerHomologyCoreUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := minimalTriggerHomologyCoreFields
  field_faithful := MinimalTriggerHomologyCoreNamecertObligations_field_faithful

instance minimalTriggerHomologyCoreNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MinimalTriggerHomologyCoreUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MinimalTriggerHomologyCoreUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MinimalTriggerHomologyCoreUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def MinimalTriggerHomologyCoreNamecertObligations_taste_gate :
    ChapterTasteGate MinimalTriggerHomologyCoreUp :=
  -- BEDC touchpoint anchor: BHist BMark
  minimalTriggerHomologyCoreChapterTasteGate

end BEDC.Derived.MinimalTriggerHomologyCoreUp
