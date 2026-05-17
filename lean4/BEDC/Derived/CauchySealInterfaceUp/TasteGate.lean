import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySealInterfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySealInterfaceUp : Type where
  | mk : (L Q B T R D E H C P N : BHist) → CauchySealInterfaceUp
  deriving DecidableEq

def cauchySealInterfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySealInterfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySealInterfaceEncodeBHist h

def cauchySealInterfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySealInterfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySealInterfaceDecodeBHist tail)

private theorem cauchySealInterfaceDecode_encode_bhist :
    ∀ h : BHist,
      cauchySealInterfaceDecodeBHist (cauchySealInterfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchySealInterface_mk_congr
    {L L' Q Q' B B' T T' R R' D D' E E' H H' C C' P P' N N' : BHist}
    (hL : L' = L) (hQ : Q' = Q) (hB : B' = B) (hT : T' = T) (hR : R' = R)
    (hD : D' = D) (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    CauchySealInterfaceUp.mk L' Q' B' T' R' D' E' H' C' P' N' =
      CauchySealInterfaceUp.mk L Q B T R D E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hL
  cases hQ
  cases hB
  cases hT
  cases hR
  cases hD
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchySealInterfaceToEventFlow : CauchySealInterfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySealInterfaceUp.mk L Q B T R D E H C P N =>
      [[BMark.b0],
        cauchySealInterfaceEncodeBHist L,
        [BMark.b1, BMark.b0],
        cauchySealInterfaceEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchySealInterfaceEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySealInterfaceEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySealInterfaceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySealInterfaceEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySealInterfaceEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchySealInterfaceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchySealInterfaceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchySealInterfaceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySealInterfaceEncodeBHist N]

private def cauchySealInterfaceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cauchySealInterfaceRawAt n rest

private def cauchySealInterfaceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cauchySealInterfaceLengthEq n rest

def cauchySealInterfaceFromEventFlow : EventFlow → Option CauchySealInterfaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match cauchySealInterfaceLengthEq 22 flow with
      | true =>
      some (CauchySealInterfaceUp.mk
        (cauchySealInterfaceDecodeBHist (cauchySealInterfaceRawAt 1 flow))
        (cauchySealInterfaceDecodeBHist (cauchySealInterfaceRawAt 3 flow))
        (cauchySealInterfaceDecodeBHist (cauchySealInterfaceRawAt 5 flow))
        (cauchySealInterfaceDecodeBHist (cauchySealInterfaceRawAt 7 flow))
        (cauchySealInterfaceDecodeBHist (cauchySealInterfaceRawAt 9 flow))
        (cauchySealInterfaceDecodeBHist (cauchySealInterfaceRawAt 11 flow))
        (cauchySealInterfaceDecodeBHist (cauchySealInterfaceRawAt 13 flow))
        (cauchySealInterfaceDecodeBHist (cauchySealInterfaceRawAt 15 flow))
        (cauchySealInterfaceDecodeBHist (cauchySealInterfaceRawAt 17 flow))
        (cauchySealInterfaceDecodeBHist (cauchySealInterfaceRawAt 19 flow))
        (cauchySealInterfaceDecodeBHist (cauchySealInterfaceRawAt 21 flow)))
      | false => none

private theorem cauchySealInterface_round_trip :
    ∀ x : CauchySealInterfaceUp,
      cauchySealInterfaceFromEventFlow (cauchySealInterfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L Q B T R D E H C P N =>
      change
        some
          (CauchySealInterfaceUp.mk
            (cauchySealInterfaceDecodeBHist (cauchySealInterfaceEncodeBHist L))
            (cauchySealInterfaceDecodeBHist (cauchySealInterfaceEncodeBHist Q))
            (cauchySealInterfaceDecodeBHist (cauchySealInterfaceEncodeBHist B))
            (cauchySealInterfaceDecodeBHist (cauchySealInterfaceEncodeBHist T))
            (cauchySealInterfaceDecodeBHist (cauchySealInterfaceEncodeBHist R))
            (cauchySealInterfaceDecodeBHist (cauchySealInterfaceEncodeBHist D))
            (cauchySealInterfaceDecodeBHist (cauchySealInterfaceEncodeBHist E))
            (cauchySealInterfaceDecodeBHist (cauchySealInterfaceEncodeBHist H))
            (cauchySealInterfaceDecodeBHist (cauchySealInterfaceEncodeBHist C))
            (cauchySealInterfaceDecodeBHist (cauchySealInterfaceEncodeBHist P))
            (cauchySealInterfaceDecodeBHist (cauchySealInterfaceEncodeBHist N))) =
          some (CauchySealInterfaceUp.mk L Q B T R D E H C P N)
      exact
        congrArg some
          (cauchySealInterface_mk_congr
            (cauchySealInterfaceDecode_encode_bhist L)
            (cauchySealInterfaceDecode_encode_bhist Q)
            (cauchySealInterfaceDecode_encode_bhist B)
            (cauchySealInterfaceDecode_encode_bhist T)
            (cauchySealInterfaceDecode_encode_bhist R)
            (cauchySealInterfaceDecode_encode_bhist D)
            (cauchySealInterfaceDecode_encode_bhist E)
            (cauchySealInterfaceDecode_encode_bhist H)
            (cauchySealInterfaceDecode_encode_bhist C)
            (cauchySealInterfaceDecode_encode_bhist P)
            (cauchySealInterfaceDecode_encode_bhist N))

private theorem cauchySealInterfaceToEventFlow_injective {x y : CauchySealInterfaceUp} :
    cauchySealInterfaceToEventFlow x = cauchySealInterfaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySealInterfaceFromEventFlow (cauchySealInterfaceToEventFlow x) =
        cauchySealInterfaceFromEventFlow (cauchySealInterfaceToEventFlow y) :=
    congrArg cauchySealInterfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySealInterface_round_trip x).symm
      (Eq.trans hread (cauchySealInterface_round_trip y)))

instance cauchySealInterfaceBHistCarrier : BHistCarrier CauchySealInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySealInterfaceToEventFlow
  fromEventFlow := cauchySealInterfaceFromEventFlow

instance cauchySealInterfaceChapterTasteGate : ChapterTasteGate CauchySealInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySealInterfaceFromEventFlow (cauchySealInterfaceToEventFlow x) = some x
    exact cauchySealInterface_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySealInterfaceToEventFlow_injective heq)

def cauchySealInterfaceFields : CauchySealInterfaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySealInterfaceUp.mk L Q B T R D E H C P N =>
      [L, Q, B, T, R, D, E, H, C, P, N]

private theorem cauchySealInterface_field_faithful_concrete :
    ∀ x y : CauchySealInterfaceUp,
      cauchySealInterfaceFields x = cauchySealInterfaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L Q B T R D E H C P N =>
      cases y with
      | mk L' Q' B' T' R' D' E' H' C' P' N' =>
          injection hfields with hL tail0
          injection tail0 with hQ tail1
          injection tail1 with hB tail2
          injection tail2 with hT tail3
          injection tail3 with hR tail4
          injection tail4 with hD tail5
          injection tail5 with hE tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _hNil
          cases hL
          cases hQ
          cases hB
          cases hT
          cases hR
          cases hD
          cases hE
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance cauchySealInterfaceFieldFaithful : FieldFaithful CauchySealInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySealInterfaceFields
  field_faithful := cauchySealInterface_field_faithful_concrete

private def cauchySealInterface_nontrivial_witness :
    Σ' (x : CauchySealInterfaceUp) (y : CauchySealInterfaceUp), x ≠ y :=
  ⟨CauchySealInterfaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    CauchySealInterfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    by
      -- BEDC touchpoint anchor: BHist BMark
      intro h
      cases h⟩

instance cauchySealInterfaceNontrivial : Nontrivial CauchySealInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair := cauchySealInterface_nontrivial_witness

theorem CauchySealInterfaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchySealInterfaceDecodeBHist (cauchySealInterfaceEncodeBHist h) = h) ∧
      (∀ x : CauchySealInterfaceUp,
        cauchySealInterfaceFromEventFlow (cauchySealInterfaceToEventFlow x) = some x) ∧
        (∀ x y : CauchySealInterfaceUp,
          cauchySealInterfaceToEventFlow x = cauchySealInterfaceToEventFlow y → x = y) ∧
          cauchySealInterfaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchySealInterfaceDecode_encode_bhist
  · constructor
    · exact cauchySealInterface_round_trip
    · constructor
      · intro x y heq
        exact cauchySealInterfaceToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchySealInterfaceUp
