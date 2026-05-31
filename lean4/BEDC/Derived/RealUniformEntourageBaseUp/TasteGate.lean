import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformEntourageBaseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealUniformEntourageBaseUp : Type where
  | mk (R U B F D S Q H C P N : BHist) : RealUniformEntourageBaseUp
  deriving DecidableEq

def realUniformEntourageBaseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realUniformEntourageBaseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realUniformEntourageBaseEncodeBHist h

def realUniformEntourageBaseDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realUniformEntourageBaseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realUniformEntourageBaseDecodeBHist tail)

private theorem realUniformEntourageBase_decode_encode_bhist :
    ∀ h : BHist,
      realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realUniformEntourageBase_mk_congr
    {R R' U U' B B' F F' D D' S S' Q Q' H H' C C' P P' N N' : BHist}
    (hR : R' = R) (hU : U' = U) (hB : B' = B) (hF : F' = F) (hD : D' = D)
    (hS : S' = S) (hQ : Q' = Q) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    RealUniformEntourageBaseUp.mk R' U' B' F' D' S' Q' H' C' P' N' =
      RealUniformEntourageBaseUp.mk R U B F D S Q H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hU
  cases hB
  cases hF
  cases hD
  cases hS
  cases hQ
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def realUniformEntourageBaseFields : RealUniformEntourageBaseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformEntourageBaseUp.mk R U B F D S Q H C P N => [R, U, B, F, D, S, Q, H, C, P, N]

def realUniformEntourageBaseToEventFlow : RealUniformEntourageBaseUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realUniformEntourageBaseFields x).map realUniformEntourageBaseEncodeBHist

private def realUniformEntourageBaseRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realUniformEntourageBaseRawAt index rest

def realUniformEntourageBaseFromEventFlow (flow : EventFlow) : Option RealUniformEntourageBaseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealUniformEntourageBaseUp.mk
      (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseRawAt 0 flow))
      (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseRawAt 1 flow))
      (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseRawAt 2 flow))
      (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseRawAt 3 flow))
      (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseRawAt 4 flow))
      (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseRawAt 5 flow))
      (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseRawAt 6 flow))
      (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseRawAt 7 flow))
      (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseRawAt 8 flow))
      (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseRawAt 9 flow))
      (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseRawAt 10 flow)))

private theorem realUniformEntourageBase_round_trip :
    ∀ x : RealUniformEntourageBaseUp,
      realUniformEntourageBaseFromEventFlow (realUniformEntourageBaseToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R U B F D S Q H C P N =>
      change
        some
          (RealUniformEntourageBaseUp.mk
            (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseEncodeBHist R))
            (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseEncodeBHist U))
            (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseEncodeBHist B))
            (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseEncodeBHist F))
            (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseEncodeBHist D))
            (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseEncodeBHist S))
            (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseEncodeBHist Q))
            (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseEncodeBHist H))
            (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseEncodeBHist C))
            (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseEncodeBHist P))
            (realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseEncodeBHist N))) =
          some (RealUniformEntourageBaseUp.mk R U B F D S Q H C P N)
      exact
        congrArg some
          (realUniformEntourageBase_mk_congr
            (realUniformEntourageBase_decode_encode_bhist R)
            (realUniformEntourageBase_decode_encode_bhist U)
            (realUniformEntourageBase_decode_encode_bhist B)
            (realUniformEntourageBase_decode_encode_bhist F)
            (realUniformEntourageBase_decode_encode_bhist D)
            (realUniformEntourageBase_decode_encode_bhist S)
            (realUniformEntourageBase_decode_encode_bhist Q)
            (realUniformEntourageBase_decode_encode_bhist H)
            (realUniformEntourageBase_decode_encode_bhist C)
            (realUniformEntourageBase_decode_encode_bhist P)
            (realUniformEntourageBase_decode_encode_bhist N))

private theorem realUniformEntourageBaseToEventFlow_injective {x y : RealUniformEntourageBaseUp} :
    realUniformEntourageBaseToEventFlow x = realUniformEntourageBaseToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realUniformEntourageBaseFromEventFlow (realUniformEntourageBaseToEventFlow x) =
        realUniformEntourageBaseFromEventFlow (realUniformEntourageBaseToEventFlow y) :=
    congrArg realUniformEntourageBaseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realUniformEntourageBase_round_trip x).symm
      (Eq.trans hread (realUniformEntourageBase_round_trip y)))

private theorem realUniformEntourageBase_fields_faithful :
    ∀ x y : RealUniformEntourageBaseUp,
      realUniformEntourageBaseFields x = realUniformEntourageBaseFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ U₁ B₁ F₁ D₁ S₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ U₂ B₂ F₂ D₂ S₂ Q₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hR tail0
          injection tail0 with hU tail1
          injection tail1 with hB tail2
          injection tail2 with hF tail3
          injection tail3 with hD tail4
          injection tail4 with hS tail5
          injection tail5 with hQ tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hR
          subst hU
          subst hB
          subst hF
          subst hD
          subst hS
          subst hQ
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance realUniformEntourageBaseBHistCarrier : BHistCarrier RealUniformEntourageBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realUniformEntourageBaseToEventFlow
  fromEventFlow := realUniformEntourageBaseFromEventFlow

instance realUniformEntourageBaseChapterTasteGate : ChapterTasteGate RealUniformEntourageBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realUniformEntourageBaseFromEventFlow (realUniformEntourageBaseToEventFlow x) =
      some x
    exact realUniformEntourageBase_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realUniformEntourageBaseToEventFlow_injective heq)

instance realUniformEntourageBaseFieldFaithful : FieldFaithful RealUniformEntourageBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realUniformEntourageBaseFields
  field_faithful := realUniformEntourageBase_fields_faithful

def taste_gate : ChapterTasteGate RealUniformEntourageBaseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realUniformEntourageBaseChapterTasteGate

theorem RealUniformEntourageBaseTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realUniformEntourageBaseDecodeBHist (realUniformEntourageBaseEncodeBHist h) = h) ∧
      (∀ x : RealUniformEntourageBaseUp,
        realUniformEntourageBaseFromEventFlow (realUniformEntourageBaseToEventFlow x) =
          some x) ∧
        (∀ x y : RealUniformEntourageBaseUp,
          realUniformEntourageBaseToEventFlow x = realUniformEntourageBaseToEventFlow y →
            x = y) ∧
          realUniformEntourageBaseEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realUniformEntourageBase_decode_encode_bhist
  · constructor
    · exact realUniformEntourageBase_round_trip
    · constructor
      · intro x y heq
        exact realUniformEntourageBaseToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealUniformEntourageBaseUp
