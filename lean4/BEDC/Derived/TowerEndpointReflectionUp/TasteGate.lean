import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TowerEndpointReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TowerEndpointReflectionUp : Type where
  | packet (E S K Q F D O H C P N : BHist) : TowerEndpointReflectionUp
  deriving DecidableEq

def towerEndpointReflectionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: towerEndpointReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: towerEndpointReflectionEncodeBHist h

def towerEndpointReflectionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (towerEndpointReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (towerEndpointReflectionDecodeBHist tail)

private theorem towerEndpointReflectionDecode_encode_bhist :
    ∀ h : BHist,
      towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def towerEndpointReflectionFields : TowerEndpointReflectionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TowerEndpointReflectionUp.packet E S K Q F D O H C P N =>
      [E, S, K, Q, F, D, O, H, C, P, N]

def towerEndpointReflectionToEventFlow : TowerEndpointReflectionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TowerEndpointReflectionUp.packet E S K Q F D O H C P N =>
      [[BMark.b0], towerEndpointReflectionEncodeBHist E,
        [BMark.b1, BMark.b0], towerEndpointReflectionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0], towerEndpointReflectionEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], towerEndpointReflectionEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          towerEndpointReflectionEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          towerEndpointReflectionEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          towerEndpointReflectionEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0], towerEndpointReflectionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0], towerEndpointReflectionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0], towerEndpointReflectionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0], towerEndpointReflectionEncodeBHist N]

def towerEndpointReflectionFromEventFlow : EventFlow -> Option TowerEndpointReflectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_t0, E, _t1, S, _t2, K, _t3, Q, _t4, F, _t5, D, _t6, O, _t7, H, _t8, C,
      _t9, P, _t10, N] =>
      some
        (TowerEndpointReflectionUp.packet
          (towerEndpointReflectionDecodeBHist E)
          (towerEndpointReflectionDecodeBHist S)
          (towerEndpointReflectionDecodeBHist K)
          (towerEndpointReflectionDecodeBHist Q)
          (towerEndpointReflectionDecodeBHist F)
          (towerEndpointReflectionDecodeBHist D)
          (towerEndpointReflectionDecodeBHist O)
          (towerEndpointReflectionDecodeBHist H)
          (towerEndpointReflectionDecodeBHist C)
          (towerEndpointReflectionDecodeBHist P)
          (towerEndpointReflectionDecodeBHist N))
  | _ => none

private theorem towerEndpointReflection_round_trip :
    ∀ x : TowerEndpointReflectionUp,
      towerEndpointReflectionFromEventFlow (towerEndpointReflectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | packet E S K Q F D O H C P N =>
      change
        some
          (TowerEndpointReflectionUp.packet
            (towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist E))
            (towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist S))
            (towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist K))
            (towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist Q))
            (towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist F))
            (towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist D))
            (towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist O))
            (towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist H))
            (towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist C))
            (towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist P))
            (towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist N))) =
          some (TowerEndpointReflectionUp.packet E S K Q F D O H C P N)
      rw [towerEndpointReflectionDecode_encode_bhist E,
        towerEndpointReflectionDecode_encode_bhist S,
        towerEndpointReflectionDecode_encode_bhist K,
        towerEndpointReflectionDecode_encode_bhist Q,
        towerEndpointReflectionDecode_encode_bhist F,
        towerEndpointReflectionDecode_encode_bhist D,
        towerEndpointReflectionDecode_encode_bhist O,
        towerEndpointReflectionDecode_encode_bhist H,
        towerEndpointReflectionDecode_encode_bhist C,
        towerEndpointReflectionDecode_encode_bhist P,
        towerEndpointReflectionDecode_encode_bhist N]

private theorem towerEndpointReflectionToEventFlow_injective {x y : TowerEndpointReflectionUp} :
    towerEndpointReflectionToEventFlow x = towerEndpointReflectionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      towerEndpointReflectionFromEventFlow (towerEndpointReflectionToEventFlow x) =
        towerEndpointReflectionFromEventFlow (towerEndpointReflectionToEventFlow y) :=
    congrArg towerEndpointReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (towerEndpointReflection_round_trip x).symm
      (Eq.trans hread (towerEndpointReflection_round_trip y)))

private theorem towerEndpointReflectionFields_faithful :
    ∀ x y : TowerEndpointReflectionUp,
      towerEndpointReflectionFields x = towerEndpointReflectionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | packet E S K Q F D O H C P N =>
      cases y with
      | packet E' S' K' Q' F' D' O' H' C' P' N' =>
          injection hfields with hE t1
          injection t1 with hS t2
          injection t2 with hK t3
          injection t3 with hQ t4
          injection t4 with hF t5
          injection t5 with hD t6
          injection t6 with hO t7
          injection t7 with hH t8
          injection t8 with hC t9
          injection t9 with hP t10
          injection t10 with hN _
          cases hE
          cases hS
          cases hK
          cases hQ
          cases hF
          cases hD
          cases hO
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance towerEndpointReflectionBHistCarrier : BHistCarrier TowerEndpointReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := towerEndpointReflectionToEventFlow
  fromEventFlow := towerEndpointReflectionFromEventFlow

instance towerEndpointReflectionChapterTasteGate :
    ChapterTasteGate TowerEndpointReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      towerEndpointReflectionFromEventFlow (towerEndpointReflectionToEventFlow x) = some x
    exact towerEndpointReflection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (towerEndpointReflectionToEventFlow_injective heq)

instance towerEndpointReflectionFieldFaithful : FieldFaithful TowerEndpointReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := towerEndpointReflectionFields
  field_faithful := towerEndpointReflectionFields_faithful

instance towerEndpointReflectionNontrivial : Nontrivial TowerEndpointReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TowerEndpointReflectionUp.packet BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TowerEndpointReflectionUp.packet (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TowerEndpointReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  towerEndpointReflectionChapterTasteGate

end BEDC.Derived.TowerEndpointReflectionUp
