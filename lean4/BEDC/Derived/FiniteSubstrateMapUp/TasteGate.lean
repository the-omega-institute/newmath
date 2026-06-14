import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSubstrateMapUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSubstrateMapUp : Type where
  | mk (B E S W L O M H C P N : BHist) : FiniteSubstrateMapUp
  deriving DecidableEq

def finiteSubstrateMapEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSubstrateMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSubstrateMapEncodeBHist h

def finiteSubstrateMapDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSubstrateMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSubstrateMapDecodeBHist tail)

theorem finiteSubstrateMap_decode_encode :
    forall h : BHist, finiteSubstrateMapDecodeBHist (finiteSubstrateMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteSubstrateMapFields : FiniteSubstrateMapUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSubstrateMapUp.mk B E S W L O M H C P N => [B, E, S, W, L, O, M, H, C, P, N]

def finiteSubstrateMapToEventFlow : FiniteSubstrateMapUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteSubstrateMapFields x).map finiteSubstrateMapEncodeBHist

def finiteSubstrateMapFromEventFlow : EventFlow -> Option FiniteSubstrateMapUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | B :: rest0 =>
      match rest0 with
      | [] => none
      | E :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | O :: rest5 =>
                          match rest5 with
                          | [] => none
                          | M :: rest6 =>
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
                                                    (FiniteSubstrateMapUp.mk
                                                      (finiteSubstrateMapDecodeBHist B)
                                                      (finiteSubstrateMapDecodeBHist E)
                                                      (finiteSubstrateMapDecodeBHist S)
                                                      (finiteSubstrateMapDecodeBHist W)
                                                      (finiteSubstrateMapDecodeBHist L)
                                                      (finiteSubstrateMapDecodeBHist O)
                                                      (finiteSubstrateMapDecodeBHist M)
                                                      (finiteSubstrateMapDecodeBHist H)
                                                      (finiteSubstrateMapDecodeBHist C)
                                                      (finiteSubstrateMapDecodeBHist P)
                                                      (finiteSubstrateMapDecodeBHist N))
                                              | _ :: _ => none

theorem finiteSubstrateMap_round_trip :
    forall x : FiniteSubstrateMapUp,
      finiteSubstrateMapFromEventFlow (finiteSubstrateMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B E S W L O M H C P N =>
      change
        some
          (FiniteSubstrateMapUp.mk
            (finiteSubstrateMapDecodeBHist (finiteSubstrateMapEncodeBHist B))
            (finiteSubstrateMapDecodeBHist (finiteSubstrateMapEncodeBHist E))
            (finiteSubstrateMapDecodeBHist (finiteSubstrateMapEncodeBHist S))
            (finiteSubstrateMapDecodeBHist (finiteSubstrateMapEncodeBHist W))
            (finiteSubstrateMapDecodeBHist (finiteSubstrateMapEncodeBHist L))
            (finiteSubstrateMapDecodeBHist (finiteSubstrateMapEncodeBHist O))
            (finiteSubstrateMapDecodeBHist (finiteSubstrateMapEncodeBHist M))
            (finiteSubstrateMapDecodeBHist (finiteSubstrateMapEncodeBHist H))
            (finiteSubstrateMapDecodeBHist (finiteSubstrateMapEncodeBHist C))
            (finiteSubstrateMapDecodeBHist (finiteSubstrateMapEncodeBHist P))
            (finiteSubstrateMapDecodeBHist (finiteSubstrateMapEncodeBHist N))) =
          some (FiniteSubstrateMapUp.mk B E S W L O M H C P N)
      rw [finiteSubstrateMap_decode_encode B, finiteSubstrateMap_decode_encode E,
        finiteSubstrateMap_decode_encode S, finiteSubstrateMap_decode_encode W,
        finiteSubstrateMap_decode_encode L, finiteSubstrateMap_decode_encode O,
        finiteSubstrateMap_decode_encode M, finiteSubstrateMap_decode_encode H,
        finiteSubstrateMap_decode_encode C, finiteSubstrateMap_decode_encode P,
        finiteSubstrateMap_decode_encode N]

theorem finiteSubstrateMapToEventFlow_injective {x y : FiniteSubstrateMapUp} :
    finiteSubstrateMapToEventFlow x = finiteSubstrateMapToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSubstrateMapFromEventFlow (finiteSubstrateMapToEventFlow x) =
        finiteSubstrateMapFromEventFlow (finiteSubstrateMapToEventFlow y) :=
    congrArg finiteSubstrateMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteSubstrateMap_round_trip x).symm
      (Eq.trans hread (finiteSubstrateMap_round_trip y)))

theorem finiteSubstrateMap_field_faithful :
    forall x y : FiniteSubstrateMapUp, finiteSubstrateMapFields x = finiteSubstrateMapFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 E1 S1 W1 L1 O1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 E2 S2 W2 L2 O2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteSubstrateMapBHistCarrier : BHistCarrier FiniteSubstrateMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSubstrateMapToEventFlow
  fromEventFlow := finiteSubstrateMapFromEventFlow

instance finiteSubstrateMapChapterTasteGate : ChapterTasteGate FiniteSubstrateMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => finiteSubstrateMap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteSubstrateMapToEventFlow_injective heq)

instance finiteSubstrateMapFieldFaithful : FieldFaithful FiniteSubstrateMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteSubstrateMapFields
  field_faithful := finiteSubstrateMap_field_faithful

instance finiteSubstrateMapNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteSubstrateMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteSubstrateMapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteSubstrateMapUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteSubstrateMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteSubstrateMapChapterTasteGate

theorem FiniteSubstrateMapTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteSubstrateMapDecodeBHist (finiteSubstrateMapEncodeBHist h) = h) ∧
      (∀ x : FiniteSubstrateMapUp,
        finiteSubstrateMapFromEventFlow (finiteSubstrateMapToEventFlow x) = some x) ∧
        (∀ x y : FiniteSubstrateMapUp,
          finiteSubstrateMapToEventFlow x = finiteSubstrateMapToEventFlow y -> x = y) ∧
          finiteSubstrateMapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨finiteSubstrateMap_decode_encode, finiteSubstrateMap_round_trip,
      (fun _ _ heq => finiteSubstrateMapToEventFlow_injective heq), rfl⟩

end BEDC.Derived.FiniteSubstrateMapUp.TasteGate
