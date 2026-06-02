import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructivePolishSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructivePolishSpaceUp : Type where
  | mk (M S D W Q R L H C G N : BHist) : ConstructivePolishSpaceUp

def constructivePolishSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructivePolishSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructivePolishSpaceEncodeBHist h

def constructivePolishSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructivePolishSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructivePolishSpaceDecodeBHist tail)

private theorem constructivePolishSpace_decode_encode_bhist :
    ∀ h : BHist, constructivePolishSpaceDecodeBHist (constructivePolishSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem constructivePolishSpaceEncodeBHist_injective {h k : BHist} :
    constructivePolishSpaceEncodeBHist h = constructivePolishSpaceEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      constructivePolishSpaceDecodeBHist (constructivePolishSpaceEncodeBHist h) =
        constructivePolishSpaceDecodeBHist (constructivePolishSpaceEncodeBHist k) :=
    congrArg constructivePolishSpaceDecodeBHist heq
  exact
    Eq.trans (constructivePolishSpace_decode_encode_bhist h).symm
      (Eq.trans hdecode (constructivePolishSpace_decode_encode_bhist k))

private theorem constructivePolishSpace_mk_congr
    {M M' S S' D D' W W' Q Q' R R' L L' H H' C C' G G' N N' : BHist}
    (hM : M' = M) (hS : S' = S) (hD : D' = D) (hW : W' = W) (hQ : Q' = Q)
    (hR : R' = R) (hL : L' = L) (hH : H' = H) (hC : C' = C) (hG : G' = G)
    (hN : N' = N) :
    ConstructivePolishSpaceUp.mk M' S' D' W' Q' R' L' H' C' G' N' =
      ConstructivePolishSpaceUp.mk M S D W Q R L H C G N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hS
  cases hD
  cases hW
  cases hQ
  cases hR
  cases hL
  cases hH
  cases hC
  cases hG
  cases hN
  rfl

def constructivePolishSpaceToEventFlow : ConstructivePolishSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructivePolishSpaceUp.mk M S D W Q R L H C G N =>
      [constructivePolishSpaceEncodeBHist M, constructivePolishSpaceEncodeBHist S,
        constructivePolishSpaceEncodeBHist D, constructivePolishSpaceEncodeBHist W,
        constructivePolishSpaceEncodeBHist Q, constructivePolishSpaceEncodeBHist R,
        constructivePolishSpaceEncodeBHist L, constructivePolishSpaceEncodeBHist H,
        constructivePolishSpaceEncodeBHist C, constructivePolishSpaceEncodeBHist G,
        constructivePolishSpaceEncodeBHist N]

private def constructivePolishSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructivePolishSpaceEventAtDefault index rest

def constructivePolishSpaceFromEventFlow (ef : EventFlow) : Option ConstructivePolishSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructivePolishSpaceUp.mk
      (constructivePolishSpaceDecodeBHist (constructivePolishSpaceEventAtDefault 0 ef))
      (constructivePolishSpaceDecodeBHist (constructivePolishSpaceEventAtDefault 1 ef))
      (constructivePolishSpaceDecodeBHist (constructivePolishSpaceEventAtDefault 2 ef))
      (constructivePolishSpaceDecodeBHist (constructivePolishSpaceEventAtDefault 3 ef))
      (constructivePolishSpaceDecodeBHist (constructivePolishSpaceEventAtDefault 4 ef))
      (constructivePolishSpaceDecodeBHist (constructivePolishSpaceEventAtDefault 5 ef))
      (constructivePolishSpaceDecodeBHist (constructivePolishSpaceEventAtDefault 6 ef))
      (constructivePolishSpaceDecodeBHist (constructivePolishSpaceEventAtDefault 7 ef))
      (constructivePolishSpaceDecodeBHist (constructivePolishSpaceEventAtDefault 8 ef))
      (constructivePolishSpaceDecodeBHist (constructivePolishSpaceEventAtDefault 9 ef))
      (constructivePolishSpaceDecodeBHist (constructivePolishSpaceEventAtDefault 10 ef)))

private theorem constructivePolishSpace_round_trip :
    ∀ x : ConstructivePolishSpaceUp,
      constructivePolishSpaceFromEventFlow (constructivePolishSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S D W Q R L H C G N =>
      exact
        congrArg some
          (constructivePolishSpace_mk_congr
            (constructivePolishSpace_decode_encode_bhist M)
            (constructivePolishSpace_decode_encode_bhist S)
            (constructivePolishSpace_decode_encode_bhist D)
            (constructivePolishSpace_decode_encode_bhist W)
            (constructivePolishSpace_decode_encode_bhist Q)
            (constructivePolishSpace_decode_encode_bhist R)
            (constructivePolishSpace_decode_encode_bhist L)
            (constructivePolishSpace_decode_encode_bhist H)
            (constructivePolishSpace_decode_encode_bhist C)
            (constructivePolishSpace_decode_encode_bhist G)
            (constructivePolishSpace_decode_encode_bhist N))

private theorem constructivePolishSpaceToEventFlow_injective {x y : ConstructivePolishSpaceUp} :
    constructivePolishSpaceToEventFlow x = constructivePolishSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk M S D W Q R L H C G N =>
      cases y with
      | mk M' S' D' W' Q' R' L' H' C' G' N' =>
          injection heq with MEq tailEq1
          injection tailEq1 with SEq tailEq2
          injection tailEq2 with DEq tailEq3
          injection tailEq3 with WEq tailEq4
          injection tailEq4 with QEq tailEq5
          injection tailEq5 with REq tailEq6
          injection tailEq6 with LEq tailEq7
          injection tailEq7 with HEq tailEq8
          injection tailEq8 with CEq tailEq9
          injection tailEq9 with GEq tailEq10
          injection tailEq10 with NEq _nilEq
          exact
            constructivePolishSpace_mk_congr
              (constructivePolishSpaceEncodeBHist_injective MEq)
              (constructivePolishSpaceEncodeBHist_injective SEq)
              (constructivePolishSpaceEncodeBHist_injective DEq)
              (constructivePolishSpaceEncodeBHist_injective WEq)
              (constructivePolishSpaceEncodeBHist_injective QEq)
              (constructivePolishSpaceEncodeBHist_injective REq)
              (constructivePolishSpaceEncodeBHist_injective LEq)
              (constructivePolishSpaceEncodeBHist_injective HEq)
              (constructivePolishSpaceEncodeBHist_injective CEq)
              (constructivePolishSpaceEncodeBHist_injective GEq)
              (constructivePolishSpaceEncodeBHist_injective NEq)

instance constructivePolishSpaceBHistCarrier : BHistCarrier ConstructivePolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructivePolishSpaceToEventFlow
  fromEventFlow := constructivePolishSpaceFromEventFlow

instance constructivePolishSpaceChapterTasteGate :
    ChapterTasteGate ConstructivePolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructivePolishSpaceFromEventFlow (constructivePolishSpaceToEventFlow x) = some x
    exact constructivePolishSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (constructivePolishSpaceToEventFlow_injective heq)

theorem ConstructivePolishSpaceTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier ConstructivePolishSpaceUp,
      Nonempty (@ChapterTasteGate ConstructivePolishSpaceUp carrier)) ∧
        (∀ h : BHist,
          constructivePolishSpaceDecodeBHist (constructivePolishSpaceEncodeBHist h) = h) ∧
          (∀ x : ConstructivePolishSpaceUp,
            constructivePolishSpaceFromEventFlow (constructivePolishSpaceToEventFlow x) = some x) ∧
            constructivePolishSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  let carrier : BHistCarrier ConstructivePolishSpaceUp :=
    { toEventFlow := constructivePolishSpaceToEventFlow
      fromEventFlow := constructivePolishSpaceFromEventFlow }
  let gate : @ChapterTasteGate ConstructivePolishSpaceUp carrier :=
    { round_trip := by
        intro x
        exact constructivePolishSpace_round_trip x
      layer_separation := by
        intro x y hxy heq
        exact hxy (constructivePolishSpaceToEventFlow_injective heq) }
  exact
    ⟨⟨carrier, ⟨gate⟩⟩, constructivePolishSpace_decode_encode_bhist,
      constructivePolishSpace_round_trip, rfl⟩

end BEDC.Derived.ConstructivePolishSpaceUp
