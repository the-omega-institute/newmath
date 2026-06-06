import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContractiveMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContractiveMapUp : Type where
  | mk (X Y f k D G S H C P N : BHist) : ContractiveMapUp
  deriving DecidableEq

def contractiveMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contractiveMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contractiveMapEncodeBHist h

def contractiveMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contractiveMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contractiveMapDecodeBHist tail)

private theorem ContractiveMapTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, contractiveMapDecodeBHist (contractiveMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contractiveMapFields : ContractiveMapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContractiveMapUp.mk X Y f k D G S H C P N => [X, Y, f, k, D, G, S, H, C, P, N]

def contractiveMapToEventFlow : ContractiveMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (contractiveMapFields x).map contractiveMapEncodeBHist

def contractiveMapFromEventFlow : EventFlow → Option ContractiveMapUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | Y :: restY =>
          match restY with
          | f :: restF =>
              match restF with
              | k :: restK =>
                  match restK with
                  | D :: restD =>
                      match restD with
                      | G :: restG =>
                          match restG with
                          | S :: restS =>
                              match restS with
                              | H :: restH =>
                                  match restH with
                                  | C :: restC =>
                                      match restC with
                                      | P :: restP =>
                                          match restP with
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (ContractiveMapUp.mk
                                                      (contractiveMapDecodeBHist X)
                                                      (contractiveMapDecodeBHist Y)
                                                      (contractiveMapDecodeBHist f)
                                                      (contractiveMapDecodeBHist k)
                                                      (contractiveMapDecodeBHist D)
                                                      (contractiveMapDecodeBHist G)
                                                      (contractiveMapDecodeBHist S)
                                                      (contractiveMapDecodeBHist H)
                                                      (contractiveMapDecodeBHist C)
                                                      (contractiveMapDecodeBHist P)
                                                      (contractiveMapDecodeBHist N))
                                              | _ :: _ => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem contractiveMap_mk_congr
    {X X' Y Y' f f' k k' D D' G G' S S' H H' C C' P P' N N' : BHist}
    (hX : X' = X) (hY : Y' = Y) (hf : f' = f) (hk : k' = k) (hD : D' = D)
    (hG : G' = G) (hS : S' = S) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    ContractiveMapUp.mk X' Y' f' k' D' G' S' H' C' P' N' =
      ContractiveMapUp.mk X Y f k D G S H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hY
  cases hf
  cases hk
  cases hD
  cases hG
  cases hS
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem ContractiveMapTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ContractiveMapUp,
      contractiveMapFromEventFlow (contractiveMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y f k D G S H C P N =>
      exact
        congrArg some
          (contractiveMap_mk_congr
            (ContractiveMapTasteGate_single_carrier_alignment_decode X)
            (ContractiveMapTasteGate_single_carrier_alignment_decode Y)
            (ContractiveMapTasteGate_single_carrier_alignment_decode f)
            (ContractiveMapTasteGate_single_carrier_alignment_decode k)
            (ContractiveMapTasteGate_single_carrier_alignment_decode D)
            (ContractiveMapTasteGate_single_carrier_alignment_decode G)
            (ContractiveMapTasteGate_single_carrier_alignment_decode S)
            (ContractiveMapTasteGate_single_carrier_alignment_decode H)
            (ContractiveMapTasteGate_single_carrier_alignment_decode C)
            (ContractiveMapTasteGate_single_carrier_alignment_decode P)
            (ContractiveMapTasteGate_single_carrier_alignment_decode N))

private theorem contractiveMapToEventFlow_injective {x y : ContractiveMapUp} :
    contractiveMapToEventFlow x = contractiveMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contractiveMapFromEventFlow (contractiveMapToEventFlow x) =
        contractiveMapFromEventFlow (contractiveMapToEventFlow y) :=
    congrArg contractiveMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ContractiveMapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ContractiveMapTasteGate_single_carrier_alignment_round_trip y)))

private theorem contractiveMap_field_faithful :
    ∀ x y : ContractiveMapUp, contractiveMapFields x = contractiveMapFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X Y f k D G S H C P N =>
      cases y with
      | mk X' Y' f' k' D' G' S' H' C' P' N' =>
          cases hfields
          rfl

instance contractiveMapBHistCarrier : BHistCarrier ContractiveMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contractiveMapToEventFlow
  fromEventFlow := contractiveMapFromEventFlow

instance contractiveMapChapterTasteGate : ChapterTasteGate ContractiveMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contractiveMapFromEventFlow (contractiveMapToEventFlow x) = some x
    exact ContractiveMapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (contractiveMapToEventFlow_injective heq)

instance contractiveMapFieldFaithful : FieldFaithful ContractiveMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := contractiveMapFields
  field_faithful := contractiveMap_field_faithful

instance contractiveMapNontrivial : BEDC.Meta.TasteGate.Nontrivial ContractiveMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContractiveMapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContractiveMapUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ContractiveMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  contractiveMapChapterTasteGate

theorem ContractiveMapTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ContractiveMapUp) ∧
      Nonempty (FieldFaithful ContractiveMapUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial ContractiveMapUp) ∧
      (∀ h : BHist, contractiveMapDecodeBHist (contractiveMapEncodeBHist h) = h) ∧
      (∀ x : ContractiveMapUp,
        contractiveMapFromEventFlow (contractiveMapToEventFlow x) = some x) ∧
      (∀ x y : ContractiveMapUp,
        contractiveMapToEventFlow x = contractiveMapToEventFlow y → x = y) ∧
      contractiveMapEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨contractiveMapChapterTasteGate⟩
  constructor
  · exact ⟨contractiveMapFieldFaithful⟩
  constructor
  · exact ⟨contractiveMapNontrivial⟩
  constructor
  · exact ContractiveMapTasteGate_single_carrier_alignment_decode
  constructor
  · exact ContractiveMapTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact contractiveMapToEventFlow_injective heq
  · rfl

end BEDC.Derived.ContractiveMapUp
