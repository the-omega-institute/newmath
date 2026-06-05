import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyStructureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyStructureUp : Type where
  | mk (F G D S R E H C P N : BHist) : CauchyStructureUp
  deriving DecidableEq

def CauchyStructureTasteGate_single_carrier_alignment_encodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CauchyStructureTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CauchyStructureTasteGate_single_carrier_alignment_encodeBHist h

def CauchyStructureTasteGate_single_carrier_alignment_decodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchyStructureTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
        (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchyStructureTasteGate_single_carrier_alignment_fields :
    CauchyStructureUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyStructureUp.mk F G D S R E H C P N => [F, G, D, S, R, E, H, C, P, N]

def CauchyStructureTasteGate_single_carrier_alignment_toEventFlow :
    CauchyStructureUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token =>
      (CauchyStructureTasteGate_single_carrier_alignment_fields token).map
        CauchyStructureTasteGate_single_carrier_alignment_encodeBHist

def CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option CauchyStructureUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: restF =>
      match restF with
      | G :: restG =>
          match restG with
          | D :: restD =>
              match restD with
              | S :: restS =>
                  match restS with
                  | R :: restR =>
                      match restR with
                      | E :: restE =>
                          match restE with
                          | H :: restH =>
                              match restH with
                              | C :: restC =>
                                  match restC with
                                  | P :: restP =>
                                      match restP with
                                      | N :: restN =>
                                          match restN with
                                          | [] =>
                                              some
                                                (CauchyStructureUp.mk
                                                  (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist F)
                                                  (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist G)
                                                  (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist D)
                                                  (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist S)
                                                  (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist R)
                                                  (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist E)
                                                  (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist H)
                                                  (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist C)
                                                  (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist P)
                                                  (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist N))
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

private theorem CauchyStructureTasteGate_single_carrier_alignment_round_trip :
    forall token : CauchyStructureUp,
      CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow
        (CauchyStructureTasteGate_single_carrier_alignment_toEventFlow token) = some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk F G D S R E H C P N =>
      change
        some
            (CauchyStructureUp.mk
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist F))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist G))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist D))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist S))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist R))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist E))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist H))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist C))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist P))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CauchyStructureUp.mk F G D S R E H C P N)
      rw [CauchyStructureTasteGate_single_carrier_alignment_decode F]
      rw [CauchyStructureTasteGate_single_carrier_alignment_decode G]
      rw [CauchyStructureTasteGate_single_carrier_alignment_decode D]
      rw [CauchyStructureTasteGate_single_carrier_alignment_decode S]
      rw [CauchyStructureTasteGate_single_carrier_alignment_decode R]
      rw [CauchyStructureTasteGate_single_carrier_alignment_decode E]
      rw [CauchyStructureTasteGate_single_carrier_alignment_decode H]
      rw [CauchyStructureTasteGate_single_carrier_alignment_decode C]
      rw [CauchyStructureTasteGate_single_carrier_alignment_decode P]
      rw [CauchyStructureTasteGate_single_carrier_alignment_decode N]

private theorem CauchyStructureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyStructureUp} :
    CauchyStructureTasteGate_single_carrier_alignment_toEventFlow x =
      CauchyStructureTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyStructureTasteGate_single_carrier_alignment_toEventFlow x) =
        CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyStructureTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyStructureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyStructureTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyStructureBHistCarrier : BHistCarrier CauchyStructureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyStructureTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow

instance cauchyStructureChapterTasteGate : ChapterTasteGate CauchyStructureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow
        (CauchyStructureTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact CauchyStructureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyStructureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def CauchyStructureTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyStructureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyStructureChapterTasteGate

theorem CauchyStructureTasteGate_single_carrier_alignment :
    ChapterTasteGate CauchyStructureUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact cauchyStructureChapterTasteGate

end BEDC.Derived.CauchyStructureUp
