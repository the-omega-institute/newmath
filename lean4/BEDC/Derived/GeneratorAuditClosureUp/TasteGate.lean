import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GeneratorAuditClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GeneratorAuditClosureUp : Type where
  | mk (G K A Q H C P N : BHist) : GeneratorAuditClosureUp
  deriving DecidableEq

def generatorAuditClosureEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: generatorAuditClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: generatorAuditClosureEncodeBHist h

def generatorAuditClosureDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (generatorAuditClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (generatorAuditClosureDecodeBHist tail)

private theorem GeneratorAuditClosureTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      generatorAuditClosureDecodeBHist (generatorAuditClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def generatorAuditClosureToEventFlow : GeneratorAuditClosureUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GeneratorAuditClosureUp.mk G K A Q H C P N =>
      [generatorAuditClosureEncodeBHist G,
        generatorAuditClosureEncodeBHist K,
        generatorAuditClosureEncodeBHist A,
        generatorAuditClosureEncodeBHist Q,
        generatorAuditClosureEncodeBHist H,
        generatorAuditClosureEncodeBHist C,
        generatorAuditClosureEncodeBHist P,
        generatorAuditClosureEncodeBHist N]

def generatorAuditClosureFromEventFlow : EventFlow -> Option GeneratorAuditClosureUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | G :: rest0 =>
      match rest0 with
      | [] => none
      | K :: rest1 =>
          match rest1 with
          | [] => none
          | A :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | P :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (GeneratorAuditClosureUp.mk
                                          (generatorAuditClosureDecodeBHist G)
                                          (generatorAuditClosureDecodeBHist K)
                                          (generatorAuditClosureDecodeBHist A)
                                          (generatorAuditClosureDecodeBHist Q)
                                          (generatorAuditClosureDecodeBHist H)
                                          (generatorAuditClosureDecodeBHist C)
                                          (generatorAuditClosureDecodeBHist P)
                                          (generatorAuditClosureDecodeBHist N))
                                  | _ :: _ => none

private theorem GeneratorAuditClosureTasteGate_single_carrier_alignment_round_trip :
    forall x : GeneratorAuditClosureUp,
      generatorAuditClosureFromEventFlow (generatorAuditClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G K A Q H C P N =>
      change
        some
          (GeneratorAuditClosureUp.mk
            (generatorAuditClosureDecodeBHist (generatorAuditClosureEncodeBHist G))
            (generatorAuditClosureDecodeBHist (generatorAuditClosureEncodeBHist K))
            (generatorAuditClosureDecodeBHist (generatorAuditClosureEncodeBHist A))
            (generatorAuditClosureDecodeBHist (generatorAuditClosureEncodeBHist Q))
            (generatorAuditClosureDecodeBHist (generatorAuditClosureEncodeBHist H))
            (generatorAuditClosureDecodeBHist (generatorAuditClosureEncodeBHist C))
            (generatorAuditClosureDecodeBHist (generatorAuditClosureEncodeBHist P))
            (generatorAuditClosureDecodeBHist (generatorAuditClosureEncodeBHist N))) =
          some (GeneratorAuditClosureUp.mk G K A Q H C P N)
      rw [GeneratorAuditClosureTasteGate_single_carrier_alignment_decode G,
        GeneratorAuditClosureTasteGate_single_carrier_alignment_decode K,
        GeneratorAuditClosureTasteGate_single_carrier_alignment_decode A,
        GeneratorAuditClosureTasteGate_single_carrier_alignment_decode Q,
        GeneratorAuditClosureTasteGate_single_carrier_alignment_decode H,
        GeneratorAuditClosureTasteGate_single_carrier_alignment_decode C,
        GeneratorAuditClosureTasteGate_single_carrier_alignment_decode P,
        GeneratorAuditClosureTasteGate_single_carrier_alignment_decode N]

private theorem GeneratorAuditClosureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GeneratorAuditClosureUp} :
    generatorAuditClosureToEventFlow x = generatorAuditClosureToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      generatorAuditClosureFromEventFlow (generatorAuditClosureToEventFlow x) =
        generatorAuditClosureFromEventFlow (generatorAuditClosureToEventFlow y) :=
    congrArg generatorAuditClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (GeneratorAuditClosureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (GeneratorAuditClosureTasteGate_single_carrier_alignment_round_trip y)))

instance generatorAuditClosureBHistCarrier : BHistCarrier GeneratorAuditClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := generatorAuditClosureToEventFlow
  fromEventFlow := generatorAuditClosureFromEventFlow

instance generatorAuditClosureChapterTasteGate :
    ChapterTasteGate GeneratorAuditClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change generatorAuditClosureFromEventFlow (generatorAuditClosureToEventFlow x) = some x
    exact GeneratorAuditClosureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GeneratorAuditClosureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem GeneratorAuditClosureTasteGate_single_carrier_alignment :
    (forall h : BHist,
      generatorAuditClosureDecodeBHist (generatorAuditClosureEncodeBHist h) = h) /\
      Nonempty (BHistCarrier GeneratorAuditClosureUp) /\
        Nonempty (ChapterTasteGate GeneratorAuditClosureUp) /\
          generatorAuditClosureEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨GeneratorAuditClosureTasteGate_single_carrier_alignment_decode,
      ⟨generatorAuditClosureBHistCarrier⟩,
      ⟨generatorAuditClosureChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.GeneratorAuditClosureUp
