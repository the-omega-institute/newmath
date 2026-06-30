import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DendriteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DendriteUp : Type where
  | mk :
      (compactMetric locallyConnected peanoContinuum tree endpoint uniqueArc cutpoint transport
        replay provenance source nameCert : BHist) ->
        DendriteUp
  deriving DecidableEq

def dendriteEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dendriteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dendriteEncodeBHist h

def dendriteDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dendriteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dendriteDecodeBHist tail)

theorem DendriteTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, dendriteDecodeBHist (dendriteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dendriteFields : DendriteUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DendriteUp.mk compactMetric locallyConnected peanoContinuum tree endpoint uniqueArc
      cutpoint transport replay provenance source nameCert =>
      [compactMetric, locallyConnected, peanoContinuum, tree, endpoint, uniqueArc, cutpoint,
        transport, replay, provenance, source, nameCert]

def dendriteToEventFlow : DendriteUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dendriteFields x).map dendriteEncodeBHist

def dendriteFromEventFlow : EventFlow -> Option DendriteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | [] => none
    | compactMetric :: rest0 =>
        match rest0 with
        | [] => none
        | locallyConnected :: rest1 =>
            match rest1 with
            | [] => none
            | peanoContinuum :: rest2 =>
                match rest2 with
                | [] => none
                | tree :: rest3 =>
                    match rest3 with
                    | [] => none
                    | endpoint :: rest4 =>
                        match rest4 with
                        | [] => none
                        | uniqueArc :: rest5 =>
                            match rest5 with
                            | [] => none
                            | cutpoint :: rest6 =>
                                match rest6 with
                                | [] => none
                                | transport :: rest7 =>
                                    match rest7 with
                                    | [] => none
                                    | replay :: rest8 =>
                                        match rest8 with
                                        | [] => none
                                        | provenance :: rest9 =>
                                            match rest9 with
                                            | [] => none
                                            | source :: rest10 =>
                                                match rest10 with
                                                | [] => none
                                                | nameCert :: rest11 =>
                                                    match rest11 with
                                                    | [] =>
                                                        some
                                                          (DendriteUp.mk
                                                            (dendriteDecodeBHist compactMetric)
                                                            (dendriteDecodeBHist locallyConnected)
                                                            (dendriteDecodeBHist peanoContinuum)
                                                            (dendriteDecodeBHist tree)
                                                            (dendriteDecodeBHist endpoint)
                                                            (dendriteDecodeBHist uniqueArc)
                                                            (dendriteDecodeBHist cutpoint)
                                                            (dendriteDecodeBHist transport)
                                                            (dendriteDecodeBHist replay)
                                                            (dendriteDecodeBHist provenance)
                                                            (dendriteDecodeBHist source)
                                                            (dendriteDecodeBHist nameCert))
                                                    | _ :: _ => none

private theorem dendrite_round_trip :
    forall x : DendriteUp, dendriteFromEventFlow (dendriteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactMetric locallyConnected peanoContinuum tree endpoint uniqueArc cutpoint transport
      replay provenance source nameCert =>
      change
        some
          (DendriteUp.mk
            (dendriteDecodeBHist (dendriteEncodeBHist compactMetric))
            (dendriteDecodeBHist (dendriteEncodeBHist locallyConnected))
            (dendriteDecodeBHist (dendriteEncodeBHist peanoContinuum))
            (dendriteDecodeBHist (dendriteEncodeBHist tree))
            (dendriteDecodeBHist (dendriteEncodeBHist endpoint))
            (dendriteDecodeBHist (dendriteEncodeBHist uniqueArc))
            (dendriteDecodeBHist (dendriteEncodeBHist cutpoint))
            (dendriteDecodeBHist (dendriteEncodeBHist transport))
            (dendriteDecodeBHist (dendriteEncodeBHist replay))
            (dendriteDecodeBHist (dendriteEncodeBHist provenance))
            (dendriteDecodeBHist (dendriteEncodeBHist source))
            (dendriteDecodeBHist (dendriteEncodeBHist nameCert))) =
          some
            (DendriteUp.mk compactMetric locallyConnected peanoContinuum tree endpoint
              uniqueArc cutpoint transport replay provenance source nameCert)
      rw [DendriteTasteGate_single_carrier_alignment_decode_encode compactMetric,
        DendriteTasteGate_single_carrier_alignment_decode_encode locallyConnected,
        DendriteTasteGate_single_carrier_alignment_decode_encode peanoContinuum,
        DendriteTasteGate_single_carrier_alignment_decode_encode tree,
        DendriteTasteGate_single_carrier_alignment_decode_encode endpoint,
        DendriteTasteGate_single_carrier_alignment_decode_encode uniqueArc,
        DendriteTasteGate_single_carrier_alignment_decode_encode cutpoint,
        DendriteTasteGate_single_carrier_alignment_decode_encode transport,
        DendriteTasteGate_single_carrier_alignment_decode_encode replay,
        DendriteTasteGate_single_carrier_alignment_decode_encode provenance,
        DendriteTasteGate_single_carrier_alignment_decode_encode source,
        DendriteTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem dendriteToEventFlow_injective {x y : DendriteUp} :
    dendriteToEventFlow x = dendriteToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dendriteFromEventFlow (dendriteToEventFlow x) =
        dendriteFromEventFlow (dendriteToEventFlow y) :=
    congrArg dendriteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dendrite_round_trip x).symm (Eq.trans hread (dendrite_round_trip y)))

def dendriteCarrier : BHistCarrier DendriteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dendriteToEventFlow
  fromEventFlow := dendriteFromEventFlow

instance dendriteBHistCarrier : BHistCarrier DendriteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dendriteCarrier

def dendriteTasteGate : @ChapterTasteGate DendriteUp dendriteCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => dendrite_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dendriteToEventFlow_injective heq)

instance dendriteChapterTasteGate : ChapterTasteGate DendriteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dendriteTasteGate

theorem DendriteTasteGate_single_carrier_alignment :
    (∀ h : BHist, dendriteDecodeBHist (dendriteEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DendriteUp) ∧ Nonempty (ChapterTasteGate DendriteUp) ∧
        ∃ x : DendriteUp, dendriteFromEventFlow (dendriteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DendriteTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨dendriteCarrier⟩,
        ⟨⟨dendriteTasteGate⟩,
          ⟨DendriteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            rfl⟩⟩⟩⟩

end BEDC.Derived.DendriteUp
