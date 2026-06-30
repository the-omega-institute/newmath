import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WeylEquidistributionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WeylEquidistributionUp : Type where
  | mk :
      (sequence intervalLedger counting discrepancy exhaustion transport replay provenance
        localName : BHist) →
      WeylEquidistributionUp
  deriving DecidableEq

def weylEquidistributionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: weylEquidistributionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: weylEquidistributionEncodeBHist h

def weylEquidistributionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (weylEquidistributionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (weylEquidistributionDecodeBHist tail)

private theorem WeylEquidistributionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      weylEquidistributionDecodeBHist (weylEquidistributionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def weylEquidistributionFields : WeylEquidistributionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WeylEquidistributionUp.mk sequence intervalLedger counting discrepancy exhaustion transport
      replay provenance localName =>
      [sequence, intervalLedger, counting, discrepancy, exhaustion, transport, replay,
        provenance, localName]

def weylEquidistributionToEventFlow : WeylEquidistributionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (weylEquidistributionFields x).map weylEquidistributionEncodeBHist

def weylEquidistributionFromEventFlow : EventFlow → Option WeylEquidistributionUp
  -- BEDC touchpoint anchor: BHist BMark
  | sequence :: restSequence =>
      match restSequence with
      | intervalLedger :: restIntervalLedger =>
          match restIntervalLedger with
          | counting :: restCounting =>
              match restCounting with
              | discrepancy :: restDiscrepancy =>
                  match restDiscrepancy with
                  | exhaustion :: restExhaustion =>
                      match restExhaustion with
                      | transport :: restTransport =>
                          match restTransport with
                          | replay :: restReplay =>
                              match restReplay with
                              | provenance :: restProvenance =>
                                  match restProvenance with
                                  | localName :: restLocalName =>
                                      match restLocalName with
                                      | [] =>
                                          some
                                            (WeylEquidistributionUp.mk
                                              (weylEquidistributionDecodeBHist sequence)
                                              (weylEquidistributionDecodeBHist intervalLedger)
                                              (weylEquidistributionDecodeBHist counting)
                                              (weylEquidistributionDecodeBHist discrepancy)
                                              (weylEquidistributionDecodeBHist exhaustion)
                                              (weylEquidistributionDecodeBHist transport)
                                              (weylEquidistributionDecodeBHist replay)
                                              (weylEquidistributionDecodeBHist provenance)
                                              (weylEquidistributionDecodeBHist localName))
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

private theorem weylEquidistribution_mk_congr
    {sequence sequence' intervalLedger intervalLedger' counting counting' discrepancy
      discrepancy' exhaustion exhaustion' transport transport' replay replay' provenance
      provenance' localName localName' : BHist}
    (hSequence : sequence' = sequence)
    (hIntervalLedger : intervalLedger' = intervalLedger)
    (hCounting : counting' = counting)
    (hDiscrepancy : discrepancy' = discrepancy)
    (hExhaustion : exhaustion' = exhaustion)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    WeylEquidistributionUp.mk sequence' intervalLedger' counting' discrepancy' exhaustion'
        transport' replay' provenance' localName' =
      WeylEquidistributionUp.mk sequence intervalLedger counting discrepancy exhaustion transport
        replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSequence
  cases hIntervalLedger
  cases hCounting
  cases hDiscrepancy
  cases hExhaustion
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

private theorem WeylEquidistributionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : WeylEquidistributionUp,
      weylEquidistributionFromEventFlow (weylEquidistributionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sequence intervalLedger counting discrepancy exhaustion transport replay provenance localName =>
      exact
        congrArg some
          (weylEquidistribution_mk_congr
            (WeylEquidistributionTasteGate_single_carrier_alignment_decode sequence)
            (WeylEquidistributionTasteGate_single_carrier_alignment_decode intervalLedger)
            (WeylEquidistributionTasteGate_single_carrier_alignment_decode counting)
            (WeylEquidistributionTasteGate_single_carrier_alignment_decode discrepancy)
            (WeylEquidistributionTasteGate_single_carrier_alignment_decode exhaustion)
            (WeylEquidistributionTasteGate_single_carrier_alignment_decode transport)
            (WeylEquidistributionTasteGate_single_carrier_alignment_decode replay)
            (WeylEquidistributionTasteGate_single_carrier_alignment_decode provenance)
            (WeylEquidistributionTasteGate_single_carrier_alignment_decode localName))

private theorem weylEquidistributionToEventFlow_injective
    {x y : WeylEquidistributionUp} :
    weylEquidistributionToEventFlow x = weylEquidistributionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      weylEquidistributionFromEventFlow (weylEquidistributionToEventFlow x) =
        weylEquidistributionFromEventFlow (weylEquidistributionToEventFlow y) :=
    congrArg weylEquidistributionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (WeylEquidistributionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (WeylEquidistributionTasteGate_single_carrier_alignment_round_trip y)))

instance weylEquidistributionBHistCarrier : BHistCarrier WeylEquidistributionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := weylEquidistributionToEventFlow
  fromEventFlow := weylEquidistributionFromEventFlow

instance weylEquidistributionChapterTasteGate :
    ChapterTasteGate WeylEquidistributionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change weylEquidistributionFromEventFlow (weylEquidistributionToEventFlow x) = some x
    exact WeylEquidistributionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (weylEquidistributionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate WeylEquidistributionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  weylEquidistributionChapterTasteGate

theorem WeylEquidistributionTasteGate_single_carrier_alignment :
    (∀ h : BHist, weylEquidistributionDecodeBHist (weylEquidistributionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier WeylEquidistributionUp) ∧
      Nonempty (ChapterTasteGate WeylEquidistributionUp) ∧
      weylEquidistributionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨WeylEquidistributionTasteGate_single_carrier_alignment_decode,
      ⟨weylEquidistributionBHistCarrier⟩,
      ⟨weylEquidistributionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.WeylEquidistributionUp
