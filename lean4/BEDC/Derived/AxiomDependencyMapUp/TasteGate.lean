import BEDC.Derived.AxiomDependencyMapUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxiomDependencyMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Eight-row carrier for the axiom-dependency-map certificate surface. -/
inductive AxiomDependencyMapUp : Type where
  | mk
      (claim mode witness supply transport replay provenance localName : BHist) :
      AxiomDependencyMapUp

def axiomDependencyMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axiomDependencyMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axiomDependencyMapEncodeBHist h

def axiomDependencyMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axiomDependencyMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axiomDependencyMapDecodeBHist tail)

private theorem axiomDependencyMapDecode_encode_bhist :
    ∀ h : BHist, axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def axiomDependencyMapFields : AxiomDependencyMapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AxiomDependencyMapUp.mk claim mode witness supply transport replay provenance localName =>
      [claim, mode, witness, supply, transport, replay, provenance, localName]

def axiomDependencyMapToEventFlow : AxiomDependencyMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (axiomDependencyMapFields x).map axiomDependencyMapEncodeBHist

private def axiomDependencyMapEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => axiomDependencyMapEventAtDefault index rest

def axiomDependencyMapFromEventFlow (ef : EventFlow) : Option AxiomDependencyMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AxiomDependencyMapUp.mk
      (axiomDependencyMapDecodeBHist (axiomDependencyMapEventAtDefault 0 ef))
      (axiomDependencyMapDecodeBHist (axiomDependencyMapEventAtDefault 1 ef))
      (axiomDependencyMapDecodeBHist (axiomDependencyMapEventAtDefault 2 ef))
      (axiomDependencyMapDecodeBHist (axiomDependencyMapEventAtDefault 3 ef))
      (axiomDependencyMapDecodeBHist (axiomDependencyMapEventAtDefault 4 ef))
      (axiomDependencyMapDecodeBHist (axiomDependencyMapEventAtDefault 5 ef))
      (axiomDependencyMapDecodeBHist (axiomDependencyMapEventAtDefault 6 ef))
      (axiomDependencyMapDecodeBHist (axiomDependencyMapEventAtDefault 7 ef)))

private theorem axiomDependencyMap_round_trip :
    ∀ x : AxiomDependencyMapUp,
      axiomDependencyMapFromEventFlow (axiomDependencyMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk claim mode witness supply transport replay provenance localName =>
      change
        some
          (AxiomDependencyMapUp.mk
            (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist claim))
            (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist mode))
            (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist witness))
            (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist supply))
            (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist transport))
            (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist replay))
            (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist provenance))
            (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist localName))) =
          some
            (AxiomDependencyMapUp.mk claim mode witness supply transport replay provenance
              localName)
      apply congrArg some
      exact
        Eq.trans
          (congrArg
            (fun z =>
              AxiomDependencyMapUp.mk z
                (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist mode))
                (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist witness))
                (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist supply))
                (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist transport))
                (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist replay))
                (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist provenance))
                (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist localName)))
            (axiomDependencyMapDecode_encode_bhist claim))
          (Eq.trans
            (congrArg
              (fun z =>
                AxiomDependencyMapUp.mk claim z
                  (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist witness))
                  (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist supply))
                  (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist transport))
                  (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist replay))
                  (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist provenance))
                  (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist localName)))
              (axiomDependencyMapDecode_encode_bhist mode))
            (Eq.trans
              (congrArg
                (fun z =>
                  AxiomDependencyMapUp.mk claim mode z
                    (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist supply))
                    (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist transport))
                    (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist replay))
                    (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist provenance))
                    (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist localName)))
                (axiomDependencyMapDecode_encode_bhist witness))
              (Eq.trans
                (congrArg
                  (fun z =>
                    AxiomDependencyMapUp.mk claim mode witness z
                      (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist transport))
                      (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist replay))
                      (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist provenance))
                      (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist localName)))
                  (axiomDependencyMapDecode_encode_bhist supply))
                (Eq.trans
                  (congrArg
                    (fun z =>
                      AxiomDependencyMapUp.mk claim mode witness supply z
                        (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist replay))
                        (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist provenance))
                        (axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist localName)))
                    (axiomDependencyMapDecode_encode_bhist transport))
                  (Eq.trans
                    (congrArg
                      (fun z =>
                        AxiomDependencyMapUp.mk claim mode witness supply transport z
                          (axiomDependencyMapDecodeBHist
                            (axiomDependencyMapEncodeBHist provenance))
                          (axiomDependencyMapDecodeBHist
                            (axiomDependencyMapEncodeBHist localName)))
                      (axiomDependencyMapDecode_encode_bhist replay))
                    (Eq.trans
                      (congrArg
                        (fun z =>
                          AxiomDependencyMapUp.mk claim mode witness supply transport replay z
                            (axiomDependencyMapDecodeBHist
                              (axiomDependencyMapEncodeBHist localName)))
                        (axiomDependencyMapDecode_encode_bhist provenance))
                      (congrArg
                        (fun z =>
                          AxiomDependencyMapUp.mk claim mode witness supply transport replay
                            provenance z)
                        (axiomDependencyMapDecode_encode_bhist localName))))))))

theorem axiomDependencyMapToEventFlow_injective {x y : AxiomDependencyMapUp} :
    axiomDependencyMapToEventFlow x = axiomDependencyMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk claim₁ mode₁ witness₁ supply₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk claim₂ mode₂ witness₂ supply₂ transport₂ replay₂ provenance₂ localName₂ =>
          injection heq with hClaim tail0
          injection tail0 with hMode tail1
          injection tail1 with hWitness tail2
          injection tail2 with hSupply tail3
          injection tail3 with hTransport tail4
          injection tail4 with hReplay tail5
          injection tail5 with hProvenance tail6
          injection tail6 with hLocalName _
          have claimEq : claim₁ = claim₂ := by
            have decoded := congrArg axiomDependencyMapDecodeBHist hClaim
            exact Eq.trans (axiomDependencyMapDecode_encode_bhist claim₁).symm
              (Eq.trans decoded (axiomDependencyMapDecode_encode_bhist claim₂))
          cases claimEq
          have modeEq : mode₁ = mode₂ := by
            have decoded := congrArg axiomDependencyMapDecodeBHist hMode
            exact Eq.trans (axiomDependencyMapDecode_encode_bhist mode₁).symm
              (Eq.trans decoded (axiomDependencyMapDecode_encode_bhist mode₂))
          cases modeEq
          have witnessEq : witness₁ = witness₂ := by
            have decoded := congrArg axiomDependencyMapDecodeBHist hWitness
            exact Eq.trans (axiomDependencyMapDecode_encode_bhist witness₁).symm
              (Eq.trans decoded (axiomDependencyMapDecode_encode_bhist witness₂))
          cases witnessEq
          have supplyEq : supply₁ = supply₂ := by
            have decoded := congrArg axiomDependencyMapDecodeBHist hSupply
            exact Eq.trans (axiomDependencyMapDecode_encode_bhist supply₁).symm
              (Eq.trans decoded (axiomDependencyMapDecode_encode_bhist supply₂))
          cases supplyEq
          have transportEq : transport₁ = transport₂ := by
            have decoded := congrArg axiomDependencyMapDecodeBHist hTransport
            exact Eq.trans (axiomDependencyMapDecode_encode_bhist transport₁).symm
              (Eq.trans decoded (axiomDependencyMapDecode_encode_bhist transport₂))
          cases transportEq
          have replayEq : replay₁ = replay₂ := by
            have decoded := congrArg axiomDependencyMapDecodeBHist hReplay
            exact Eq.trans (axiomDependencyMapDecode_encode_bhist replay₁).symm
              (Eq.trans decoded (axiomDependencyMapDecode_encode_bhist replay₂))
          cases replayEq
          have provenanceEq : provenance₁ = provenance₂ := by
            have decoded := congrArg axiomDependencyMapDecodeBHist hProvenance
            exact Eq.trans (axiomDependencyMapDecode_encode_bhist provenance₁).symm
              (Eq.trans decoded (axiomDependencyMapDecode_encode_bhist provenance₂))
          cases provenanceEq
          have localNameEq : localName₁ = localName₂ := by
            have decoded := congrArg axiomDependencyMapDecodeBHist hLocalName
            exact Eq.trans (axiomDependencyMapDecode_encode_bhist localName₁).symm
              (Eq.trans decoded (axiomDependencyMapDecode_encode_bhist localName₂))
          cases localNameEq
          rfl

instance axiomDependencyMapBHistCarrier : BHistCarrier AxiomDependencyMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axiomDependencyMapToEventFlow
  fromEventFlow := axiomDependencyMapFromEventFlow

instance axiomDependencyMapChapterTasteGate : ChapterTasteGate AxiomDependencyMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change axiomDependencyMapFromEventFlow (axiomDependencyMapToEventFlow x) = some x
    exact axiomDependencyMap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axiomDependencyMapToEventFlow_injective heq)

def taste_gate : ChapterTasteGate AxiomDependencyMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  axiomDependencyMapChapterTasteGate

theorem AxiomDependencyMapTasteGate_single_carrier_alignment :
    (∀ h : BHist, axiomDependencyMapDecodeBHist (axiomDependencyMapEncodeBHist h) = h) ∧
      (∀ x : AxiomDependencyMapUp,
        axiomDependencyMapFromEventFlow (axiomDependencyMapToEventFlow x) = some x) ∧
        (∀ x y : AxiomDependencyMapUp,
          axiomDependencyMapToEventFlow x = axiomDependencyMapToEventFlow y → x = y) ∧
          axiomDependencyMapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨axiomDependencyMapDecode_encode_bhist,
      axiomDependencyMap_round_trip,
      (fun _ _ heq => axiomDependencyMapToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AxiomDependencyMapUp
