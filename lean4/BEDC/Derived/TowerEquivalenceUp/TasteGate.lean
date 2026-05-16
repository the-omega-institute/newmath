import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TowerEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TowerEquivalenceUp : Type where
  | mk :
      (tower tower' approx approx' physical physical' openFit openFit' objectivity ledger descent
        endpoint transport provenance name : BHist) →
      TowerEquivalenceUp
  deriving DecidableEq

def towerEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: towerEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: towerEquivalenceEncodeBHist h

def towerEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (towerEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (towerEquivalenceDecodeBHist tail)

private theorem towerEquivalenceDecode_encode_bhist :
    ∀ h : BHist, towerEquivalenceDecodeBHist (towerEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem towerEquivalence_mk_congr
    {tower tower' approx approx' physical physical' openFit openFit' objectivity ledger descent
      endpoint transport provenance name tower₁ tower₁' approx₁ approx₁' physical₁ physical₁'
      openFit₁ openFit₁' objectivity₁ ledger₁ descent₁ endpoint₁ transport₁ provenance₁
      name₁ : BHist}
    (hTower : tower₁ = tower)
    (hTower' : tower₁' = tower')
    (hApprox : approx₁ = approx)
    (hApprox' : approx₁' = approx')
    (hPhysical : physical₁ = physical)
    (hPhysical' : physical₁' = physical')
    (hOpenFit : openFit₁ = openFit)
    (hOpenFit' : openFit₁' = openFit')
    (hObjectivity : objectivity₁ = objectivity)
    (hLedger : ledger₁ = ledger)
    (hDescent : descent₁ = descent)
    (hEndpoint : endpoint₁ = endpoint)
    (hTransport : transport₁ = transport)
    (hProvenance : provenance₁ = provenance)
    (hName : name₁ = name) :
    TowerEquivalenceUp.mk tower₁ tower₁' approx₁ approx₁' physical₁ physical₁' openFit₁
        openFit₁' objectivity₁ ledger₁ descent₁ endpoint₁ transport₁ provenance₁ name₁ =
      TowerEquivalenceUp.mk tower tower' approx approx' physical physical' openFit openFit'
        objectivity ledger descent endpoint transport provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTower
  cases hTower'
  cases hApprox
  cases hApprox'
  cases hPhysical
  cases hPhysical'
  cases hOpenFit
  cases hOpenFit'
  cases hObjectivity
  cases hLedger
  cases hDescent
  cases hEndpoint
  cases hTransport
  cases hProvenance
  cases hName
  rfl

private theorem towerEquivalenceEncodeBHist_injective {h k : BHist} :
    towerEquivalenceEncodeBHist h = towerEquivalenceEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      towerEquivalenceDecodeBHist (towerEquivalenceEncodeBHist h) =
        towerEquivalenceDecodeBHist (towerEquivalenceEncodeBHist k) :=
    congrArg towerEquivalenceDecodeBHist heq
  exact Eq.trans (towerEquivalenceDecode_encode_bhist h).symm
    (Eq.trans hdecode (towerEquivalenceDecode_encode_bhist k))

def towerEquivalenceFields : TowerEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TowerEquivalenceUp.mk tower tower' approx approx' physical physical' openFit openFit'
      objectivity ledger descent endpoint transport provenance name =>
      [tower, tower', approx, approx', physical, physical', openFit, openFit', objectivity,
        ledger, descent, endpoint, transport, provenance, name]

def towerEquivalenceToEventFlow : TowerEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TowerEquivalenceUp.mk tower tower' approx approx' physical physical' openFit openFit'
      objectivity ledger descent endpoint transport provenance name =>
      [towerEquivalenceEncodeBHist tower, towerEquivalenceEncodeBHist tower',
        towerEquivalenceEncodeBHist approx, towerEquivalenceEncodeBHist approx',
        towerEquivalenceEncodeBHist physical, towerEquivalenceEncodeBHist physical',
        towerEquivalenceEncodeBHist openFit, towerEquivalenceEncodeBHist openFit',
        towerEquivalenceEncodeBHist objectivity, towerEquivalenceEncodeBHist ledger,
        towerEquivalenceEncodeBHist descent, towerEquivalenceEncodeBHist endpoint,
        towerEquivalenceEncodeBHist transport, towerEquivalenceEncodeBHist provenance,
        towerEquivalenceEncodeBHist name]

def towerEquivalenceFromEventFlow : EventFlow → Option TowerEquivalenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [tower, tower', approx, approx', physical, physical', openFit, openFit', objectivity,
      ledger, descent, endpoint, transport, provenance, name] =>
      some
        (TowerEquivalenceUp.mk (towerEquivalenceDecodeBHist tower)
          (towerEquivalenceDecodeBHist tower') (towerEquivalenceDecodeBHist approx)
          (towerEquivalenceDecodeBHist approx') (towerEquivalenceDecodeBHist physical)
          (towerEquivalenceDecodeBHist physical') (towerEquivalenceDecodeBHist openFit)
          (towerEquivalenceDecodeBHist openFit') (towerEquivalenceDecodeBHist objectivity)
          (towerEquivalenceDecodeBHist ledger) (towerEquivalenceDecodeBHist descent)
          (towerEquivalenceDecodeBHist endpoint) (towerEquivalenceDecodeBHist transport)
          (towerEquivalenceDecodeBHist provenance) (towerEquivalenceDecodeBHist name))
  | _ => none

private theorem towerEquivalence_round_trip :
    ∀ x : TowerEquivalenceUp,
      towerEquivalenceFromEventFlow (towerEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk tower tower' approx approx' physical physical' openFit openFit' objectivity ledger
      descent endpoint transport provenance name =>
      exact
        congrArg some
          (towerEquivalence_mk_congr
            (towerEquivalenceDecode_encode_bhist tower)
            (towerEquivalenceDecode_encode_bhist tower')
            (towerEquivalenceDecode_encode_bhist approx)
            (towerEquivalenceDecode_encode_bhist approx')
            (towerEquivalenceDecode_encode_bhist physical)
            (towerEquivalenceDecode_encode_bhist physical')
            (towerEquivalenceDecode_encode_bhist openFit)
            (towerEquivalenceDecode_encode_bhist openFit')
            (towerEquivalenceDecode_encode_bhist objectivity)
            (towerEquivalenceDecode_encode_bhist ledger)
            (towerEquivalenceDecode_encode_bhist descent)
            (towerEquivalenceDecode_encode_bhist endpoint)
            (towerEquivalenceDecode_encode_bhist transport)
            (towerEquivalenceDecode_encode_bhist provenance)
            (towerEquivalenceDecode_encode_bhist name))

private theorem towerEquivalenceToEventFlow_injective {x y : TowerEquivalenceUp} :
    towerEquivalenceToEventFlow x = towerEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk tower tower' approx approx' physical physical' openFit openFit' objectivity ledger
      descent endpoint transport provenance name =>
      cases y with
      | mk tower₁ tower₁' approx₁ approx₁' physical₁ physical₁' openFit₁ openFit₁'
          objectivity₁ ledger₁ descent₁ endpoint₁ transport₁ provenance₁ name₁ =>
          injection heq with hTower tail1
          injection tail1 with hTower' tail2
          injection tail2 with hApprox tail3
          injection tail3 with hApprox' tail4
          injection tail4 with hPhysical tail5
          injection tail5 with hPhysical' tail6
          injection tail6 with hOpenFit tail7
          injection tail7 with hOpenFit' tail8
          injection tail8 with hObjectivity tail9
          injection tail9 with hLedger tail10
          injection tail10 with hDescent tail11
          injection tail11 with hEndpoint tail12
          injection tail12 with hTransport tail13
          injection tail13 with hProvenance tail14
          injection tail14 with hName _
          exact
            towerEquivalence_mk_congr
              (towerEquivalenceEncodeBHist_injective hTower)
              (towerEquivalenceEncodeBHist_injective hTower')
              (towerEquivalenceEncodeBHist_injective hApprox)
              (towerEquivalenceEncodeBHist_injective hApprox')
              (towerEquivalenceEncodeBHist_injective hPhysical)
              (towerEquivalenceEncodeBHist_injective hPhysical')
              (towerEquivalenceEncodeBHist_injective hOpenFit)
              (towerEquivalenceEncodeBHist_injective hOpenFit')
              (towerEquivalenceEncodeBHist_injective hObjectivity)
              (towerEquivalenceEncodeBHist_injective hLedger)
              (towerEquivalenceEncodeBHist_injective hDescent)
              (towerEquivalenceEncodeBHist_injective hEndpoint)
              (towerEquivalenceEncodeBHist_injective hTransport)
              (towerEquivalenceEncodeBHist_injective hProvenance)
              (towerEquivalenceEncodeBHist_injective hName)

private theorem towerEquivalence_field_faithful :
    ∀ x y : TowerEquivalenceUp, towerEquivalenceFields x = towerEquivalenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk tower tower' approx approx' physical physical' openFit openFit' objectivity ledger
      descent endpoint transport provenance name =>
      cases y with
      | mk tower₁ tower₁' approx₁ approx₁' physical₁ physical₁' openFit₁ openFit₁'
          objectivity₁ ledger₁ descent₁ endpoint₁ transport₁ provenance₁ name₁ =>
          cases hfields
          rfl

instance towerEquivalenceBHistCarrier : BHistCarrier TowerEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := towerEquivalenceToEventFlow
  fromEventFlow := towerEquivalenceFromEventFlow

instance towerEquivalenceChapterTasteGate : ChapterTasteGate TowerEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change towerEquivalenceFromEventFlow (towerEquivalenceToEventFlow x) = some x
    exact towerEquivalence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (towerEquivalenceToEventFlow_injective heq)

instance towerEquivalenceFieldFaithful : FieldFaithful TowerEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := towerEquivalenceFields
  field_faithful := towerEquivalence_field_faithful

instance towerEquivalenceNontrivial : Nontrivial TowerEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TowerEquivalenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      TowerEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TowerEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  towerEquivalenceChapterTasteGate

theorem TowerEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, towerEquivalenceDecodeBHist (towerEquivalenceEncodeBHist h) = h) ∧
      towerEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x y : TowerEquivalenceUp, towerEquivalenceFields x = towerEquivalenceFields y →
          x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact towerEquivalenceDecode_encode_bhist
  · constructor
    · rfl
    · exact towerEquivalence_field_faithful

end BEDC.Derived.TowerEquivalenceUp
