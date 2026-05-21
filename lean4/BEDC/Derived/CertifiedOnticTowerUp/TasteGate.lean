import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CertifiedOnticTowerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CertifiedOnticTowerUp : Type where
  | mk :
      (stage signatures refinement ledger classifier transport replay provenance name : BHist) →
      CertifiedOnticTowerUp
  deriving DecidableEq

def certifiedOnticTowerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: certifiedOnticTowerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: certifiedOnticTowerEncodeBHist h

def certifiedOnticTowerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (certifiedOnticTowerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (certifiedOnticTowerDecodeBHist tail)

private theorem certifiedOnticTower_decode_encode_bhist :
    ∀ h : BHist, certifiedOnticTowerDecodeBHist (certifiedOnticTowerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def certifiedOnticTowerFields : CertifiedOnticTowerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CertifiedOnticTowerUp.mk stage signatures refinement ledger classifier transport replay
      provenance name =>
      [stage, signatures, refinement, ledger, classifier, transport, replay, provenance, name]

def certifiedOnticTowerToEventFlow : CertifiedOnticTowerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map certifiedOnticTowerEncodeBHist (certifiedOnticTowerFields x)

def certifiedOnticTowerFromEventFlow : EventFlow → Option CertifiedOnticTowerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [stage, signatures, refinement, ledger, classifier, transport, replay, provenance, name] =>
      some
        (CertifiedOnticTowerUp.mk
          (certifiedOnticTowerDecodeBHist stage)
          (certifiedOnticTowerDecodeBHist signatures)
          (certifiedOnticTowerDecodeBHist refinement)
          (certifiedOnticTowerDecodeBHist ledger)
          (certifiedOnticTowerDecodeBHist classifier)
          (certifiedOnticTowerDecodeBHist transport)
          (certifiedOnticTowerDecodeBHist replay)
          (certifiedOnticTowerDecodeBHist provenance)
          (certifiedOnticTowerDecodeBHist name))
  | _ => none

private theorem certifiedOnticTower_round_trip :
    ∀ x : CertifiedOnticTowerUp,
      certifiedOnticTowerFromEventFlow (certifiedOnticTowerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stage signatures refinement ledger classifier transport replay provenance name =>
      change
        some
          (CertifiedOnticTowerUp.mk
            (certifiedOnticTowerDecodeBHist (certifiedOnticTowerEncodeBHist stage))
            (certifiedOnticTowerDecodeBHist (certifiedOnticTowerEncodeBHist signatures))
            (certifiedOnticTowerDecodeBHist (certifiedOnticTowerEncodeBHist refinement))
            (certifiedOnticTowerDecodeBHist (certifiedOnticTowerEncodeBHist ledger))
            (certifiedOnticTowerDecodeBHist (certifiedOnticTowerEncodeBHist classifier))
            (certifiedOnticTowerDecodeBHist (certifiedOnticTowerEncodeBHist transport))
            (certifiedOnticTowerDecodeBHist (certifiedOnticTowerEncodeBHist replay))
            (certifiedOnticTowerDecodeBHist (certifiedOnticTowerEncodeBHist provenance))
            (certifiedOnticTowerDecodeBHist (certifiedOnticTowerEncodeBHist name))) =
          some
            (CertifiedOnticTowerUp.mk stage signatures refinement ledger classifier transport
              replay provenance name)
      rw [certifiedOnticTower_decode_encode_bhist stage,
        certifiedOnticTower_decode_encode_bhist signatures,
        certifiedOnticTower_decode_encode_bhist refinement,
        certifiedOnticTower_decode_encode_bhist ledger,
        certifiedOnticTower_decode_encode_bhist classifier,
        certifiedOnticTower_decode_encode_bhist transport,
        certifiedOnticTower_decode_encode_bhist replay,
        certifiedOnticTower_decode_encode_bhist provenance,
        certifiedOnticTower_decode_encode_bhist name]

private theorem certifiedOnticTowerToEventFlow_injective {x y : CertifiedOnticTowerUp} :
    certifiedOnticTowerToEventFlow x = certifiedOnticTowerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      certifiedOnticTowerFromEventFlow (certifiedOnticTowerToEventFlow x) =
        certifiedOnticTowerFromEventFlow (certifiedOnticTowerToEventFlow y) :=
    congrArg certifiedOnticTowerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (certifiedOnticTower_round_trip x).symm
      (Eq.trans hread (certifiedOnticTower_round_trip y)))

private theorem certifiedOnticTower_field_faithful :
    ∀ x y : CertifiedOnticTowerUp, certifiedOnticTowerFields x = certifiedOnticTowerFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk stage₁ signatures₁ refinement₁ ledger₁ classifier₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk stage₂ signatures₂ refinement₂ ledger₂ classifier₂ transport₂ replay₂ provenance₂
          name₂ =>
          cases h
          rfl

instance certifiedOnticTowerBHistCarrier : BHistCarrier CertifiedOnticTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := certifiedOnticTowerToEventFlow
  fromEventFlow := certifiedOnticTowerFromEventFlow

instance certifiedOnticTowerChapterTasteGate : ChapterTasteGate CertifiedOnticTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change certifiedOnticTowerFromEventFlow (certifiedOnticTowerToEventFlow x) = some x
    exact certifiedOnticTower_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (certifiedOnticTowerToEventFlow_injective heq)

instance certifiedOnticTowerFieldFaithful : FieldFaithful CertifiedOnticTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := certifiedOnticTowerFields
  field_faithful := certifiedOnticTower_field_faithful

instance certifiedOnticTowerNontrivial : Nontrivial CertifiedOnticTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CertifiedOnticTowerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CertifiedOnticTowerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CertifiedOnticTowerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  certifiedOnticTowerChapterTasteGate

theorem CertifiedOnticTower_ledger_continuity
    {stage signatures refinement ledger classifier transport replay provenance name : BHist} :
    certifiedOnticTowerFields
        (CertifiedOnticTowerUp.mk stage signatures refinement ledger classifier transport replay
          provenance name) =
        [stage, signatures, refinement, ledger, classifier, transport, replay, provenance, name] ∧
      certifiedOnticTowerToEventFlow
          (CertifiedOnticTowerUp.mk stage signatures refinement ledger classifier transport replay
            provenance name) =
        List.map certifiedOnticTowerEncodeBHist
          [stage, signatures, refinement, ledger, classifier, transport, replay, provenance,
            name] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · rfl

end BEDC.Derived.CertifiedOnticTowerUp
