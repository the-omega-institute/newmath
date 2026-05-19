import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyWitnessGluingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyWitnessGluingUp : Type where
  | mk
      (ledger tail synchronizer classifier stream regular dyadic realSeal witnessEdge
        transports continuations provenance nameCert : BHist) :
      CauchyWitnessGluingUp

def cauchyWitnessGluingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyWitnessGluingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyWitnessGluingEncodeBHist h

def cauchyWitnessGluingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyWitnessGluingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyWitnessGluingDecodeBHist tail)

private theorem cauchyWitnessGluingDecode_encode_bhist :
    ∀ h : BHist, cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyWitnessGluingToEventFlow : CauchyWitnessGluingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyWitnessGluingUp.mk ledger tail synchronizer classifier stream regular dyadic
      realSeal witnessEdge transports continuations provenance nameCert =>
      [cauchyWitnessGluingEncodeBHist ledger,
        cauchyWitnessGluingEncodeBHist tail,
        cauchyWitnessGluingEncodeBHist synchronizer,
        cauchyWitnessGluingEncodeBHist classifier,
        cauchyWitnessGluingEncodeBHist stream,
        cauchyWitnessGluingEncodeBHist regular,
        cauchyWitnessGluingEncodeBHist dyadic,
        cauchyWitnessGluingEncodeBHist realSeal,
        cauchyWitnessGluingEncodeBHist witnessEdge,
        cauchyWitnessGluingEncodeBHist transports,
        cauchyWitnessGluingEncodeBHist continuations,
        cauchyWitnessGluingEncodeBHist provenance,
        cauchyWitnessGluingEncodeBHist nameCert]

def cauchyWitnessGluingFromEventFlow : EventFlow → Option CauchyWitnessGluingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | ledger :: rest0 =>
      match rest0 with
      | [] => none
      | tail :: rest1 =>
          match rest1 with
          | [] => none
          | synchronizer :: rest2 =>
              match rest2 with
              | [] => none
              | classifier :: rest3 =>
                  match rest3 with
                  | [] => none
                  | stream :: rest4 =>
                      match rest4 with
                      | [] => none
                      | regular :: rest5 =>
                          match rest5 with
                          | [] => none
                          | dyadic :: rest6 =>
                              match rest6 with
                              | [] => none
                              | realSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | witnessEdge :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transports :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | continuations :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | nameCert :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (CauchyWitnessGluingUp.mk
                                                              (cauchyWitnessGluingDecodeBHist ledger)
                                                              (cauchyWitnessGluingDecodeBHist tail)
                                                              (cauchyWitnessGluingDecodeBHist synchronizer)
                                                              (cauchyWitnessGluingDecodeBHist classifier)
                                                              (cauchyWitnessGluingDecodeBHist stream)
                                                              (cauchyWitnessGluingDecodeBHist regular)
                                                              (cauchyWitnessGluingDecodeBHist dyadic)
                                                              (cauchyWitnessGluingDecodeBHist realSeal)
                                                              (cauchyWitnessGluingDecodeBHist witnessEdge)
                                                              (cauchyWitnessGluingDecodeBHist transports)
                                                              (cauchyWitnessGluingDecodeBHist continuations)
                                                              (cauchyWitnessGluingDecodeBHist provenance)
                                                              (cauchyWitnessGluingDecodeBHist nameCert))
                                                      | _ :: _ => none

private theorem cauchyWitnessGluing_round_trip :
    ∀ x : CauchyWitnessGluingUp,
      cauchyWitnessGluingFromEventFlow (cauchyWitnessGluingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk ledger tail synchronizer classifier stream regular dyadic realSeal witnessEdge
      transports continuations provenance nameCert =>
      change
        some
          (CauchyWitnessGluingUp.mk
            (cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist ledger))
            (cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist tail))
            (cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist synchronizer))
            (cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist classifier))
            (cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist stream))
            (cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist regular))
            (cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist dyadic))
            (cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist realSeal))
            (cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist witnessEdge))
            (cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist transports))
            (cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist continuations))
            (cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist provenance))
            (cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist nameCert))) =
          some
            (CauchyWitnessGluingUp.mk ledger tail synchronizer classifier stream regular
              dyadic realSeal witnessEdge transports continuations provenance nameCert)
      rw [cauchyWitnessGluingDecode_encode_bhist ledger,
        cauchyWitnessGluingDecode_encode_bhist tail,
        cauchyWitnessGluingDecode_encode_bhist synchronizer,
        cauchyWitnessGluingDecode_encode_bhist classifier,
        cauchyWitnessGluingDecode_encode_bhist stream,
        cauchyWitnessGluingDecode_encode_bhist regular,
        cauchyWitnessGluingDecode_encode_bhist dyadic,
        cauchyWitnessGluingDecode_encode_bhist realSeal,
        cauchyWitnessGluingDecode_encode_bhist witnessEdge,
        cauchyWitnessGluingDecode_encode_bhist transports,
        cauchyWitnessGluingDecode_encode_bhist continuations,
        cauchyWitnessGluingDecode_encode_bhist provenance,
        cauchyWitnessGluingDecode_encode_bhist nameCert]

private theorem cauchyWitnessGluingToEventFlow_injective {x y : CauchyWitnessGluingUp} :
    cauchyWitnessGluingToEventFlow x = cauchyWitnessGluingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyWitnessGluingFromEventFlow (cauchyWitnessGluingToEventFlow x) =
        cauchyWitnessGluingFromEventFlow (cauchyWitnessGluingToEventFlow y) :=
    congrArg cauchyWitnessGluingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyWitnessGluing_round_trip x).symm
      (Eq.trans hread (cauchyWitnessGluing_round_trip y)))

private def cauchyWitnessGluingFields : CauchyWitnessGluingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyWitnessGluingUp.mk ledger tail synchronizer classifier stream regular dyadic
      realSeal witnessEdge transports continuations provenance nameCert =>
      [ledger, tail, synchronizer, classifier, stream, regular, dyadic, realSeal,
        witnessEdge, transports, continuations, provenance, nameCert]

private theorem cauchyWitnessGluing_field_faithful :
    ∀ x y : CauchyWitnessGluingUp,
      cauchyWitnessGluingFields x = cauchyWitnessGluingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk ledger₁ tail₁ synchronizer₁ classifier₁ stream₁ regular₁ dyadic₁ realSeal₁
      witnessEdge₁ transports₁ continuations₁ provenance₁ nameCert₁ =>
      cases y with
      | mk ledger₂ tail₂ synchronizer₂ classifier₂ stream₂ regular₂ dyadic₂ realSeal₂
          witnessEdge₂ transports₂ continuations₂ provenance₂ nameCert₂ =>
          cases h
          rfl

instance cauchyWitnessGluingBHistCarrier : BHistCarrier CauchyWitnessGluingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyWitnessGluingToEventFlow
  fromEventFlow := cauchyWitnessGluingFromEventFlow

instance cauchyWitnessGluingChapterTasteGate : ChapterTasteGate CauchyWitnessGluingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyWitnessGluingFromEventFlow (cauchyWitnessGluingToEventFlow x) = some x
    exact cauchyWitnessGluing_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyWitnessGluingToEventFlow_injective heq)

instance cauchyWitnessGluingFieldFaithful : FieldFaithful CauchyWitnessGluingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyWitnessGluingFields
  field_faithful := cauchyWitnessGluing_field_faithful

instance cauchyWitnessGluingNontrivial : Nontrivial CauchyWitnessGluingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyWitnessGluingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyWitnessGluingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyWitnessGluingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyWitnessGluingChapterTasteGate

theorem CauchyWitnessGluingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyWitnessGluingUp) ∧
      Nonempty (FieldFaithful CauchyWitnessGluingUp) ∧
      Nonempty (Nontrivial CauchyWitnessGluingUp) ∧
      (∀ h : BHist, cauchyWitnessGluingDecodeBHist (cauchyWitnessGluingEncodeBHist h) = h) ∧
      (∀ x : CauchyWitnessGluingUp,
        cauchyWitnessGluingFromEventFlow (cauchyWitnessGluingToEventFlow x) = some x) ∧
      cauchyWitnessGluingEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨{
      round_trip := by
        intro x
        change cauchyWitnessGluingFromEventFlow (cauchyWitnessGluingToEventFlow x) = some x
        exact cauchyWitnessGluing_round_trip x
      layer_separation := by
        intro x y hxy heq
        exact hxy (cauchyWitnessGluingToEventFlow_injective heq)
    }⟩
  · constructor
    · exact ⟨{
        fields := cauchyWitnessGluingFields
        field_faithful := cauchyWitnessGluing_field_faithful
      }⟩
    · constructor
      · exact ⟨{
          witness_pair :=
            ⟨CauchyWitnessGluingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty,
              CauchyWitnessGluingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
              by
                intro h
                cases h⟩
        }⟩
      · exact
          ⟨cauchyWitnessGluingDecode_encode_bhist, cauchyWitnessGluing_round_trip, rfl⟩

theorem CauchyWitnessGluingCarrier_budget_compatibility [AskSetup] [PackageSetup]
    {ledger tail synchronizer classifier stream regular dyadic realSeal witnessEdge transports
      continuations provenance nameCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont ledger tail synchronizer →
      Cont synchronizer classifier realSeal →
        Cont stream dyadic regular →
          Cont regular realSeal consumer →
            PkgSig bundle consumer pkg →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row consumer ∧
                    ∃ packet : CauchyWitnessGluingUp,
                      packet = CauchyWitnessGluingUp.mk ledger tail synchronizer classifier stream
                        regular dyadic realSeal witnessEdge transports continuations provenance
                        nameCert)
                (fun row : BHist =>
                  Cont ledger tail synchronizer ∧ Cont synchronizer classifier realSeal ∧
                    Cont stream dyadic regular ∧ Cont regular realSeal consumer ∧
                      hsame row consumer)
                (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro ledgerTail synchronizerClassifier streamRegular regularConsumer consumerPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumer
          ⟨hsame_refl consumer,
            Exists.intro
              (CauchyWitnessGluingUp.mk ledger tail synchronizer classifier stream regular dyadic
                realSeal witnessEdge transports continuations provenance nameCert)
              rfl⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨ledgerTail, synchronizerClassifier, streamRegular, regularConsumer, sourceRow.left⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, consumerPkg⟩
  }

end BEDC.Derived.CauchyWitnessGluingUp
