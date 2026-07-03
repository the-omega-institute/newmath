import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ActiveReadingGateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ActiveReadingGateUp : Type where
  | mk : (target active retired blocking exportRow transport replay provenance name : BHist) →
      ActiveReadingGateUp
  deriving DecidableEq

def activeReadingGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: activeReadingGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: activeReadingGateEncodeBHist h

def activeReadingGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (activeReadingGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (activeReadingGateDecodeBHist tail)

private theorem activeReadingGate_decode_encode_bhist :
    ∀ h : BHist, activeReadingGateDecodeBHist (activeReadingGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def activeReadingGateFields : ActiveReadingGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ActiveReadingGateUp.mk target active retired blocking exportRow transport replay provenance
      name =>
      [target, active, retired, blocking, exportRow, transport, replay, provenance, name]

def activeReadingGateToEventFlow : ActiveReadingGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map activeReadingGateEncodeBHist (activeReadingGateFields x)

def activeReadingGateFromEventFlow : EventFlow → Option ActiveReadingGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | target :: rest0 =>
      match rest0 with
      | [] => none
      | active :: rest1 =>
          match rest1 with
          | [] => none
          | retired :: rest2 =>
              match rest2 with
              | [] => none
              | blocking :: rest3 =>
                  match rest3 with
                  | [] => none
                  | exportRow :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | name :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (ActiveReadingGateUp.mk
                                              (activeReadingGateDecodeBHist target)
                                              (activeReadingGateDecodeBHist active)
                                              (activeReadingGateDecodeBHist retired)
                                              (activeReadingGateDecodeBHist blocking)
                                              (activeReadingGateDecodeBHist exportRow)
                                              (activeReadingGateDecodeBHist transport)
                                              (activeReadingGateDecodeBHist replay)
                                              (activeReadingGateDecodeBHist provenance)
                                              (activeReadingGateDecodeBHist name))
                                      | _ :: _ => none

private theorem activeReadingGate_round_trip :
    ∀ x : ActiveReadingGateUp,
      activeReadingGateFromEventFlow (activeReadingGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk target active retired blocking exportRow transport replay provenance name =>
      change
        some
          (ActiveReadingGateUp.mk
            (activeReadingGateDecodeBHist (activeReadingGateEncodeBHist target))
            (activeReadingGateDecodeBHist (activeReadingGateEncodeBHist active))
            (activeReadingGateDecodeBHist (activeReadingGateEncodeBHist retired))
            (activeReadingGateDecodeBHist (activeReadingGateEncodeBHist blocking))
            (activeReadingGateDecodeBHist (activeReadingGateEncodeBHist exportRow))
            (activeReadingGateDecodeBHist (activeReadingGateEncodeBHist transport))
            (activeReadingGateDecodeBHist (activeReadingGateEncodeBHist replay))
            (activeReadingGateDecodeBHist (activeReadingGateEncodeBHist provenance))
            (activeReadingGateDecodeBHist (activeReadingGateEncodeBHist name))) =
          some
            (ActiveReadingGateUp.mk target active retired blocking exportRow transport replay
              provenance name)
      rw [activeReadingGate_decode_encode_bhist target,
        activeReadingGate_decode_encode_bhist active,
        activeReadingGate_decode_encode_bhist retired,
        activeReadingGate_decode_encode_bhist blocking,
        activeReadingGate_decode_encode_bhist exportRow,
        activeReadingGate_decode_encode_bhist transport,
        activeReadingGate_decode_encode_bhist replay,
        activeReadingGate_decode_encode_bhist provenance,
        activeReadingGate_decode_encode_bhist name]

private theorem activeReadingGateToEventFlow_injective {x y : ActiveReadingGateUp} :
    activeReadingGateToEventFlow x = activeReadingGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      activeReadingGateFromEventFlow (activeReadingGateToEventFlow x) =
        activeReadingGateFromEventFlow (activeReadingGateToEventFlow y) :=
    congrArg activeReadingGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (activeReadingGate_round_trip x).symm
      (Eq.trans hread (activeReadingGate_round_trip y)))

private theorem activeReadingGate_field_faithful :
    ∀ x y : ActiveReadingGateUp, activeReadingGateFields x = activeReadingGateFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk target₁ active₁ retired₁ blocking₁ export₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk target₂ active₂ retired₂ blocking₂ export₂ transport₂ replay₂ provenance₂ name₂ =>
          cases h
          rfl

instance activeReadingGateBHistCarrier : BHistCarrier ActiveReadingGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := activeReadingGateToEventFlow
  fromEventFlow := activeReadingGateFromEventFlow

instance activeReadingGateChapterTasteGate : ChapterTasteGate ActiveReadingGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change activeReadingGateFromEventFlow (activeReadingGateToEventFlow x) = some x
    exact activeReadingGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (activeReadingGateToEventFlow_injective heq)

instance activeReadingGateFieldFaithful : FieldFaithful ActiveReadingGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := activeReadingGateFields
  field_faithful := activeReadingGate_field_faithful

instance activeReadingGateNontrivial : Nontrivial ActiveReadingGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ActiveReadingGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ActiveReadingGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ActiveReadingGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  activeReadingGateChapterTasteGate

theorem ActiveReadingGateTasteGate_single_carrier_alignment :
    (∀ h : BHist, activeReadingGateDecodeBHist (activeReadingGateEncodeBHist h) = h) ∧
      (∀ x : ActiveReadingGateUp,
        activeReadingGateFromEventFlow (activeReadingGateToEventFlow x) = some x) ∧
        (∀ x y : ActiveReadingGateUp,
          activeReadingGateToEventFlow x = activeReadingGateToEventFlow y → x = y) ∧
          activeReadingGateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact activeReadingGate_decode_encode_bhist
  · constructor
    · exact activeReadingGate_round_trip
    · constructor
      · intro x y heq
        exact activeReadingGateToEventFlow_injective heq
      · rfl

theorem ActiveReadingGateCarrier_export_uniqueness
    {target active retired blocking exportRow transport replay provenance nameCert
      exportRead : BHist} :
    UnaryHistory target ->
      UnaryHistory active ->
        UnaryHistory blocking ->
          UnaryHistory exportRow ->
            Cont target active blocking ->
              Cont blocking exportRow exportRead ->
                hsame exportRead nameCert ->
                  activeReadingGateFields
                      (ActiveReadingGateUp.mk target active retired blocking exportRow
                        transport replay provenance nameCert) =
                    [target, active, retired, blocking, exportRow, transport, replay,
                      provenance, nameCert] ∧
                    SemanticNameCert
                        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row target ∨ hsame row active ∨ hsame row blocking ∨
                            hsame row exportRow ∨ hsame row exportRead)
                        (fun row : BHist =>
                          hsame row exportRead ∧ Cont target active blocking ∧
                            Cont blocking exportRow exportRead)
                        hsame ∧
                      UnaryHistory exportRead ∧ UnaryHistory nameCert := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryTarget unaryActive unaryBlocking unaryExport targetActive blockingExport
    exportName
  have unaryExportRead : UnaryHistory exportRead :=
    unary_cont_closed unaryBlocking unaryExport blockingExport
  have unaryNameCert : UnaryHistory nameCert :=
    unary_transport unaryExportRead exportName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row target ∨ hsame row active ∨ hsame row blocking ∨
              hsame row exportRow ∨ hsame row exportRead)
          (fun row : BHist =>
            hsame row exportRead ∧ Cont target active blocking ∧
              Cont blocking exportRow exportRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead ⟨hsame_refl exportRead, unaryExportRead⟩
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, targetActive, blockingExport⟩
  }
  exact ⟨rfl, cert, unaryExportRead, unaryNameCert⟩

end BEDC.Derived.ActiveReadingGateUp
