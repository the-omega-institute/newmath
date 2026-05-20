import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedConsistencyAssemblyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedConsistencyAssemblyUp : Type where
  | mk :
      (closedness typing endpoint exclusion boundary obstruction ledger route provenance
        name : BHist) →
      ClosedConsistencyAssemblyUp
  deriving DecidableEq

def closedConsistencyAssemblyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedConsistencyAssemblyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedConsistencyAssemblyEncodeBHist h

def closedConsistencyAssemblyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedConsistencyAssemblyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedConsistencyAssemblyDecodeBHist tail)

private theorem closedConsistencyAssembly_decode_encode_bhist :
    ∀ h : BHist,
      closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedConsistencyAssemblyFields : ClosedConsistencyAssemblyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedConsistencyAssemblyUp.mk closedness typing endpoint exclusion boundary obstruction
      ledger route provenance name =>
      [closedness, typing, endpoint, exclusion, boundary, obstruction, ledger, route,
        provenance, name]

def closedConsistencyAssemblyToEventFlow : ClosedConsistencyAssemblyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedConsistencyAssemblyFields x).map closedConsistencyAssemblyEncodeBHist

def closedConsistencyAssemblyFromEventFlow : EventFlow → Option ClosedConsistencyAssemblyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | closedness :: rest0 =>
      match rest0 with
      | [] => none
      | typing :: rest1 =>
          match rest1 with
          | [] => none
          | endpoint :: rest2 =>
              match rest2 with
              | [] => none
              | exclusion :: rest3 =>
                  match rest3 with
                  | [] => none
                  | boundary :: rest4 =>
                      match rest4 with
                      | [] => none
                      | obstruction :: rest5 =>
                          match rest5 with
                          | [] => none
                          | ledger :: rest6 =>
                              match rest6 with
                              | [] => none
                              | route :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | name :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (ClosedConsistencyAssemblyUp.mk
                                                  (closedConsistencyAssemblyDecodeBHist
                                                    closedness)
                                                  (closedConsistencyAssemblyDecodeBHist typing)
                                                  (closedConsistencyAssemblyDecodeBHist
                                                    endpoint)
                                                  (closedConsistencyAssemblyDecodeBHist
                                                    exclusion)
                                                  (closedConsistencyAssemblyDecodeBHist
                                                    boundary)
                                                  (closedConsistencyAssemblyDecodeBHist
                                                    obstruction)
                                                  (closedConsistencyAssemblyDecodeBHist ledger)
                                                  (closedConsistencyAssemblyDecodeBHist route)
                                                  (closedConsistencyAssemblyDecodeBHist
                                                    provenance)
                                                  (closedConsistencyAssemblyDecodeBHist name))
                                          | _ :: _ => none

private theorem closedConsistencyAssembly_round_trip :
    ∀ x : ClosedConsistencyAssemblyUp,
      closedConsistencyAssemblyFromEventFlow (closedConsistencyAssemblyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk closedness typing endpoint exclusion boundary obstruction ledger route provenance
      name =>
      change
        some
          (ClosedConsistencyAssemblyUp.mk
            (closedConsistencyAssemblyDecodeBHist
              (closedConsistencyAssemblyEncodeBHist closedness))
            (closedConsistencyAssemblyDecodeBHist
              (closedConsistencyAssemblyEncodeBHist typing))
            (closedConsistencyAssemblyDecodeBHist
              (closedConsistencyAssemblyEncodeBHist endpoint))
            (closedConsistencyAssemblyDecodeBHist
              (closedConsistencyAssemblyEncodeBHist exclusion))
            (closedConsistencyAssemblyDecodeBHist
              (closedConsistencyAssemblyEncodeBHist boundary))
            (closedConsistencyAssemblyDecodeBHist
              (closedConsistencyAssemblyEncodeBHist obstruction))
            (closedConsistencyAssemblyDecodeBHist
              (closedConsistencyAssemblyEncodeBHist ledger))
            (closedConsistencyAssemblyDecodeBHist
              (closedConsistencyAssemblyEncodeBHist route))
            (closedConsistencyAssemblyDecodeBHist
              (closedConsistencyAssemblyEncodeBHist provenance))
            (closedConsistencyAssemblyDecodeBHist
              (closedConsistencyAssemblyEncodeBHist name))) =
          some
            (ClosedConsistencyAssemblyUp.mk closedness typing endpoint exclusion boundary
              obstruction ledger route provenance name)
      rw [closedConsistencyAssembly_decode_encode_bhist closedness,
        closedConsistencyAssembly_decode_encode_bhist typing,
        closedConsistencyAssembly_decode_encode_bhist endpoint,
        closedConsistencyAssembly_decode_encode_bhist exclusion,
        closedConsistencyAssembly_decode_encode_bhist boundary,
        closedConsistencyAssembly_decode_encode_bhist obstruction,
        closedConsistencyAssembly_decode_encode_bhist ledger,
        closedConsistencyAssembly_decode_encode_bhist route,
        closedConsistencyAssembly_decode_encode_bhist provenance,
        closedConsistencyAssembly_decode_encode_bhist name]

private theorem closedConsistencyAssemblyToEventFlow_injective
    {x y : ClosedConsistencyAssemblyUp} :
    closedConsistencyAssemblyToEventFlow x = closedConsistencyAssemblyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedConsistencyAssemblyFromEventFlow (closedConsistencyAssemblyToEventFlow x) =
        closedConsistencyAssemblyFromEventFlow (closedConsistencyAssemblyToEventFlow y) :=
    congrArg closedConsistencyAssemblyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedConsistencyAssembly_round_trip x).symm
      (Eq.trans hread (closedConsistencyAssembly_round_trip y)))

private theorem closedConsistencyAssembly_fields_faithful :
    ∀ x y : ClosedConsistencyAssemblyUp,
      closedConsistencyAssemblyFields x = closedConsistencyAssemblyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk closedness₁ typing₁ endpoint₁ exclusion₁ boundary₁ obstruction₁ ledger₁ route₁
      provenance₁ name₁ =>
      cases y with
      | mk closedness₂ typing₂ endpoint₂ exclusion₂ boundary₂ obstruction₂ ledger₂ route₂
          provenance₂ name₂ =>
          injection hfields with hClosedness tail0
          injection tail0 with hTyping tail1
          injection tail1 with hEndpoint tail2
          injection tail2 with hExclusion tail3
          injection tail3 with hBoundary tail4
          injection tail4 with hObstruction tail5
          injection tail5 with hLedger tail6
          injection tail6 with hRoute tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hName _
          subst hClosedness
          subst hTyping
          subst hEndpoint
          subst hExclusion
          subst hBoundary
          subst hObstruction
          subst hLedger
          subst hRoute
          subst hProvenance
          subst hName
          rfl

instance closedConsistencyAssemblyBHistCarrier :
    BHistCarrier ClosedConsistencyAssemblyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedConsistencyAssemblyToEventFlow
  fromEventFlow := closedConsistencyAssemblyFromEventFlow

instance closedConsistencyAssemblyChapterTasteGate :
    ChapterTasteGate ClosedConsistencyAssemblyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedConsistencyAssemblyFromEventFlow (closedConsistencyAssemblyToEventFlow x) =
        some x
    exact closedConsistencyAssembly_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedConsistencyAssemblyToEventFlow_injective heq)

instance closedConsistencyAssemblyFieldFaithful :
    FieldFaithful ClosedConsistencyAssemblyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedConsistencyAssemblyFields
  field_faithful := closedConsistencyAssembly_fields_faithful

instance closedConsistencyAssemblyNontrivial :
    Nontrivial ClosedConsistencyAssemblyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedConsistencyAssemblyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedConsistencyAssemblyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        injection h with hClosedness
        cases hClosedness⟩

def taste_gate : ChapterTasteGate ClosedConsistencyAssemblyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedConsistencyAssemblyFromEventFlow (closedConsistencyAssemblyToEventFlow x) =
        some x
    exact closedConsistencyAssembly_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedConsistencyAssemblyToEventFlow_injective heq)

theorem ClosedConsistencyAssemblyUp_namecert_obligations
    (x : ClosedConsistencyAssemblyUp) :
    SemanticNameCert
      (fun row : BHist => row ∈ closedConsistencyAssemblyFields x)
      (fun row : BHist => row ∈ closedConsistencyAssemblyFields x)
      (fun row : BHist => row ∈ closedConsistencyAssemblyFields x)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  cases x with
  | mk closedness typing endpoint exclusion boundary obstruction ledger route provenance name =>
      exact
        {
          core := {
            carrier_inhabited := Exists.intro closedness (List.Mem.head _)
            equiv_refl := by
              intro row _source
              exact hsame_refl row
            equiv_symm := by
              intro row row' same
              exact hsame_symm same
            equiv_trans := by
              intro row row' row'' sameLeft sameRight
              exact hsame_trans sameLeft sameRight
            carrier_respects_equiv := by
              intro row row' same source
              cases same
              exact source
          }
          pattern_sound := by
            intro row source
            exact source
          ledger_sound := by
            intro row source
            exact source
        }

end BEDC.Derived.ClosedConsistencyAssemblyUp
