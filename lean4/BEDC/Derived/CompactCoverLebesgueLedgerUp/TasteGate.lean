import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactCoverLebesgueLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactCoverLebesgueLedgerUp : Type where
  | mk :
      (compactNet pointwiseRadius ratLedger lowerBoundFold uniformModulus transport route
        provenance name : BHist) →
      CompactCoverLebesgueLedgerUp
  deriving DecidableEq

def compactCoverLebesgueLedgerEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactCoverLebesgueLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactCoverLebesgueLedgerEncodeBHist h

def compactCoverLebesgueLedgerDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactCoverLebesgueLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactCoverLebesgueLedgerDecodeBHist tail)

private theorem compactCoverLebesgueLedgerDecode_encode_bhist :
    ∀ h : BHist,
      compactCoverLebesgueLedgerDecodeBHist
        (compactCoverLebesgueLedgerEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactCoverLebesgueLedgerFields :
    CompactCoverLebesgueLedgerUp → List BHist
  | CompactCoverLebesgueLedgerUp.mk compactNet pointwiseRadius ratLedger lowerBoundFold
      uniformModulus transport route provenance name =>
      [compactNet, pointwiseRadius, ratLedger, lowerBoundFold, uniformModulus, transport,
        route, provenance, name]

def compactCoverLebesgueLedgerToEventFlow :
    CompactCoverLebesgueLedgerUp → EventFlow
  | x => (compactCoverLebesgueLedgerFields x).map compactCoverLebesgueLedgerEncodeBHist

def compactCoverLebesgueLedgerFromEventFlow :
    EventFlow → Option CompactCoverLebesgueLedgerUp
  | [] => none
  | compactNet :: rest0 =>
      match rest0 with
      | [] => none
      | pointwiseRadius :: rest1 =>
          match rest1 with
          | [] => none
          | ratLedger :: rest2 =>
              match rest2 with
              | [] => none
              | lowerBoundFold :: rest3 =>
                  match rest3 with
                  | [] => none
                  | uniformModulus :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | route :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | name :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (CompactCoverLebesgueLedgerUp.mk
                                              (compactCoverLebesgueLedgerDecodeBHist
                                                compactNet)
                                              (compactCoverLebesgueLedgerDecodeBHist
                                                pointwiseRadius)
                                              (compactCoverLebesgueLedgerDecodeBHist
                                                ratLedger)
                                              (compactCoverLebesgueLedgerDecodeBHist
                                                lowerBoundFold)
                                              (compactCoverLebesgueLedgerDecodeBHist
                                                uniformModulus)
                                              (compactCoverLebesgueLedgerDecodeBHist
                                                transport)
                                              (compactCoverLebesgueLedgerDecodeBHist route)
                                              (compactCoverLebesgueLedgerDecodeBHist
                                                provenance)
                                              (compactCoverLebesgueLedgerDecodeBHist name))
                                      | _ :: _ => none

private theorem compactCoverLebesgueLedger_round_trip :
    ∀ x : CompactCoverLebesgueLedgerUp,
      compactCoverLebesgueLedgerFromEventFlow
        (compactCoverLebesgueLedgerToEventFlow x) = some x := by
  intro x
  cases x with
  | mk compactNet pointwiseRadius ratLedger lowerBoundFold uniformModulus transport route
      provenance name =>
      change
        some
          (CompactCoverLebesgueLedgerUp.mk
            (compactCoverLebesgueLedgerDecodeBHist
              (compactCoverLebesgueLedgerEncodeBHist compactNet))
            (compactCoverLebesgueLedgerDecodeBHist
              (compactCoverLebesgueLedgerEncodeBHist pointwiseRadius))
            (compactCoverLebesgueLedgerDecodeBHist
              (compactCoverLebesgueLedgerEncodeBHist ratLedger))
            (compactCoverLebesgueLedgerDecodeBHist
              (compactCoverLebesgueLedgerEncodeBHist lowerBoundFold))
            (compactCoverLebesgueLedgerDecodeBHist
              (compactCoverLebesgueLedgerEncodeBHist uniformModulus))
            (compactCoverLebesgueLedgerDecodeBHist
              (compactCoverLebesgueLedgerEncodeBHist transport))
            (compactCoverLebesgueLedgerDecodeBHist
              (compactCoverLebesgueLedgerEncodeBHist route))
            (compactCoverLebesgueLedgerDecodeBHist
              (compactCoverLebesgueLedgerEncodeBHist provenance))
            (compactCoverLebesgueLedgerDecodeBHist
              (compactCoverLebesgueLedgerEncodeBHist name))) =
          some
            (CompactCoverLebesgueLedgerUp.mk compactNet pointwiseRadius ratLedger
              lowerBoundFold uniformModulus transport route provenance name)
      rw [compactCoverLebesgueLedgerDecode_encode_bhist compactNet,
        compactCoverLebesgueLedgerDecode_encode_bhist pointwiseRadius,
        compactCoverLebesgueLedgerDecode_encode_bhist ratLedger,
        compactCoverLebesgueLedgerDecode_encode_bhist lowerBoundFold,
        compactCoverLebesgueLedgerDecode_encode_bhist uniformModulus,
        compactCoverLebesgueLedgerDecode_encode_bhist transport,
        compactCoverLebesgueLedgerDecode_encode_bhist route,
        compactCoverLebesgueLedgerDecode_encode_bhist provenance,
        compactCoverLebesgueLedgerDecode_encode_bhist name]

private theorem compactCoverLebesgueLedgerToEventFlow_injective
    {x y : CompactCoverLebesgueLedgerUp} :
    compactCoverLebesgueLedgerToEventFlow x =
      compactCoverLebesgueLedgerToEventFlow y → x = y := by
  intro heq
  have hread :
      compactCoverLebesgueLedgerFromEventFlow
          (compactCoverLebesgueLedgerToEventFlow x) =
        compactCoverLebesgueLedgerFromEventFlow
          (compactCoverLebesgueLedgerToEventFlow y) :=
    congrArg compactCoverLebesgueLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactCoverLebesgueLedger_round_trip x).symm
      (Eq.trans hread (compactCoverLebesgueLedger_round_trip y)))

instance compactCoverLebesgueLedgerBHistCarrier :
    BHistCarrier CompactCoverLebesgueLedgerUp where
  toEventFlow := compactCoverLebesgueLedgerToEventFlow
  fromEventFlow := compactCoverLebesgueLedgerFromEventFlow

instance compactCoverLebesgueLedgerChapterTasteGate :
    ChapterTasteGate CompactCoverLebesgueLedgerUp where
  round_trip := by
    intro x
    change
      compactCoverLebesgueLedgerFromEventFlow
        (compactCoverLebesgueLedgerToEventFlow x) = some x
    exact compactCoverLebesgueLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactCoverLebesgueLedgerToEventFlow_injective heq)

instance compactCoverLebesgueLedgerFieldFaithful :
    FieldFaithful CompactCoverLebesgueLedgerUp where
  fields := compactCoverLebesgueLedgerFields
  field_faithful := by
    intro x y h
    cases x with
    | mk compactNet₁ pointwiseRadius₁ ratLedger₁ lowerBoundFold₁ uniformModulus₁
        transport₁ route₁ provenance₁ name₁ =>
        cases y with
        | mk compactNet₂ pointwiseRadius₂ ratLedger₂ lowerBoundFold₂ uniformModulus₂
            transport₂ route₂ provenance₂ name₂ =>
            injection h with hCompactNet hRest₁
            injection hRest₁ with hPointwiseRadius hRest₂
            injection hRest₂ with hRatLedger hRest₃
            injection hRest₃ with hLowerBoundFold hRest₄
            injection hRest₄ with hUniformModulus hRest₅
            injection hRest₅ with hTransport hRest₆
            injection hRest₆ with hRoute hRest₇
            injection hRest₇ with hProvenance hRest₈
            injection hRest₈ with hName _
            subst hCompactNet
            subst hPointwiseRadius
            subst hRatLedger
            subst hLowerBoundFold
            subst hUniformModulus
            subst hTransport
            subst hRoute
            subst hProvenance
            subst hName
            rfl

instance compactCoverLebesgueLedgerNontrivial :
    Nontrivial CompactCoverLebesgueLedgerUp where
  witness_pair :=
    ⟨CompactCoverLebesgueLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactCoverLebesgueLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactCoverLebesgueLedgerUp :=
  compactCoverLebesgueLedgerChapterTasteGate

theorem CompactCoverLebesgueLedgerTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CompactCoverLebesgueLedgerUp) ∧
      Nonempty (ChapterTasteGate CompactCoverLebesgueLedgerUp) ∧
        Nonempty (FieldFaithful CompactCoverLebesgueLedgerUp) ∧
          Nonempty (Nontrivial CompactCoverLebesgueLedgerUp) ∧
            compactCoverLebesgueLedgerEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              compactCoverLebesgueLedgerEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  constructor
  · exact ⟨compactCoverLebesgueLedgerBHistCarrier⟩
  · constructor
    · exact ⟨compactCoverLebesgueLedgerChapterTasteGate⟩
    · constructor
      · exact ⟨compactCoverLebesgueLedgerFieldFaithful⟩
      · constructor
        · exact ⟨compactCoverLebesgueLedgerNontrivial⟩
        · constructor
          · rfl
          · rfl

theorem CompactCoverLebesgueLedgerCarrier_namecert_obligations
    (x : CompactCoverLebesgueLedgerUp) :
    FieldFaithful.fields x = compactCoverLebesgueLedgerFields x ∧
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
        ∃ compactNet pointwiseRadius ratLedger lowerBoundFold uniformModulus transport route
            provenance name : BHist,
          x =
              CompactCoverLebesgueLedgerUp.mk compactNet pointwiseRadius ratLedger
                lowerBoundFold uniformModulus transport route provenance name ∧
            compactCoverLebesgueLedgerFields x =
              [compactNet, pointwiseRadius, ratLedger, lowerBoundFold, uniformModulus,
                transport, route, provenance, name] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk compactNet pointwiseRadius ratLedger lowerBoundFold uniformModulus transport route
      provenance name =>
      constructor
      · rfl
      · constructor
        · change
            compactCoverLebesgueLedgerFromEventFlow
              (compactCoverLebesgueLedgerToEventFlow
                (CompactCoverLebesgueLedgerUp.mk compactNet pointwiseRadius ratLedger
                  lowerBoundFold uniformModulus transport route provenance name)) =
              some
                (CompactCoverLebesgueLedgerUp.mk compactNet pointwiseRadius ratLedger
                  lowerBoundFold uniformModulus transport route provenance name)
          exact
            compactCoverLebesgueLedger_round_trip
              (CompactCoverLebesgueLedgerUp.mk compactNet pointwiseRadius ratLedger
                lowerBoundFold uniformModulus transport route provenance name)
        · exact
            ⟨compactNet, pointwiseRadius, ratLedger, lowerBoundFold, uniformModulus,
              transport, route, provenance, name, rfl, rfl⟩

end BEDC.Derived.CompactCoverLebesgueLedgerUp
