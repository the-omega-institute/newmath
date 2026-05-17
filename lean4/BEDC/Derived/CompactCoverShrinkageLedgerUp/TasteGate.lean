import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactCoverShrinkageLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactCoverShrinkageLedgerUp : Type where
  | packet
      (compactNet uniformConsumer finiteFold metric rat route transport provenance
        name : BHist) :
      CompactCoverShrinkageLedgerUp
  deriving DecidableEq

def compactCoverShrinkageLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactCoverShrinkageLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactCoverShrinkageLedgerEncodeBHist h

def compactCoverShrinkageLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactCoverShrinkageLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactCoverShrinkageLedgerDecodeBHist tail)

private theorem compactCoverShrinkageLedgerDecode_encode_bhist :
    ∀ h : BHist,
      compactCoverShrinkageLedgerDecodeBHist
        (compactCoverShrinkageLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactCoverShrinkageLedgerFields :
    CompactCoverShrinkageLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactCoverShrinkageLedgerUp.packet compactNet uniformConsumer finiteFold metric rat route
      transport provenance name =>
      [compactNet, uniformConsumer, finiteFold, metric, rat, route, transport, provenance, name]

def compactCoverShrinkageLedgerToEventFlow :
    CompactCoverShrinkageLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (compactCoverShrinkageLedgerFields x).map compactCoverShrinkageLedgerEncodeBHist

def compactCoverShrinkageLedgerFromEventFlow :
    EventFlow → Option CompactCoverShrinkageLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | compactNet :: rest0 =>
      match rest0 with
      | [] => none
      | uniformConsumer :: rest1 =>
          match rest1 with
          | [] => none
          | finiteFold :: rest2 =>
              match rest2 with
              | [] => none
              | metric :: rest3 =>
                  match rest3 with
                  | [] => none
                  | rat :: rest4 =>
                      match rest4 with
                      | [] => none
                      | route :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | name :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (CompactCoverShrinkageLedgerUp.packet
                                              (compactCoverShrinkageLedgerDecodeBHist
                                                compactNet)
                                              (compactCoverShrinkageLedgerDecodeBHist
                                                uniformConsumer)
                                              (compactCoverShrinkageLedgerDecodeBHist
                                                finiteFold)
                                              (compactCoverShrinkageLedgerDecodeBHist metric)
                                              (compactCoverShrinkageLedgerDecodeBHist rat)
                                              (compactCoverShrinkageLedgerDecodeBHist route)
                                              (compactCoverShrinkageLedgerDecodeBHist transport)
                                              (compactCoverShrinkageLedgerDecodeBHist provenance)
                                              (compactCoverShrinkageLedgerDecodeBHist name))
                                      | _ :: _ => none

private theorem compactCoverShrinkageLedger_round_trip :
    ∀ x : CompactCoverShrinkageLedgerUp,
      compactCoverShrinkageLedgerFromEventFlow
        (compactCoverShrinkageLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | packet compactNet uniformConsumer finiteFold metric rat route transport provenance name =>
      change
        some
          (CompactCoverShrinkageLedgerUp.packet
            (compactCoverShrinkageLedgerDecodeBHist
              (compactCoverShrinkageLedgerEncodeBHist compactNet))
            (compactCoverShrinkageLedgerDecodeBHist
              (compactCoverShrinkageLedgerEncodeBHist uniformConsumer))
            (compactCoverShrinkageLedgerDecodeBHist
              (compactCoverShrinkageLedgerEncodeBHist finiteFold))
            (compactCoverShrinkageLedgerDecodeBHist
              (compactCoverShrinkageLedgerEncodeBHist metric))
            (compactCoverShrinkageLedgerDecodeBHist
              (compactCoverShrinkageLedgerEncodeBHist rat))
            (compactCoverShrinkageLedgerDecodeBHist
              (compactCoverShrinkageLedgerEncodeBHist route))
            (compactCoverShrinkageLedgerDecodeBHist
              (compactCoverShrinkageLedgerEncodeBHist transport))
            (compactCoverShrinkageLedgerDecodeBHist
              (compactCoverShrinkageLedgerEncodeBHist provenance))
            (compactCoverShrinkageLedgerDecodeBHist
              (compactCoverShrinkageLedgerEncodeBHist name))) =
          some
            (CompactCoverShrinkageLedgerUp.packet compactNet uniformConsumer finiteFold metric
              rat route transport provenance name)
      rw [compactCoverShrinkageLedgerDecode_encode_bhist compactNet,
        compactCoverShrinkageLedgerDecode_encode_bhist uniformConsumer,
        compactCoverShrinkageLedgerDecode_encode_bhist finiteFold,
        compactCoverShrinkageLedgerDecode_encode_bhist metric,
        compactCoverShrinkageLedgerDecode_encode_bhist rat,
        compactCoverShrinkageLedgerDecode_encode_bhist route,
        compactCoverShrinkageLedgerDecode_encode_bhist transport,
        compactCoverShrinkageLedgerDecode_encode_bhist provenance,
        compactCoverShrinkageLedgerDecode_encode_bhist name]

private theorem compactCoverShrinkageLedgerToEventFlow_injective
    {x y : CompactCoverShrinkageLedgerUp} :
    compactCoverShrinkageLedgerToEventFlow x =
      compactCoverShrinkageLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactCoverShrinkageLedgerFromEventFlow
          (compactCoverShrinkageLedgerToEventFlow x) =
        compactCoverShrinkageLedgerFromEventFlow
          (compactCoverShrinkageLedgerToEventFlow y) :=
    congrArg compactCoverShrinkageLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactCoverShrinkageLedger_round_trip x).symm
      (Eq.trans hread (compactCoverShrinkageLedger_round_trip y)))

instance compactCoverShrinkageLedgerBHistCarrier :
    BHistCarrier CompactCoverShrinkageLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactCoverShrinkageLedgerToEventFlow
  fromEventFlow := compactCoverShrinkageLedgerFromEventFlow

instance compactCoverShrinkageLedgerChapterTasteGate :
    ChapterTasteGate CompactCoverShrinkageLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactCoverShrinkageLedgerFromEventFlow
        (compactCoverShrinkageLedgerToEventFlow x) = some x
    exact compactCoverShrinkageLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactCoverShrinkageLedgerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactCoverShrinkageLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactCoverShrinkageLedgerFromEventFlow
        (compactCoverShrinkageLedgerToEventFlow x) = some x
    exact compactCoverShrinkageLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactCoverShrinkageLedgerToEventFlow_injective heq)

instance compactCoverShrinkageLedgerFieldFaithful :
    FieldFaithful CompactCoverShrinkageLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactCoverShrinkageLedgerFields
  field_faithful := by
    intro x y h
    cases x with
    | packet compactNet₁ uniformConsumer₁ finiteFold₁ metric₁ rat₁ route₁ transport₁
        provenance₁ name₁ =>
        cases y with
        | packet compactNet₂ uniformConsumer₂ finiteFold₂ metric₂ rat₂ route₂ transport₂
            provenance₂ name₂ =>
            injection h with hCompactNet t1
            injection t1 with hUniformConsumer t2
            injection t2 with hFiniteFold t3
            injection t3 with hMetric t4
            injection t4 with hRat t5
            injection t5 with hRoute t6
            injection t6 with hTransport t7
            injection t7 with hProvenance t8
            injection t8 with hName _
            cases hCompactNet
            cases hUniformConsumer
            cases hFiniteFold
            cases hMetric
            cases hRat
            cases hRoute
            cases hTransport
            cases hProvenance
            cases hName
            rfl

instance compactCoverShrinkageLedgerNontrivial :
    Nontrivial CompactCoverShrinkageLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactCoverShrinkageLedgerUp.packet BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactCoverShrinkageLedgerUp.packet (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

end BEDC.Derived.CompactCoverShrinkageLedgerUp
