import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletionExactBoundaryUp : Type where
  | mk :
      (limitSeal classifier witness synchronizer window readback dyadic terminal transport replay
        provenance nameCert : BHist) →
        RealCompletionExactBoundaryUp
  deriving DecidableEq

def realCompletionExactBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionExactBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionExactBoundaryEncodeBHist h

def realCompletionExactBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionExactBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionExactBoundaryDecodeBHist tail)

private theorem realCompletionExactBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem realCompletionExactBoundary_mk_congr
    {limitSeal limitSeal' classifier classifier' witness witness' synchronizer synchronizer'
      window window' readback readback' dyadic dyadic' terminal terminal'
      transport transport' replay replay' provenance provenance' nameCert nameCert' : BHist}
    (hSeal : limitSeal' = limitSeal)
    (hClassifier : classifier' = classifier)
    (hWitness : witness' = witness)
    (hSynchronizer : synchronizer' = synchronizer)
    (hWindow : window' = window)
    (hReadback : readback' = readback)
    (hDyadic : dyadic' = dyadic)
    (hTerminal : terminal' = terminal)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    RealCompletionExactBoundaryUp.mk limitSeal' classifier' witness' synchronizer' window'
        readback' dyadic' terminal' transport' replay' provenance' nameCert' =
      RealCompletionExactBoundaryUp.mk limitSeal classifier witness synchronizer window readback
        dyadic terminal transport replay provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSeal
  cases hClassifier
  cases hWitness
  cases hSynchronizer
  cases hWindow
  cases hReadback
  cases hDyadic
  cases hTerminal
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hNameCert
  rfl

def realCompletionExactBoundaryFields :
    RealCompletionExactBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionExactBoundaryUp.mk limitSeal classifier witness synchronizer window readback
      dyadic terminal transport replay provenance nameCert =>
      [limitSeal, classifier, witness, synchronizer, window, readback, dyadic, terminal,
        transport, replay, provenance, nameCert]

def realCompletionExactBoundaryToEventFlow :
    RealCompletionExactBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionExactBoundaryUp.mk limitSeal classifier witness synchronizer window readback
      dyadic terminal transport replay provenance nameCert =>
      [[BMark.b0],
        realCompletionExactBoundaryEncodeBHist limitSeal,
        [BMark.b1, BMark.b0],
        realCompletionExactBoundaryEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b0],
        realCompletionExactBoundaryEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionExactBoundaryEncodeBHist synchronizer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionExactBoundaryEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionExactBoundaryEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionExactBoundaryEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realCompletionExactBoundaryEncodeBHist terminal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realCompletionExactBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realCompletionExactBoundaryEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionExactBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionExactBoundaryEncodeBHist nameCert]

private def realCompletionExactBoundaryEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      realCompletionExactBoundaryEventAtDefault index rest

def realCompletionExactBoundaryFromEventFlow
    (ef : EventFlow) : Option RealCompletionExactBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealCompletionExactBoundaryUp.mk
      (realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEventAtDefault 1 ef))
      (realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEventAtDefault 3 ef))
      (realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEventAtDefault 5 ef))
      (realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEventAtDefault 7 ef))
      (realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEventAtDefault 9 ef))
      (realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEventAtDefault 11 ef))
      (realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEventAtDefault 13 ef))
      (realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEventAtDefault 15 ef))
      (realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEventAtDefault 17 ef))
      (realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEventAtDefault 19 ef))
      (realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEventAtDefault 21 ef))
      (realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEventAtDefault 23 ef)))

private theorem realCompletionExactBoundary_round_trip :
    ∀ x : RealCompletionExactBoundaryUp,
      realCompletionExactBoundaryFromEventFlow
        (realCompletionExactBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk limitSeal classifier witness synchronizer window readback dyadic terminal transport replay
      provenance nameCert =>
      change
        some
          (RealCompletionExactBoundaryUp.mk
            (realCompletionExactBoundaryDecodeBHist
              (realCompletionExactBoundaryEncodeBHist limitSeal))
            (realCompletionExactBoundaryDecodeBHist
              (realCompletionExactBoundaryEncodeBHist classifier))
            (realCompletionExactBoundaryDecodeBHist
              (realCompletionExactBoundaryEncodeBHist witness))
            (realCompletionExactBoundaryDecodeBHist
              (realCompletionExactBoundaryEncodeBHist synchronizer))
            (realCompletionExactBoundaryDecodeBHist
              (realCompletionExactBoundaryEncodeBHist window))
            (realCompletionExactBoundaryDecodeBHist
              (realCompletionExactBoundaryEncodeBHist readback))
            (realCompletionExactBoundaryDecodeBHist
              (realCompletionExactBoundaryEncodeBHist dyadic))
            (realCompletionExactBoundaryDecodeBHist
              (realCompletionExactBoundaryEncodeBHist terminal))
            (realCompletionExactBoundaryDecodeBHist
              (realCompletionExactBoundaryEncodeBHist transport))
            (realCompletionExactBoundaryDecodeBHist
              (realCompletionExactBoundaryEncodeBHist replay))
            (realCompletionExactBoundaryDecodeBHist
              (realCompletionExactBoundaryEncodeBHist provenance))
            (realCompletionExactBoundaryDecodeBHist
              (realCompletionExactBoundaryEncodeBHist nameCert))) =
          some
            (RealCompletionExactBoundaryUp.mk limitSeal classifier witness synchronizer window
              readback dyadic terminal transport replay provenance nameCert)
      exact
        congrArg some
          (realCompletionExactBoundary_mk_congr
            (realCompletionExactBoundaryDecode_encode_bhist limitSeal)
            (realCompletionExactBoundaryDecode_encode_bhist classifier)
            (realCompletionExactBoundaryDecode_encode_bhist witness)
            (realCompletionExactBoundaryDecode_encode_bhist synchronizer)
            (realCompletionExactBoundaryDecode_encode_bhist window)
            (realCompletionExactBoundaryDecode_encode_bhist readback)
            (realCompletionExactBoundaryDecode_encode_bhist dyadic)
            (realCompletionExactBoundaryDecode_encode_bhist terminal)
            (realCompletionExactBoundaryDecode_encode_bhist transport)
            (realCompletionExactBoundaryDecode_encode_bhist replay)
            (realCompletionExactBoundaryDecode_encode_bhist provenance)
            (realCompletionExactBoundaryDecode_encode_bhist nameCert))

private theorem realCompletionExactBoundaryToEventFlow_injective
    {x y : RealCompletionExactBoundaryUp} :
    realCompletionExactBoundaryToEventFlow x =
      realCompletionExactBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletionExactBoundaryFromEventFlow
          (realCompletionExactBoundaryToEventFlow x) =
        realCompletionExactBoundaryFromEventFlow
          (realCompletionExactBoundaryToEventFlow y) :=
    congrArg realCompletionExactBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCompletionExactBoundary_round_trip x).symm
      (Eq.trans hread (realCompletionExactBoundary_round_trip y)))

private theorem realCompletionExactBoundary_fields_faithful :
    ∀ x y : RealCompletionExactBoundaryUp,
      realCompletionExactBoundaryFields x =
        realCompletionExactBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk limitSeal₁ classifier₁ witness₁ synchronizer₁ window₁ readback₁ dyadic₁ terminal₁
      transport₁ replay₁ provenance₁ nameCert₁ =>
      cases y with
      | mk limitSeal₂ classifier₂ witness₂ synchronizer₂ window₂ readback₂ dyadic₂ terminal₂
          transport₂ replay₂ provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance realCompletionExactBoundaryBHistCarrier :
    BHistCarrier RealCompletionExactBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletionExactBoundaryToEventFlow
  fromEventFlow := realCompletionExactBoundaryFromEventFlow

instance realCompletionExactBoundaryChapterTasteGate :
    ChapterTasteGate RealCompletionExactBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCompletionExactBoundaryFromEventFlow
        (realCompletionExactBoundaryToEventFlow x) = some x
    exact realCompletionExactBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletionExactBoundaryToEventFlow_injective heq)

instance realCompletionExactBoundaryFieldFaithful :
    FieldFaithful RealCompletionExactBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realCompletionExactBoundaryFields
  field_faithful := realCompletionExactBoundary_fields_faithful

instance realCompletionExactBoundaryNontrivial :
    Nontrivial RealCompletionExactBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCompletionExactBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RealCompletionExactBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealCompletionExactBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCompletionExactBoundaryChapterTasteGate

theorem RealCompletionExactBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realCompletionExactBoundaryDecodeBHist
        (realCompletionExactBoundaryEncodeBHist h) = h) ∧
      (∀ x : RealCompletionExactBoundaryUp,
        realCompletionExactBoundaryFromEventFlow
          (realCompletionExactBoundaryToEventFlow x) = some x) ∧
        (∀ x y : RealCompletionExactBoundaryUp,
          realCompletionExactBoundaryToEventFlow x =
            realCompletionExactBoundaryToEventFlow y → x = y) ∧
          realCompletionExactBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realCompletionExactBoundaryDecode_encode_bhist
  · constructor
    · exact realCompletionExactBoundary_round_trip
    · constructor
      · intro x y heq
        exact realCompletionExactBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealCompletionExactBoundaryUp
