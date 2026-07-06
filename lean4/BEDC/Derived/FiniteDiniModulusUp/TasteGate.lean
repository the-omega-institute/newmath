import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteDiniModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteDiniModulusUp : Type where
  | mk :
      (compactNet graph realSeal monotoneDescent dyadicTolerance finiteBudget transport
        replay provenance localName : BHist) →
        FiniteDiniModulusUp
  deriving DecidableEq

def finiteDiniModulusFields : FiniteDiniModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDiniModulusUp.mk compactNet graph realSeal monotoneDescent dyadicTolerance
      finiteBudget transport replay provenance localName =>
      [compactNet, graph, realSeal, monotoneDescent, dyadicTolerance, finiteBudget,
        transport, replay, provenance, localName]

def finiteDiniModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteDiniModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteDiniModulusEncodeBHist h

def finiteDiniModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteDiniModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteDiniModulusDecodeBHist tail)

private theorem finiteDiniModulusDecodeEncodeBHist :
    ∀ h : BHist, finiteDiniModulusDecodeBHist (finiteDiniModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteDiniModulusToEventFlow : FiniteDiniModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDiniModulusUp.mk compactNet graph realSeal monotoneDescent dyadicTolerance
      finiteBudget transport replay provenance localName =>
      [[BMark.b0],
        finiteDiniModulusEncodeBHist compactNet,
        [BMark.b1, BMark.b0],
        finiteDiniModulusEncodeBHist graph,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteDiniModulusEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteDiniModulusEncodeBHist monotoneDescent,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteDiniModulusEncodeBHist dyadicTolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteDiniModulusEncodeBHist finiteBudget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteDiniModulusEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteDiniModulusEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteDiniModulusEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finiteDiniModulusEncodeBHist localName]

private def finiteDiniModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteDiniModulusEventAtDefault index rest

def finiteDiniModulusFromEventFlow (ef : EventFlow) : Option FiniteDiniModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteDiniModulusUp.mk
      (finiteDiniModulusDecodeBHist (finiteDiniModulusEventAtDefault 1 ef))
      (finiteDiniModulusDecodeBHist (finiteDiniModulusEventAtDefault 3 ef))
      (finiteDiniModulusDecodeBHist (finiteDiniModulusEventAtDefault 5 ef))
      (finiteDiniModulusDecodeBHist (finiteDiniModulusEventAtDefault 7 ef))
      (finiteDiniModulusDecodeBHist (finiteDiniModulusEventAtDefault 9 ef))
      (finiteDiniModulusDecodeBHist (finiteDiniModulusEventAtDefault 11 ef))
      (finiteDiniModulusDecodeBHist (finiteDiniModulusEventAtDefault 13 ef))
      (finiteDiniModulusDecodeBHist (finiteDiniModulusEventAtDefault 15 ef))
      (finiteDiniModulusDecodeBHist (finiteDiniModulusEventAtDefault 17 ef))
      (finiteDiniModulusDecodeBHist (finiteDiniModulusEventAtDefault 19 ef)))

private theorem finiteDiniModulus_mk_congr
    {compactNet compactNet' graph graph' realSeal realSeal'
      monotoneDescent monotoneDescent' dyadicTolerance dyadicTolerance'
      finiteBudget finiteBudget' transport transport' replay replay' provenance provenance'
      localName localName' : BHist}
    (hCompactNet : compactNet' = compactNet)
    (hGraph : graph' = graph)
    (hRealSeal : realSeal' = realSeal)
    (hMonotoneDescent : monotoneDescent' = monotoneDescent)
    (hDyadicTolerance : dyadicTolerance' = dyadicTolerance)
    (hFiniteBudget : finiteBudget' = finiteBudget)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    FiniteDiniModulusUp.mk compactNet' graph' realSeal' monotoneDescent'
        dyadicTolerance' finiteBudget' transport' replay' provenance' localName' =
      FiniteDiniModulusUp.mk compactNet graph realSeal monotoneDescent dyadicTolerance
        finiteBudget transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hCompactNet
  cases hGraph
  cases hRealSeal
  cases hMonotoneDescent
  cases hDyadicTolerance
  cases hFiniteBudget
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

private theorem finiteDiniModulus_round_trip :
    ∀ x : FiniteDiniModulusUp,
      finiteDiniModulusFromEventFlow (finiteDiniModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactNet graph realSeal monotoneDescent dyadicTolerance finiteBudget transport replay
      provenance localName =>
      change
        some
            (FiniteDiniModulusUp.mk
              (finiteDiniModulusDecodeBHist (finiteDiniModulusEncodeBHist compactNet))
              (finiteDiniModulusDecodeBHist (finiteDiniModulusEncodeBHist graph))
              (finiteDiniModulusDecodeBHist (finiteDiniModulusEncodeBHist realSeal))
              (finiteDiniModulusDecodeBHist (finiteDiniModulusEncodeBHist monotoneDescent))
              (finiteDiniModulusDecodeBHist (finiteDiniModulusEncodeBHist dyadicTolerance))
              (finiteDiniModulusDecodeBHist (finiteDiniModulusEncodeBHist finiteBudget))
              (finiteDiniModulusDecodeBHist (finiteDiniModulusEncodeBHist transport))
              (finiteDiniModulusDecodeBHist (finiteDiniModulusEncodeBHist replay))
              (finiteDiniModulusDecodeBHist (finiteDiniModulusEncodeBHist provenance))
              (finiteDiniModulusDecodeBHist (finiteDiniModulusEncodeBHist localName))) =
          some
            (FiniteDiniModulusUp.mk compactNet graph realSeal monotoneDescent
              dyadicTolerance finiteBudget transport replay provenance localName)
      exact
        congrArg some
          (finiteDiniModulus_mk_congr
            (finiteDiniModulusDecodeEncodeBHist compactNet)
            (finiteDiniModulusDecodeEncodeBHist graph)
            (finiteDiniModulusDecodeEncodeBHist realSeal)
            (finiteDiniModulusDecodeEncodeBHist monotoneDescent)
            (finiteDiniModulusDecodeEncodeBHist dyadicTolerance)
            (finiteDiniModulusDecodeEncodeBHist finiteBudget)
            (finiteDiniModulusDecodeEncodeBHist transport)
            (finiteDiniModulusDecodeEncodeBHist replay)
            (finiteDiniModulusDecodeEncodeBHist provenance)
            (finiteDiniModulusDecodeEncodeBHist localName))

private theorem finiteDiniModulusToEventFlow_injective
    {x y : FiniteDiniModulusUp} :
    finiteDiniModulusToEventFlow x = finiteDiniModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteDiniModulusFromEventFlow (finiteDiniModulusToEventFlow x) =
        finiteDiniModulusFromEventFlow (finiteDiniModulusToEventFlow y) :=
    congrArg finiteDiniModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteDiniModulus_round_trip x).symm
      (Eq.trans hread (finiteDiniModulus_round_trip y)))

private theorem finiteDiniModulus_field_faithful :
    ∀ x y : FiniteDiniModulusUp, finiteDiniModulusFields x = finiteDiniModulusFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk compactNet₁ graph₁ realSeal₁ monotoneDescent₁ dyadicTolerance₁ finiteBudget₁
      transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk compactNet₂ graph₂ realSeal₂ monotoneDescent₂ dyadicTolerance₂ finiteBudget₂
          transport₂ replay₂ provenance₂ localName₂ =>
          injection h with hCompactNet hRest₁
          injection hRest₁ with hGraph hRest₂
          injection hRest₂ with hRealSeal hRest₃
          injection hRest₃ with hMonotoneDescent hRest₄
          injection hRest₄ with hDyadicTolerance hRest₅
          injection hRest₅ with hFiniteBudget hRest₆
          injection hRest₆ with hTransport hRest₇
          injection hRest₇ with hReplay hRest₈
          injection hRest₈ with hProvenance hRest₉
          injection hRest₉ with hLocalName _
          cases hCompactNet
          cases hGraph
          cases hRealSeal
          cases hMonotoneDescent
          cases hDyadicTolerance
          cases hFiniteBudget
          cases hTransport
          cases hReplay
          cases hProvenance
          cases hLocalName
          rfl

instance finiteDiniModulusBHistCarrier : BHistCarrier FiniteDiniModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteDiniModulusToEventFlow
  fromEventFlow := finiteDiniModulusFromEventFlow

instance finiteDiniModulusChapterTasteGate : ChapterTasteGate FiniteDiniModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact finiteDiniModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteDiniModulusToEventFlow_injective heq)

instance finiteDiniModulusFieldFaithful : FieldFaithful FiniteDiniModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteDiniModulusFields
  field_faithful := finiteDiniModulus_field_faithful

instance finiteDiniModulusNontrivial : Nontrivial FiniteDiniModulusUp where
  witness_pair := by
    -- BEDC touchpoint anchor: BHist BMark
    refine
      ⟨FiniteDiniModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        FiniteDiniModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty, ?_⟩
    intro h
    cases h

theorem FiniteDiniModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteDiniModulusDecodeBHist (finiteDiniModulusEncodeBHist h) = h) ∧
      (∀ x : FiniteDiniModulusUp,
        finiteDiniModulusFromEventFlow (finiteDiniModulusToEventFlow x) = some x) ∧
        (∀ x y : FiniteDiniModulusUp,
          finiteDiniModulusToEventFlow x = finiteDiniModulusToEventFlow y -> x = y) ∧
          finiteDiniModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨finiteDiniModulusDecodeEncodeBHist, finiteDiniModulus_round_trip,
      (fun _x _y heq => finiteDiniModulusToEventFlow_injective heq), rfl⟩

end BEDC.Derived.FiniteDiniModulusUp
