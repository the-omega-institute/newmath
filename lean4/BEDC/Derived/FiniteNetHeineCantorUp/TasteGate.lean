import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteNetHeineCantorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteNetHeineCantorUp : Type where
  | mk
      (source target cover centers modulus triangle transport replay provenance name : BHist) :
      FiniteNetHeineCantorUp
  deriving DecidableEq

def finiteNetHeineCantorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteNetHeineCantorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteNetHeineCantorEncodeBHist h

def finiteNetHeineCantorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteNetHeineCantorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteNetHeineCantorDecodeBHist tail)

private theorem finiteNetHeineCantorDecode_encode_bhist :
    ∀ h : BHist,
      finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteNetHeineCantorToEventFlow : FiniteNetHeineCantorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteNetHeineCantorUp.mk source target cover centers modulus triangle transport replay
      provenance name =>
      [finiteNetHeineCantorEncodeBHist source,
        finiteNetHeineCantorEncodeBHist target,
        finiteNetHeineCantorEncodeBHist cover,
        finiteNetHeineCantorEncodeBHist centers,
        finiteNetHeineCantorEncodeBHist modulus,
        finiteNetHeineCantorEncodeBHist triangle,
        finiteNetHeineCantorEncodeBHist transport,
        finiteNetHeineCantorEncodeBHist replay,
        finiteNetHeineCantorEncodeBHist provenance,
        finiteNetHeineCantorEncodeBHist name]

private def finiteNetHeineCantorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteNetHeineCantorEventAtDefault index rest

def finiteNetHeineCantorFromEventFlow : EventFlow → Option FiniteNetHeineCantorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (FiniteNetHeineCantorUp.mk
        (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEventAtDefault 0 ef))
        (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEventAtDefault 1 ef))
        (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEventAtDefault 2 ef))
        (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEventAtDefault 3 ef))
        (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEventAtDefault 4 ef))
        (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEventAtDefault 5 ef))
        (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEventAtDefault 6 ef))
        (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEventAtDefault 7 ef))
        (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEventAtDefault 8 ef))
        (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEventAtDefault 9 ef)))

private theorem finiteNetHeineCantor_mk_congr
    {source source' target target' cover cover' centers centers' modulus modulus'
      triangle triangle' transport transport' replay replay' provenance provenance' name
      name' : BHist}
    (hSource : source' = source) (hTarget : target' = target) (hCover : cover' = cover)
    (hCenters : centers' = centers) (hModulus : modulus' = modulus)
    (hTriangle : triangle' = triangle) (hTransport : transport' = transport)
    (hReplay : replay' = replay) (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    FiniteNetHeineCantorUp.mk source' target' cover' centers' modulus' triangle'
        transport' replay' provenance' name' =
      FiniteNetHeineCantorUp.mk source target cover centers modulus triangle transport replay
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hTarget
  cases hCover
  cases hCenters
  cases hModulus
  cases hTriangle
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

private theorem finiteNetHeineCantor_round_trip :
    ∀ x : FiniteNetHeineCantorUp,
      finiteNetHeineCantorFromEventFlow (finiteNetHeineCantorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target cover centers modulus triangle transport replay provenance name =>
      change
        some
          (FiniteNetHeineCantorUp.mk
            (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEncodeBHist source))
            (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEncodeBHist target))
            (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEncodeBHist cover))
            (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEncodeBHist centers))
            (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEncodeBHist modulus))
            (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEncodeBHist triangle))
            (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEncodeBHist transport))
            (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEncodeBHist replay))
            (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEncodeBHist provenance))
            (finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEncodeBHist name))) =
          some
            (FiniteNetHeineCantorUp.mk source target cover centers modulus triangle transport
              replay provenance name)
      exact
        congrArg some
          (finiteNetHeineCantor_mk_congr
            (finiteNetHeineCantorDecode_encode_bhist source)
            (finiteNetHeineCantorDecode_encode_bhist target)
            (finiteNetHeineCantorDecode_encode_bhist cover)
            (finiteNetHeineCantorDecode_encode_bhist centers)
            (finiteNetHeineCantorDecode_encode_bhist modulus)
            (finiteNetHeineCantorDecode_encode_bhist triangle)
            (finiteNetHeineCantorDecode_encode_bhist transport)
            (finiteNetHeineCantorDecode_encode_bhist replay)
            (finiteNetHeineCantorDecode_encode_bhist provenance)
            (finiteNetHeineCantorDecode_encode_bhist name))

private theorem finiteNetHeineCantorToEventFlow_injective
    {x y : FiniteNetHeineCantorUp} :
    finiteNetHeineCantorToEventFlow x = finiteNetHeineCantorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteNetHeineCantorFromEventFlow (finiteNetHeineCantorToEventFlow x) =
        finiteNetHeineCantorFromEventFlow (finiteNetHeineCantorToEventFlow y) :=
    congrArg finiteNetHeineCantorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteNetHeineCantor_round_trip x).symm
      (Eq.trans hread (finiteNetHeineCantor_round_trip y)))

instance finiteNetHeineCantorBHistCarrier : BHistCarrier FiniteNetHeineCantorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteNetHeineCantorToEventFlow
  fromEventFlow := finiteNetHeineCantorFromEventFlow

instance finiteNetHeineCantorChapterTasteGate :
    ChapterTasteGate FiniteNetHeineCantorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteNetHeineCantorFromEventFlow (finiteNetHeineCantorToEventFlow x) = some x
    exact finiteNetHeineCantor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteNetHeineCantorToEventFlow_injective heq)

theorem FiniteNetHeineCantorTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteNetHeineCantorDecodeBHist (finiteNetHeineCantorEncodeBHist h) = h) ∧
      (∀ x : FiniteNetHeineCantorUp,
        finiteNetHeineCantorFromEventFlow (finiteNetHeineCantorToEventFlow x) = some x) ∧
      (∀ x y : FiniteNetHeineCantorUp,
        finiteNetHeineCantorToEventFlow x = finiteNetHeineCantorToEventFlow y → x = y) ∧
      finiteNetHeineCantorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨finiteNetHeineCantorDecode_encode_bhist,
      ⟨finiteNetHeineCantor_round_trip,
        ⟨fun _x _y heq => finiteNetHeineCantorToEventFlow_injective heq, rfl⟩⟩⟩

end BEDC.Derived.FiniteNetHeineCantorUp
