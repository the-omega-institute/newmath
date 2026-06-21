import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveHeineBorelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveHeineBorelUp : Type where
  | mk
      (endpoint mesh cover finiteSubcover readback realSeal refusal replay provenance name : BHist) :
      ConstructiveHeineBorelUp
  deriving DecidableEq

def constructiveHeineBorelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveHeineBorelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveHeineBorelEncodeBHist h

def constructiveHeineBorelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveHeineBorelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveHeineBorelDecodeBHist tail)

private theorem constructiveHeineBorelDecode_encode_bhist :
    ∀ h : BHist,
      constructiveHeineBorelDecodeBHist (constructiveHeineBorelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem constructiveHeineBorel_mk_congr
    {endpoint endpoint' mesh mesh' cover cover' finiteSubcover finiteSubcover' readback
      readback' realSeal realSeal' refusal refusal' replay replay' provenance provenance'
      name name' : BHist}
    (hEndpoint : endpoint' = endpoint)
    (hMesh : mesh' = mesh)
    (hCover : cover' = cover)
    (hFiniteSubcover : finiteSubcover' = finiteSubcover)
    (hReadback : readback' = readback)
    (hRealSeal : realSeal' = realSeal)
    (hRefusal : refusal' = refusal)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ConstructiveHeineBorelUp.mk endpoint' mesh' cover' finiteSubcover' readback' realSeal'
        refusal' replay' provenance' name' =
      ConstructiveHeineBorelUp.mk endpoint mesh cover finiteSubcover readback realSeal refusal
        replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hEndpoint
  cases hMesh
  cases hCover
  cases hFiniteSubcover
  cases hReadback
  cases hRealSeal
  cases hRefusal
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def constructiveHeineBorelFields : ConstructiveHeineBorelUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveHeineBorelUp.mk endpoint mesh cover finiteSubcover readback realSeal refusal
      replay provenance name =>
      [endpoint, mesh, cover, finiteSubcover, readback, realSeal, refusal, replay, provenance,
        name]

def constructiveHeineBorelToEventFlow : ConstructiveHeineBorelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (constructiveHeineBorelFields x).map constructiveHeineBorelEncodeBHist

private def constructiveHeineBorelEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveHeineBorelEventAt index rest

def constructiveHeineBorelFromEventFlow (ef : EventFlow) : Option ConstructiveHeineBorelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveHeineBorelUp.mk
      (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEventAt 0 ef))
      (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEventAt 1 ef))
      (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEventAt 2 ef))
      (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEventAt 3 ef))
      (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEventAt 4 ef))
      (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEventAt 5 ef))
      (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEventAt 6 ef))
      (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEventAt 7 ef))
      (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEventAt 8 ef))
      (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEventAt 9 ef)))

private theorem constructiveHeineBorel_round_trip :
    ∀ x : ConstructiveHeineBorelUp,
      constructiveHeineBorelFromEventFlow (constructiveHeineBorelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk endpoint mesh cover finiteSubcover readback realSeal refusal replay provenance name =>
      change
        some
          (ConstructiveHeineBorelUp.mk
            (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEncodeBHist endpoint))
            (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEncodeBHist mesh))
            (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEncodeBHist cover))
            (constructiveHeineBorelDecodeBHist
              (constructiveHeineBorelEncodeBHist finiteSubcover))
            (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEncodeBHist readback))
            (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEncodeBHist realSeal))
            (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEncodeBHist refusal))
            (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEncodeBHist replay))
            (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEncodeBHist provenance))
            (constructiveHeineBorelDecodeBHist (constructiveHeineBorelEncodeBHist name))) =
          some
            (ConstructiveHeineBorelUp.mk endpoint mesh cover finiteSubcover readback realSeal
              refusal replay provenance name)
      exact
        congrArg some
          (constructiveHeineBorel_mk_congr
            (constructiveHeineBorelDecode_encode_bhist endpoint)
            (constructiveHeineBorelDecode_encode_bhist mesh)
            (constructiveHeineBorelDecode_encode_bhist cover)
            (constructiveHeineBorelDecode_encode_bhist finiteSubcover)
            (constructiveHeineBorelDecode_encode_bhist readback)
            (constructiveHeineBorelDecode_encode_bhist realSeal)
            (constructiveHeineBorelDecode_encode_bhist refusal)
            (constructiveHeineBorelDecode_encode_bhist replay)
            (constructiveHeineBorelDecode_encode_bhist provenance)
            (constructiveHeineBorelDecode_encode_bhist name))

private theorem constructiveHeineBorelToEventFlow_injective
    {x y : ConstructiveHeineBorelUp} :
    constructiveHeineBorelToEventFlow x = constructiveHeineBorelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveHeineBorelFromEventFlow (constructiveHeineBorelToEventFlow x) =
        constructiveHeineBorelFromEventFlow (constructiveHeineBorelToEventFlow y) :=
    congrArg constructiveHeineBorelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (constructiveHeineBorel_round_trip x).symm
      (Eq.trans hread (constructiveHeineBorel_round_trip y)))

instance constructiveHeineBorelBHistCarrier : BHistCarrier ConstructiveHeineBorelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveHeineBorelToEventFlow
  fromEventFlow := constructiveHeineBorelFromEventFlow

instance constructiveHeineBorelChapterTasteGate :
    ChapterTasteGate ConstructiveHeineBorelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveHeineBorelFromEventFlow (constructiveHeineBorelToEventFlow x) = some x
    exact constructiveHeineBorel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (constructiveHeineBorelToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ConstructiveHeineBorelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveHeineBorelChapterTasteGate

theorem ConstructiveHeineBorelTasteGate_single_carrier_alignment :
    (∀ h : BHist, constructiveHeineBorelDecodeBHist
      (constructiveHeineBorelEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ConstructiveHeineBorelUp) ∧
        Nonempty (ChapterTasteGate ConstructiveHeineBorelUp) ∧
          constructiveHeineBorelEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨constructiveHeineBorelDecode_encode_bhist,
      ⟨{ toEventFlow := constructiveHeineBorelToEventFlow
         fromEventFlow := constructiveHeineBorelFromEventFlow }⟩,
      ⟨{ round_trip := by
            intro x
            change
              constructiveHeineBorelFromEventFlow
                  (constructiveHeineBorelToEventFlow x) =
                some x
            exact constructiveHeineBorel_round_trip x
         layer_separation := by
            intro x y hxy heq
            exact hxy (constructiveHeineBorelToEventFlow_injective heq) }⟩,
      rfl⟩

end BEDC.Derived.ConstructiveHeineBorelUp
