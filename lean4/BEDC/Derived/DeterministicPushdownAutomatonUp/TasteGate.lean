import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DeterministicPushdownAutomatonUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DeterministicPushdownAutomatonUp : Type where
  | mk :
      (control inputAlphabet stackAlphabet transition start initialStack accepting inputWord run
        stackHistory endpoint acceptance transport replay provenance nameCert : BHist) →
        DeterministicPushdownAutomatonUp
  deriving DecidableEq

def deterministicPushdownAutomatonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: deterministicPushdownAutomatonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: deterministicPushdownAutomatonEncodeBHist h

def deterministicPushdownAutomatonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (deterministicPushdownAutomatonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (deterministicPushdownAutomatonDecodeBHist tail)

private theorem deterministicPushdownAutomatonDecode_encode_bhist :
    ∀ h : BHist,
      deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def deterministicPushdownAutomatonFields :
    DeterministicPushdownAutomatonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DeterministicPushdownAutomatonUp.mk control inputAlphabet stackAlphabet transition start
      initialStack accepting inputWord run stackHistory endpoint acceptance transport replay
      provenance nameCert =>
      [control, inputAlphabet, stackAlphabet, transition, start, initialStack, accepting,
        inputWord, run, stackHistory, endpoint, acceptance, transport, replay, provenance,
        nameCert]

def deterministicPushdownAutomatonToEventFlow :
    DeterministicPushdownAutomatonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (deterministicPushdownAutomatonFields x).map
      deterministicPushdownAutomatonEncodeBHist

def deterministicPushdownAutomatonFromEventFlow
    (ef : EventFlow) : Option DeterministicPushdownAutomatonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [control, inputAlphabet, stackAlphabet, transition, start, initialStack, accepting,
      inputWord, run, stackHistory, endpoint, acceptance, transport, replay, provenance,
      nameCert] =>
      some
        (DeterministicPushdownAutomatonUp.mk
          (deterministicPushdownAutomatonDecodeBHist control)
          (deterministicPushdownAutomatonDecodeBHist inputAlphabet)
          (deterministicPushdownAutomatonDecodeBHist stackAlphabet)
          (deterministicPushdownAutomatonDecodeBHist transition)
          (deterministicPushdownAutomatonDecodeBHist start)
          (deterministicPushdownAutomatonDecodeBHist initialStack)
          (deterministicPushdownAutomatonDecodeBHist accepting)
          (deterministicPushdownAutomatonDecodeBHist inputWord)
          (deterministicPushdownAutomatonDecodeBHist run)
          (deterministicPushdownAutomatonDecodeBHist stackHistory)
          (deterministicPushdownAutomatonDecodeBHist endpoint)
          (deterministicPushdownAutomatonDecodeBHist acceptance)
          (deterministicPushdownAutomatonDecodeBHist transport)
          (deterministicPushdownAutomatonDecodeBHist replay)
          (deterministicPushdownAutomatonDecodeBHist provenance)
          (deterministicPushdownAutomatonDecodeBHist nameCert))
  | _ => none

private theorem deterministicPushdownAutomaton_round_trip :
    ∀ x : DeterministicPushdownAutomatonUp,
      deterministicPushdownAutomatonFromEventFlow
        (deterministicPushdownAutomatonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk control inputAlphabet stackAlphabet transition start initialStack accepting inputWord
      run stackHistory endpoint acceptance transport replay provenance nameCert =>
      change
        some
          (DeterministicPushdownAutomatonUp.mk
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist control))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist inputAlphabet))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist stackAlphabet))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist transition))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist start))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist initialStack))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist accepting))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist inputWord))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist run))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist stackHistory))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist endpoint))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist acceptance))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist transport))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist replay))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist provenance))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist nameCert))) =
          some
            (DeterministicPushdownAutomatonUp.mk control inputAlphabet stackAlphabet transition
              start initialStack accepting inputWord run stackHistory endpoint acceptance
              transport replay provenance nameCert)
      rw [deterministicPushdownAutomatonDecode_encode_bhist control,
        deterministicPushdownAutomatonDecode_encode_bhist inputAlphabet,
        deterministicPushdownAutomatonDecode_encode_bhist stackAlphabet,
        deterministicPushdownAutomatonDecode_encode_bhist transition,
        deterministicPushdownAutomatonDecode_encode_bhist start,
        deterministicPushdownAutomatonDecode_encode_bhist initialStack,
        deterministicPushdownAutomatonDecode_encode_bhist accepting,
        deterministicPushdownAutomatonDecode_encode_bhist inputWord,
        deterministicPushdownAutomatonDecode_encode_bhist run,
        deterministicPushdownAutomatonDecode_encode_bhist stackHistory,
        deterministicPushdownAutomatonDecode_encode_bhist endpoint,
        deterministicPushdownAutomatonDecode_encode_bhist acceptance,
        deterministicPushdownAutomatonDecode_encode_bhist transport,
        deterministicPushdownAutomatonDecode_encode_bhist replay,
        deterministicPushdownAutomatonDecode_encode_bhist provenance,
        deterministicPushdownAutomatonDecode_encode_bhist nameCert]

private theorem deterministicPushdownAutomatonToEventFlow_injective
    {x y : DeterministicPushdownAutomatonUp} :
    deterministicPushdownAutomatonToEventFlow x =
      deterministicPushdownAutomatonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      deterministicPushdownAutomatonFromEventFlow
          (deterministicPushdownAutomatonToEventFlow x) =
        deterministicPushdownAutomatonFromEventFlow
          (deterministicPushdownAutomatonToEventFlow y) :=
    congrArg deterministicPushdownAutomatonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (deterministicPushdownAutomaton_round_trip x).symm
      (Eq.trans hread (deterministicPushdownAutomaton_round_trip y)))

private theorem deterministicPushdownAutomaton_field_faithful :
    ∀ x y : DeterministicPushdownAutomatonUp,
      deterministicPushdownAutomatonFields x =
        deterministicPushdownAutomatonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk control inputAlphabet stackAlphabet transition start initialStack accepting inputWord
      run stackHistory endpoint acceptance transport replay provenance nameCert =>
      cases y with
      | mk control' inputAlphabet' stackAlphabet' transition' start' initialStack' accepting'
          inputWord' run' stackHistory' endpoint' acceptance' transport' replay' provenance'
          nameCert' =>
          cases hfields
          rfl

instance deterministicPushdownAutomatonBHistCarrier :
    BHistCarrier DeterministicPushdownAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := deterministicPushdownAutomatonToEventFlow
  fromEventFlow := deterministicPushdownAutomatonFromEventFlow

instance deterministicPushdownAutomatonChapterTasteGate :
    ChapterTasteGate DeterministicPushdownAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := deterministicPushdownAutomaton_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (deterministicPushdownAutomatonToEventFlow_injective heq)

instance deterministicPushdownAutomatonFieldFaithful :
    FieldFaithful DeterministicPushdownAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := deterministicPushdownAutomatonFields
  field_faithful := deterministicPushdownAutomaton_field_faithful

instance deterministicPushdownAutomatonNontrivial :
    Nontrivial DeterministicPushdownAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DeterministicPushdownAutomatonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DeterministicPushdownAutomatonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DeterministicPushdownAutomatonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  deterministicPushdownAutomatonChapterTasteGate

end BEDC.Derived.DeterministicPushdownAutomatonUp.TasteGate
