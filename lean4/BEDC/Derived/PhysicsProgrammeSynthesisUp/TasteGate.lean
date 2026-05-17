import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicsProgrammeSynthesisUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicsProgrammeSynthesisUp : Type where
  | mk (route falsification ledger verification failure transport continuation provenance name :
      BHist) : PhysicsProgrammeSynthesisUp
  deriving DecidableEq

def physicsProgrammeSynthesisFields (x : PhysicsProgrammeSynthesisUp) : List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  match x with
  | PhysicsProgrammeSynthesisUp.mk route falsification ledger verification failure transport
      continuation provenance name =>
      [route, falsification, ledger, verification, failure, transport, continuation, provenance,
        name]

def physicsProgrammeSynthesisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicsProgrammeSynthesisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicsProgrammeSynthesisEncodeBHist h

def physicsProgrammeSynthesisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicsProgrammeSynthesisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicsProgrammeSynthesisDecodeBHist tail)

private theorem physicsProgrammeSynthesis_decode_encode_bhist :
    ∀ h : BHist,
      physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def physicsProgrammeSynthesisToEventFlow :
    PhysicsProgrammeSynthesisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicsProgrammeSynthesisUp.mk route falsification ledger verification failure transport
      continuation provenance name =>
      [[BMark.b0],
        physicsProgrammeSynthesisEncodeBHist route,
        [BMark.b1, BMark.b0],
        physicsProgrammeSynthesisEncodeBHist falsification,
        [BMark.b1, BMark.b1, BMark.b0],
        physicsProgrammeSynthesisEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicsProgrammeSynthesisEncodeBHist verification,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicsProgrammeSynthesisEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicsProgrammeSynthesisEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicsProgrammeSynthesisEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        physicsProgrammeSynthesisEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        physicsProgrammeSynthesisEncodeBHist name]

def physicsProgrammeSynthesisFromEventFlow :
    EventFlow → Option PhysicsProgrammeSynthesisUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, route, _tag1, falsification, _tag2, ledger, _tag3, verification, _tag4,
      failure, _tag5, transport, _tag6, continuation, _tag7, provenance, _tag8, name] =>
      some
        (PhysicsProgrammeSynthesisUp.mk
          (physicsProgrammeSynthesisDecodeBHist route)
          (physicsProgrammeSynthesisDecodeBHist falsification)
          (physicsProgrammeSynthesisDecodeBHist ledger)
          (physicsProgrammeSynthesisDecodeBHist verification)
          (physicsProgrammeSynthesisDecodeBHist failure)
          (physicsProgrammeSynthesisDecodeBHist transport)
          (physicsProgrammeSynthesisDecodeBHist continuation)
          (physicsProgrammeSynthesisDecodeBHist provenance)
          (physicsProgrammeSynthesisDecodeBHist name))
  | _ => none

private theorem physicsProgrammeSynthesis_round_trip :
    ∀ x : PhysicsProgrammeSynthesisUp,
      physicsProgrammeSynthesisFromEventFlow
        (physicsProgrammeSynthesisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk route falsification ledger verification failure transport continuation provenance name =>
      change
        some
          (PhysicsProgrammeSynthesisUp.mk
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist route))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist falsification))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist ledger))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist verification))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist failure))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist transport))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist continuation))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist provenance))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist name))) =
          some
            (PhysicsProgrammeSynthesisUp.mk route falsification ledger verification failure
              transport continuation provenance name)
      rw [physicsProgrammeSynthesis_decode_encode_bhist route,
        physicsProgrammeSynthesis_decode_encode_bhist falsification,
        physicsProgrammeSynthesis_decode_encode_bhist ledger,
        physicsProgrammeSynthesis_decode_encode_bhist verification,
        physicsProgrammeSynthesis_decode_encode_bhist failure,
        physicsProgrammeSynthesis_decode_encode_bhist transport,
        physicsProgrammeSynthesis_decode_encode_bhist continuation,
        physicsProgrammeSynthesis_decode_encode_bhist provenance,
        physicsProgrammeSynthesis_decode_encode_bhist name]

private theorem physicsProgrammeSynthesisToEventFlow_injective
    {x y : PhysicsProgrammeSynthesisUp} :
    physicsProgrammeSynthesisToEventFlow x =
      physicsProgrammeSynthesisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicsProgrammeSynthesisFromEventFlow
          (physicsProgrammeSynthesisToEventFlow x) =
        physicsProgrammeSynthesisFromEventFlow
          (physicsProgrammeSynthesisToEventFlow y) :=
    congrArg physicsProgrammeSynthesisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicsProgrammeSynthesis_round_trip x).symm
      (Eq.trans hread (physicsProgrammeSynthesis_round_trip y)))

instance physicsProgrammeSynthesisBHistCarrier :
    BHistCarrier PhysicsProgrammeSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicsProgrammeSynthesisToEventFlow
  fromEventFlow := physicsProgrammeSynthesisFromEventFlow

instance physicsProgrammeSynthesisChapterTasteGate :
    ChapterTasteGate PhysicsProgrammeSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      physicsProgrammeSynthesisFromEventFlow
        (physicsProgrammeSynthesisToEventFlow x) = some x
    exact physicsProgrammeSynthesis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicsProgrammeSynthesisToEventFlow_injective heq)

instance physicsProgrammeSynthesisFieldFaithful :
    FieldFaithful PhysicsProgrammeSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicsProgrammeSynthesisFields
  field_faithful := by
    intro x y h
    cases x with
    | mk route₁ falsification₁ ledger₁ verification₁ failure₁ transport₁ continuation₁
        provenance₁ name₁ =>
        cases y with
        | mk route₂ falsification₂ ledger₂ verification₂ failure₂ transport₂ continuation₂
            provenance₂ name₂ =>
            injection h with hroute tail₁
            injection tail₁ with hfalsification tail₂
            injection tail₂ with hledger tail₃
            injection tail₃ with hverification tail₄
            injection tail₄ with hfailure tail₅
            injection tail₅ with htransport tail₆
            injection tail₆ with hcontinuation tail₇
            injection tail₇ with hprovenance tail₈
            injection tail₈ with hname _
            cases hroute
            cases hfalsification
            cases hledger
            cases hverification
            cases hfailure
            cases htransport
            cases hcontinuation
            cases hprovenance
            cases hname
            rfl

instance physicsProgrammeSynthesisNontrivial :
    Nontrivial PhysicsProgrammeSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicsProgrammeSynthesisUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhysicsProgrammeSynthesisUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicsProgrammeSynthesisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem PhysicsProgrammeSynthesisFalsificationNonescape
    (route falsification ledger verification failure transport continuation provenance name
      hostTail : BHist) :
    physicsProgrammeSynthesisFields
        (PhysicsProgrammeSynthesisUp.mk route falsification ledger verification failure
          transport continuation provenance name) =
        [route, falsification, ledger, verification, failure, transport, continuation,
          provenance, name] ∧
      Cont route falsification (append route falsification) ∧
        hsame (append route falsification) (append route falsification) ∧
          (Cont (append route falsification) (BHist.e0 hostTail) route -> False) ∧
            (Cont (append route falsification) (BHist.e1 hostTail) route -> False) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · intro hostReturn
          have noReturn :=
            cont_mutual_extension_right_tail_absurd
              (h := route) (k := append route falsification) (leftTail := falsification)
              (rightTail := hostTail)
          exact noReturn.left rfl hostReturn
        · intro hostReturn
          have noReturn :=
            cont_mutual_extension_right_tail_absurd
              (h := route) (k := append route falsification) (leftTail := falsification)
              (rightTail := hostTail)
          exact noReturn.right rfl hostReturn

end BEDC.Derived.PhysicsProgrammeSynthesisUp.TasteGate
