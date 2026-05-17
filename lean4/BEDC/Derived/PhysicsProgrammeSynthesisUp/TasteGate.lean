import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicsProgrammeSynthesisUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicsProgrammeSynthesisUp : Type where
  | mk (route falsification ledger verification failure transport continuation provenance name :
      BHist) : PhysicsProgrammeSynthesisUp
  deriving DecidableEq

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

private def physicsProgrammeSynthesisRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => physicsProgrammeSynthesisRawAt n rest

def physicsProgrammeSynthesisFields : PhysicsProgrammeSynthesisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicsProgrammeSynthesisUp.mk route falsification ledger verification failure transport
      continuation provenance name =>
      [route, falsification, ledger, verification, failure, transport, continuation, provenance,
        name]

def physicsProgrammeSynthesisToEventFlow : PhysicsProgrammeSynthesisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicsProgrammeSynthesisUp.mk route falsification ledger verification failure transport
      continuation provenance name =>
      [physicsProgrammeSynthesisEncodeBHist route,
        physicsProgrammeSynthesisEncodeBHist falsification,
        physicsProgrammeSynthesisEncodeBHist ledger,
        physicsProgrammeSynthesisEncodeBHist verification,
        physicsProgrammeSynthesisEncodeBHist failure,
        physicsProgrammeSynthesisEncodeBHist transport,
        physicsProgrammeSynthesisEncodeBHist continuation,
        physicsProgrammeSynthesisEncodeBHist provenance,
        physicsProgrammeSynthesisEncodeBHist name]

def physicsProgrammeSynthesisFromEventFlow
    (flow : EventFlow) : Option PhysicsProgrammeSynthesisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PhysicsProgrammeSynthesisUp.mk
      (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisRawAt 0 flow))
      (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisRawAt 1 flow))
      (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisRawAt 2 flow))
      (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisRawAt 3 flow))
      (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisRawAt 4 flow))
      (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisRawAt 5 flow))
      (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisRawAt 6 flow))
      (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisRawAt 7 flow))
      (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisRawAt 8 flow)))

private theorem physicsProgrammeSynthesis_mk_congr
    {R R' F F' L L' V V' E E' H H' C C' P P' N N' : BHist}
    (hR : R' = R)
    (hF : F' = F)
    (hL : L' = L)
    (hV : V' = V)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    PhysicsProgrammeSynthesisUp.mk R' F' L' V' E' H' C' P' N' =
      PhysicsProgrammeSynthesisUp.mk R F L V E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hF
  cases hL
  cases hV
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem physicsProgrammeSynthesis_round_trip :
    ∀ x : PhysicsProgrammeSynthesisUp,
      physicsProgrammeSynthesisFromEventFlow
        (physicsProgrammeSynthesisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk route falsification ledger verification failure transport continuation provenance name =>
      exact
        congrArg some
          (physicsProgrammeSynthesis_mk_congr
            (physicsProgrammeSynthesis_decode_encode_bhist route)
            (physicsProgrammeSynthesis_decode_encode_bhist falsification)
            (physicsProgrammeSynthesis_decode_encode_bhist ledger)
            (physicsProgrammeSynthesis_decode_encode_bhist verification)
            (physicsProgrammeSynthesis_decode_encode_bhist failure)
            (physicsProgrammeSynthesis_decode_encode_bhist transport)
            (physicsProgrammeSynthesis_decode_encode_bhist continuation)
            (physicsProgrammeSynthesis_decode_encode_bhist provenance)
            (physicsProgrammeSynthesis_decode_encode_bhist name))

private theorem physicsProgrammeSynthesisToEventFlow_injective
    {x y : PhysicsProgrammeSynthesisUp} :
    physicsProgrammeSynthesisToEventFlow x = physicsProgrammeSynthesisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicsProgrammeSynthesisFromEventFlow (physicsProgrammeSynthesisToEventFlow x) =
        physicsProgrammeSynthesisFromEventFlow (physicsProgrammeSynthesisToEventFlow y) :=
    congrArg physicsProgrammeSynthesisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicsProgrammeSynthesis_round_trip x).symm
      (Eq.trans hread (physicsProgrammeSynthesis_round_trip y)))

private theorem physicsProgrammeSynthesis_field_faithful :
    ∀ x y : PhysicsProgrammeSynthesisUp,
      physicsProgrammeSynthesisFields x = physicsProgrammeSynthesisFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk route₁ falsification₁ ledger₁ verification₁ failure₁ transport₁ continuation₁
      provenance₁ name₁ =>
      cases y with
      | mk route₂ falsification₂ ledger₂ verification₂ failure₂ transport₂ continuation₂
          provenance₂ name₂ =>
          injection hfields with hroute tail₁
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

instance physicsProgrammeSynthesisBHistCarrier : BHistCarrier PhysicsProgrammeSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicsProgrammeSynthesisToEventFlow
  fromEventFlow := physicsProgrammeSynthesisFromEventFlow

instance physicsProgrammeSynthesisChapterTasteGate :
    ChapterTasteGate PhysicsProgrammeSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change physicsProgrammeSynthesisFromEventFlow
      (physicsProgrammeSynthesisToEventFlow x) = some x
    exact physicsProgrammeSynthesis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicsProgrammeSynthesisToEventFlow_injective heq)

instance physicsProgrammeSynthesisFieldFaithful :
    FieldFaithful PhysicsProgrammeSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicsProgrammeSynthesisFields
  field_faithful := physicsProgrammeSynthesis_field_faithful

instance physicsProgrammeSynthesisNontrivial : Nontrivial PhysicsProgrammeSynthesisUp where
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
  physicsProgrammeSynthesisChapterTasteGate

def taste_gate_witness : FieldFaithful PhysicsProgrammeSynthesisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicsProgrammeSynthesisFieldFaithful

theorem PhysicsProgrammeSynthesisTasteGate_single_carrier_alignment :
    (∀ h : BHist, physicsProgrammeSynthesisDecodeBHist
      (physicsProgrammeSynthesisEncodeBHist h) = h) ∧
      (∀ x : PhysicsProgrammeSynthesisUp,
        physicsProgrammeSynthesisFromEventFlow (physicsProgrammeSynthesisToEventFlow x) =
          some x) ∧
        (∀ x y : PhysicsProgrammeSynthesisUp,
          physicsProgrammeSynthesisToEventFlow x = physicsProgrammeSynthesisToEventFlow y →
            x = y) ∧
          physicsProgrammeSynthesisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨physicsProgrammeSynthesis_decode_encode_bhist,
      physicsProgrammeSynthesis_round_trip,
      (fun _x _y heq => physicsProgrammeSynthesisToEventFlow_injective heq),
      rfl⟩

namespace TasteGate

abbrev PhysicsProgrammeSynthesisUp :=
  BEDC.Derived.PhysicsProgrammeSynthesisUp.PhysicsProgrammeSynthesisUp

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

end TasteGate

end BEDC.Derived.PhysicsProgrammeSynthesisUp
