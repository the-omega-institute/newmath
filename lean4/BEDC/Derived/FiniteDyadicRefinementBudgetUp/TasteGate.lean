import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteDyadicRefinementBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteDyadicRefinementBudgetUp : Type where
  | mk
      (refinement formalBall dyadicLedger streamAddress regularReadback realSeal transport
        replay provenance localNameCert : BHist) :
      FiniteDyadicRefinementBudgetUp
  deriving DecidableEq

def finiteDyadicRefinementBudgetTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1, BMark.b1]

def finiteDyadicRefinementBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteDyadicRefinementBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteDyadicRefinementBudgetEncodeBHist h

def finiteDyadicRefinementBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteDyadicRefinementBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteDyadicRefinementBudgetDecodeBHist tail)

private theorem finiteDyadicRefinementBudgetDecodeEncode :
    ∀ h : BHist,
      finiteDyadicRefinementBudgetDecodeBHist
          (finiteDyadicRefinementBudgetEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteDyadicRefinementBudgetFields :
    FiniteDyadicRefinementBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDyadicRefinementBudgetUp.mk refinement formalBall dyadicLedger streamAddress
      regularReadback realSeal transport replay provenance localNameCert =>
      [refinement, formalBall, dyadicLedger, streamAddress, regularReadback, realSeal,
        transport, replay, provenance, localNameCert]

def finiteDyadicRefinementBudgetToEventFlow :
    FiniteDyadicRefinementBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDyadicRefinementBudgetUp.mk refinement formalBall dyadicLedger streamAddress
      regularReadback realSeal transport replay provenance localNameCert =>
      [finiteDyadicRefinementBudgetTag,
        finiteDyadicRefinementBudgetEncodeBHist refinement,
        finiteDyadicRefinementBudgetEncodeBHist formalBall,
        finiteDyadicRefinementBudgetEncodeBHist dyadicLedger,
        finiteDyadicRefinementBudgetEncodeBHist streamAddress,
        finiteDyadicRefinementBudgetEncodeBHist regularReadback,
        finiteDyadicRefinementBudgetEncodeBHist realSeal,
        finiteDyadicRefinementBudgetEncodeBHist transport,
        finiteDyadicRefinementBudgetEncodeBHist replay,
        finiteDyadicRefinementBudgetEncodeBHist provenance,
        finiteDyadicRefinementBudgetEncodeBHist localNameCert]

private def finiteDyadicRefinementBudgetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteDyadicRefinementBudgetEventAtDefault index rest

def finiteDyadicRefinementBudgetFromEventFlow :
    EventFlow → Option FiniteDyadicRefinementBudgetUp := fun ef =>
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteDyadicRefinementBudgetUp.mk
      (finiteDyadicRefinementBudgetDecodeBHist
        (finiteDyadicRefinementBudgetEventAtDefault 1 ef))
      (finiteDyadicRefinementBudgetDecodeBHist
        (finiteDyadicRefinementBudgetEventAtDefault 2 ef))
      (finiteDyadicRefinementBudgetDecodeBHist
        (finiteDyadicRefinementBudgetEventAtDefault 3 ef))
      (finiteDyadicRefinementBudgetDecodeBHist
        (finiteDyadicRefinementBudgetEventAtDefault 4 ef))
      (finiteDyadicRefinementBudgetDecodeBHist
        (finiteDyadicRefinementBudgetEventAtDefault 5 ef))
      (finiteDyadicRefinementBudgetDecodeBHist
        (finiteDyadicRefinementBudgetEventAtDefault 6 ef))
      (finiteDyadicRefinementBudgetDecodeBHist
        (finiteDyadicRefinementBudgetEventAtDefault 7 ef))
      (finiteDyadicRefinementBudgetDecodeBHist
        (finiteDyadicRefinementBudgetEventAtDefault 8 ef))
      (finiteDyadicRefinementBudgetDecodeBHist
        (finiteDyadicRefinementBudgetEventAtDefault 9 ef))
      (finiteDyadicRefinementBudgetDecodeBHist
        (finiteDyadicRefinementBudgetEventAtDefault 10 ef)))

private theorem finiteDyadicRefinementBudgetRoundTrip :
    ∀ x : FiniteDyadicRefinementBudgetUp,
      finiteDyadicRefinementBudgetFromEventFlow
          (finiteDyadicRefinementBudgetToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk refinement formalBall dyadicLedger streamAddress regularReadback realSeal transport
      replay provenance localNameCert =>
      change
        some
          (FiniteDyadicRefinementBudgetUp.mk
            (finiteDyadicRefinementBudgetDecodeBHist
              (finiteDyadicRefinementBudgetEncodeBHist refinement))
            (finiteDyadicRefinementBudgetDecodeBHist
              (finiteDyadicRefinementBudgetEncodeBHist formalBall))
            (finiteDyadicRefinementBudgetDecodeBHist
              (finiteDyadicRefinementBudgetEncodeBHist dyadicLedger))
            (finiteDyadicRefinementBudgetDecodeBHist
              (finiteDyadicRefinementBudgetEncodeBHist streamAddress))
            (finiteDyadicRefinementBudgetDecodeBHist
              (finiteDyadicRefinementBudgetEncodeBHist regularReadback))
            (finiteDyadicRefinementBudgetDecodeBHist
              (finiteDyadicRefinementBudgetEncodeBHist realSeal))
            (finiteDyadicRefinementBudgetDecodeBHist
              (finiteDyadicRefinementBudgetEncodeBHist transport))
            (finiteDyadicRefinementBudgetDecodeBHist
              (finiteDyadicRefinementBudgetEncodeBHist replay))
            (finiteDyadicRefinementBudgetDecodeBHist
              (finiteDyadicRefinementBudgetEncodeBHist provenance))
            (finiteDyadicRefinementBudgetDecodeBHist
              (finiteDyadicRefinementBudgetEncodeBHist localNameCert))) =
          some
            (FiniteDyadicRefinementBudgetUp.mk refinement formalBall dyadicLedger
              streamAddress regularReadback realSeal transport replay provenance localNameCert)
      rw [finiteDyadicRefinementBudgetDecodeEncode refinement,
        finiteDyadicRefinementBudgetDecodeEncode formalBall,
        finiteDyadicRefinementBudgetDecodeEncode dyadicLedger,
        finiteDyadicRefinementBudgetDecodeEncode streamAddress,
        finiteDyadicRefinementBudgetDecodeEncode regularReadback,
        finiteDyadicRefinementBudgetDecodeEncode realSeal,
        finiteDyadicRefinementBudgetDecodeEncode transport,
        finiteDyadicRefinementBudgetDecodeEncode replay,
        finiteDyadicRefinementBudgetDecodeEncode provenance,
        finiteDyadicRefinementBudgetDecodeEncode localNameCert]

private theorem finiteDyadicRefinementBudgetToEventFlow_injective
    {x y : FiniteDyadicRefinementBudgetUp} :
    finiteDyadicRefinementBudgetToEventFlow x =
        finiteDyadicRefinementBudgetToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteDyadicRefinementBudgetFromEventFlow
          (finiteDyadicRefinementBudgetToEventFlow x) =
        finiteDyadicRefinementBudgetFromEventFlow
          (finiteDyadicRefinementBudgetToEventFlow y) :=
    congrArg finiteDyadicRefinementBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (finiteDyadicRefinementBudgetRoundTrip x).symm
      (Eq.trans hread (finiteDyadicRefinementBudgetRoundTrip y)))

private theorem finiteDyadicRefinementBudgetFieldFaithfulProof :
    ∀ x y : FiniteDyadicRefinementBudgetUp,
      finiteDyadicRefinementBudgetFields x = finiteDyadicRefinementBudgetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk refinement1 formalBall1 dyadicLedger1 streamAddress1 regularReadback1 realSeal1
      transport1 replay1 provenance1 localNameCert1 =>
      cases y with
      | mk refinement2 formalBall2 dyadicLedger2 streamAddress2 regularReadback2 realSeal2
          transport2 replay2 provenance2 localNameCert2 =>
          cases hfields
          rfl

instance finiteDyadicRefinementBudgetBHistCarrier :
    BHistCarrier FiniteDyadicRefinementBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteDyadicRefinementBudgetToEventFlow
  fromEventFlow := finiteDyadicRefinementBudgetFromEventFlow

instance finiteDyadicRefinementBudgetChapterTasteGate :
    ChapterTasteGate FiniteDyadicRefinementBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteDyadicRefinementBudgetFromEventFlow
          (finiteDyadicRefinementBudgetToEventFlow x) =
        some x
    exact finiteDyadicRefinementBudgetRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteDyadicRefinementBudgetToEventFlow_injective heq)

instance finiteDyadicRefinementBudgetFieldFaithful :
    FieldFaithful FiniteDyadicRefinementBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteDyadicRefinementBudgetFields
  field_faithful := finiteDyadicRefinementBudgetFieldFaithfulProof

instance finiteDyadicRefinementBudgetNontrivial :
    Nontrivial FiniteDyadicRefinementBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteDyadicRefinementBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteDyadicRefinementBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteDyadicRefinementBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteDyadicRefinementBudgetChapterTasteGate

theorem FiniteDyadicRefinementBudgetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteDyadicRefinementBudgetUp) ∧
      Nonempty (FieldFaithful FiniteDyadicRefinementBudgetUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial FiniteDyadicRefinementBudgetUp) ∧
          (∀ h : BHist,
            finiteDyadicRefinementBudgetDecodeBHist
                (finiteDyadicRefinementBudgetEncodeBHist h) =
              h) ∧
            (∀ x : FiniteDyadicRefinementBudgetUp,
              finiteDyadicRefinementBudgetFromEventFlow
                  (finiteDyadicRefinementBudgetToEventFlow x) =
                some x) ∧
              (∀ x y : FiniteDyadicRefinementBudgetUp,
                finiteDyadicRefinementBudgetToEventFlow x =
                    finiteDyadicRefinementBudgetToEventFlow y →
                  x = y) ∧
                finiteDyadicRefinementBudgetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro finiteDyadicRefinementBudgetChapterTasteGate,
      Nonempty.intro finiteDyadicRefinementBudgetFieldFaithful,
      Nonempty.intro finiteDyadicRefinementBudgetNontrivial,
      finiteDyadicRefinementBudgetDecodeEncode,
      finiteDyadicRefinementBudgetRoundTrip,
      (fun _ _ heq => finiteDyadicRefinementBudgetToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteDyadicRefinementBudgetUp
