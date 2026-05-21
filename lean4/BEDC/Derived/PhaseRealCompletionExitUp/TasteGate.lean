import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhaseRealCompletionExitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhaseRealCompletionExitUp : Type where
  | mk (D S Q R B H C P N : BHist) : PhaseRealCompletionExitUp
  deriving DecidableEq

def phaseRealCompletionExitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: phaseRealCompletionExitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: phaseRealCompletionExitEncodeBHist h

def phaseRealCompletionExitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (phaseRealCompletionExitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (phaseRealCompletionExitDecodeBHist tail)

private theorem phaseRealCompletionExit_decode_encode_bhist :
    ∀ h : BHist, phaseRealCompletionExitDecodeBHist
      (phaseRealCompletionExitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem phaseRealCompletionExit_mk_congr
    {D D' S S' Q Q' R R' B B' H H' C C' P P' N N' : BHist}
    (hD : D' = D) (hS : S' = S) (hQ : Q' = Q) (hR : R' = R) (hB : B' = B)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    PhaseRealCompletionExitUp.mk D' S' Q' R' B' H' C' P' N' =
      PhaseRealCompletionExitUp.mk D S Q R B H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hS
  cases hQ
  cases hR
  cases hB
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private def phaseRealCompletionExitFields :
    PhaseRealCompletionExitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhaseRealCompletionExitUp.mk D S Q R B H C P N => [D, S, Q, R, B, H, C, P, N]

def phaseRealCompletionExitToEventFlow :
    PhaseRealCompletionExitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (phaseRealCompletionExitFields x).map phaseRealCompletionExitEncodeBHist

private def phaseRealCompletionExitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => phaseRealCompletionExitEventAtDefault index rest

def phaseRealCompletionExitFromEventFlow :
    EventFlow → Option PhaseRealCompletionExitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (PhaseRealCompletionExitUp.mk
        (phaseRealCompletionExitDecodeBHist (phaseRealCompletionExitEventAtDefault 0 ef))
        (phaseRealCompletionExitDecodeBHist (phaseRealCompletionExitEventAtDefault 1 ef))
        (phaseRealCompletionExitDecodeBHist (phaseRealCompletionExitEventAtDefault 2 ef))
        (phaseRealCompletionExitDecodeBHist (phaseRealCompletionExitEventAtDefault 3 ef))
        (phaseRealCompletionExitDecodeBHist (phaseRealCompletionExitEventAtDefault 4 ef))
        (phaseRealCompletionExitDecodeBHist (phaseRealCompletionExitEventAtDefault 5 ef))
        (phaseRealCompletionExitDecodeBHist (phaseRealCompletionExitEventAtDefault 6 ef))
        (phaseRealCompletionExitDecodeBHist (phaseRealCompletionExitEventAtDefault 7 ef))
        (phaseRealCompletionExitDecodeBHist (phaseRealCompletionExitEventAtDefault 8 ef)))

private theorem phaseRealCompletionExit_round_trip :
    ∀ x : PhaseRealCompletionExitUp,
      phaseRealCompletionExitFromEventFlow
        (phaseRealCompletionExitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S Q R B H C P N =>
      exact
        congrArg some
          (phaseRealCompletionExit_mk_congr
            (phaseRealCompletionExit_decode_encode_bhist D)
            (phaseRealCompletionExit_decode_encode_bhist S)
            (phaseRealCompletionExit_decode_encode_bhist Q)
            (phaseRealCompletionExit_decode_encode_bhist R)
            (phaseRealCompletionExit_decode_encode_bhist B)
            (phaseRealCompletionExit_decode_encode_bhist H)
            (phaseRealCompletionExit_decode_encode_bhist C)
            (phaseRealCompletionExit_decode_encode_bhist P)
            (phaseRealCompletionExit_decode_encode_bhist N))

private theorem phaseRealCompletionExitToEventFlow_injective
    {x y : PhaseRealCompletionExitUp} :
    phaseRealCompletionExitToEventFlow x = phaseRealCompletionExitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      phaseRealCompletionExitFromEventFlow (phaseRealCompletionExitToEventFlow x) =
        phaseRealCompletionExitFromEventFlow (phaseRealCompletionExitToEventFlow y) :=
    congrArg phaseRealCompletionExitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (phaseRealCompletionExit_round_trip x).symm
      (Eq.trans hread (phaseRealCompletionExit_round_trip y)))

private theorem phaseRealCompletionExit_field_faithful :
    ∀ x y : PhaseRealCompletionExitUp,
      phaseRealCompletionExitFields x = phaseRealCompletionExitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D S Q R B H C P N =>
      cases y with
      | mk D' S' Q' R' B' H' C' P' N' =>
          cases hfields
          rfl

instance phaseRealCompletionExitBHistCarrier :
    BHistCarrier PhaseRealCompletionExitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := phaseRealCompletionExitToEventFlow
  fromEventFlow := phaseRealCompletionExitFromEventFlow

instance phaseRealCompletionExitChapterTasteGate :
    ChapterTasteGate PhaseRealCompletionExitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change phaseRealCompletionExitFromEventFlow
      (phaseRealCompletionExitToEventFlow x) = some x
    exact phaseRealCompletionExit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (phaseRealCompletionExitToEventFlow_injective heq)

instance phaseRealCompletionExitFieldFaithful :
    FieldFaithful PhaseRealCompletionExitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := phaseRealCompletionExitFields
  field_faithful := phaseRealCompletionExit_field_faithful

instance phaseRealCompletionExitNontrivial :
    Nontrivial PhaseRealCompletionExitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhaseRealCompletionExitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhaseRealCompletionExitUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhaseRealCompletionExitUp :=
  phaseRealCompletionExitChapterTasteGate

theorem PhaseRealCompletionExitTasteGate_single_carrier_alignment :
    (∀ h : BHist, phaseRealCompletionExitDecodeBHist
      (phaseRealCompletionExitEncodeBHist h) = h) ∧
      (∀ x : PhaseRealCompletionExitUp,
        phaseRealCompletionExitFromEventFlow
          (phaseRealCompletionExitToEventFlow x) = some x) ∧
        (∀ x y : PhaseRealCompletionExitUp,
          phaseRealCompletionExitToEventFlow x =
              phaseRealCompletionExitToEventFlow y →
            x = y) ∧
          Nonempty (ChapterTasteGate PhaseRealCompletionExitUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨phaseRealCompletionExit_decode_encode_bhist,
      phaseRealCompletionExit_round_trip,
      (fun _ _ heq => phaseRealCompletionExitToEventFlow_injective heq),
      ⟨phaseRealCompletionExitChapterTasteGate⟩⟩

theorem PhaseRealCompletionExitUp_boundary_witness_balance
    {dyadic stream regular real boundary transport route provenance name dyadic' stream'
      regular' real' boundary' transport' route' provenance' name' boundaryRead
      boundaryRead' : BHist} :
    FieldFaithful.fields
        (PhaseRealCompletionExitUp.mk dyadic stream regular real boundary transport route
          provenance name) =
      FieldFaithful.fields
        (PhaseRealCompletionExitUp.mk dyadic' stream' regular' real' boundary' transport'
          route' provenance' name') →
      Cont real boundary boundaryRead →
        Cont real' boundary' boundaryRead' →
          real = real' ∧ boundary = boundary' ∧ route = route' ∧
            Cont real boundary boundaryRead ∧ Cont real' boundary' boundaryRead' := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful
  intro hfields boundaryRoute boundaryRoute'
  change
      phaseRealCompletionExitFields
          (PhaseRealCompletionExitUp.mk dyadic stream regular real boundary transport route
            provenance name) =
        phaseRealCompletionExitFields
          (PhaseRealCompletionExitUp.mk dyadic' stream' regular' real' boundary' transport'
            route' provenance' name') at hfields
  injection hfields with _hDyadic tail0
  injection tail0 with _hStream tail1
  injection tail1 with _hRegular tail2
  injection tail2 with hReal tail3
  injection tail3 with hBoundary tail4
  injection tail4 with _hTransport tail5
  injection tail5 with hRoute _tail6
  exact ⟨hReal, hBoundary, hRoute, boundaryRoute, boundaryRoute'⟩

end BEDC.Derived.PhaseRealCompletionExitUp
