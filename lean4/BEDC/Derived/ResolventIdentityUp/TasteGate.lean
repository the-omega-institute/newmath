import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ResolventIdentityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ResolventIdentityUp : Type where
  | mk (X T lambda mu A_lambda A_mu U_lambda U_mu I D H C P N : BHist) :
      ResolventIdentityUp
  deriving DecidableEq

def resolventIdentityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: resolventIdentityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: resolventIdentityEncodeBHist h

def resolventIdentityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (resolventIdentityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (resolventIdentityDecodeBHist tail)

private theorem ResolventIdentityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, resolventIdentityDecodeBHist (resolventIdentityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def resolventIdentityFields : ResolventIdentityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ResolventIdentityUp.mk X T lambda mu A_lambda A_mu U_lambda U_mu I D H C P N =>
      [X, T, lambda, mu, A_lambda, A_mu, U_lambda, U_mu, I, D, H, C, P, N]

def resolventIdentityToEventFlow : ResolventIdentityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (resolventIdentityFields x).map resolventIdentityEncodeBHist

private def resolventIdentityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => resolventIdentityEventAtDefault index rest

def resolventIdentityFromEventFlow (ef : EventFlow) : Option ResolventIdentityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ResolventIdentityUp.mk
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 0 ef))
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 1 ef))
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 2 ef))
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 3 ef))
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 4 ef))
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 5 ef))
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 6 ef))
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 7 ef))
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 8 ef))
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 9 ef))
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 10 ef))
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 11 ef))
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 12 ef))
      (resolventIdentityDecodeBHist (resolventIdentityEventAtDefault 13 ef)))

private theorem ResolventIdentityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ResolventIdentityUp,
      resolventIdentityFromEventFlow (resolventIdentityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X T lambda mu A_lambda A_mu U_lambda U_mu I D H C P N =>
      change
        some
          (ResolventIdentityUp.mk
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist X))
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist T))
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist lambda))
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist mu))
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist A_lambda))
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist A_mu))
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist U_lambda))
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist U_mu))
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist I))
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist D))
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist H))
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist C))
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist P))
            (resolventIdentityDecodeBHist (resolventIdentityEncodeBHist N))) =
          some
            (ResolventIdentityUp.mk X T lambda mu A_lambda A_mu U_lambda U_mu I D H C P N)
      rw [ResolventIdentityTasteGate_single_carrier_alignment_decode_encode X,
        ResolventIdentityTasteGate_single_carrier_alignment_decode_encode T,
        ResolventIdentityTasteGate_single_carrier_alignment_decode_encode lambda,
        ResolventIdentityTasteGate_single_carrier_alignment_decode_encode mu,
        ResolventIdentityTasteGate_single_carrier_alignment_decode_encode A_lambda,
        ResolventIdentityTasteGate_single_carrier_alignment_decode_encode A_mu,
        ResolventIdentityTasteGate_single_carrier_alignment_decode_encode U_lambda,
        ResolventIdentityTasteGate_single_carrier_alignment_decode_encode U_mu,
        ResolventIdentityTasteGate_single_carrier_alignment_decode_encode I,
        ResolventIdentityTasteGate_single_carrier_alignment_decode_encode D,
        ResolventIdentityTasteGate_single_carrier_alignment_decode_encode H,
        ResolventIdentityTasteGate_single_carrier_alignment_decode_encode C,
        ResolventIdentityTasteGate_single_carrier_alignment_decode_encode P,
        ResolventIdentityTasteGate_single_carrier_alignment_decode_encode N]

private theorem ResolventIdentityTasteGate_single_carrier_alignment_injective
    {x y : ResolventIdentityUp} :
    resolventIdentityToEventFlow x = resolventIdentityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      resolventIdentityFromEventFlow (resolventIdentityToEventFlow x) =
        resolventIdentityFromEventFlow (resolventIdentityToEventFlow y) :=
    congrArg resolventIdentityFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (ResolventIdentityTasteGate_single_carrier_alignment_round_trip x).symm
        (Eq.trans hread (ResolventIdentityTasteGate_single_carrier_alignment_round_trip y)))

instance resolventIdentityBHistCarrier : BHistCarrier ResolventIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := resolventIdentityToEventFlow
  fromEventFlow := resolventIdentityFromEventFlow

instance resolventIdentityChapterTasteGate : ChapterTasteGate ResolventIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change resolventIdentityFromEventFlow (resolventIdentityToEventFlow x) = some x
    exact ResolventIdentityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ResolventIdentityTasteGate_single_carrier_alignment_injective heq)

theorem ResolventIdentityTasteGate_single_carrier_alignment :
    (∀ h : BHist, resolventIdentityDecodeBHist (resolventIdentityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ResolventIdentityUp) ∧
      Nonempty (ChapterTasteGate ResolventIdentityUp) ∧
      resolventIdentityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ResolventIdentityTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨resolventIdentityBHistCarrier⟩, ⟨⟨resolventIdentityChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.ResolventIdentityUp
