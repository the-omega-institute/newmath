import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionTriangleIdentityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionTriangleIdentityUp : Type where
  | mk
      (monad unit counit adjunction idempotent leftRoute rightRoute stream dyadic
        realRegular transport replay provenance nameCert : BHist) :
      CauchyCompletionTriangleIdentityUp
  deriving DecidableEq

def cauchyCompletionTriangleIdentityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionTriangleIdentityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionTriangleIdentityEncodeBHist h

def cauchyCompletionTriangleIdentityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionTriangleIdentityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionTriangleIdentityDecodeBHist tail)

private theorem CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionTriangleIdentityDecodeBHist
          (cauchyCompletionTriangleIdentityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionTriangleIdentityFields :
    CauchyCompletionTriangleIdentityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionTriangleIdentityUp.mk monad unit counit adjunction idempotent
      leftRoute rightRoute stream dyadic realRegular transport replay provenance
      nameCert =>
      [monad, unit, counit, adjunction, idempotent, leftRoute, rightRoute, stream,
        dyadic, realRegular, transport, replay, provenance, nameCert]

def cauchyCompletionTriangleIdentityToEventFlow :
    CauchyCompletionTriangleIdentityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map cauchyCompletionTriangleIdentityEncodeBHist
        (cauchyCompletionTriangleIdentityFields x)

private def cauchyCompletionTriangleIdentityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionTriangleIdentityEventAt index rest

def cauchyCompletionTriangleIdentityFromEventFlow :
    EventFlow → Option CauchyCompletionTriangleIdentityUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchyCompletionTriangleIdentityUp.mk
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 0 ef))
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 1 ef))
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 2 ef))
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 3 ef))
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 4 ef))
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 5 ef))
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 6 ef))
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 7 ef))
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 8 ef))
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 9 ef))
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 10 ef))
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 11 ef))
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 12 ef))
          (cauchyCompletionTriangleIdentityDecodeBHist
            (cauchyCompletionTriangleIdentityEventAt 13 ef)))

private theorem CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionTriangleIdentityUp,
      cauchyCompletionTriangleIdentityFromEventFlow
          (cauchyCompletionTriangleIdentityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk monad unit counit adjunction idempotent leftRoute rightRoute stream dyadic
      realRegular transport replay provenance nameCert =>
      change
        some
          (CauchyCompletionTriangleIdentityUp.mk
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist monad))
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist unit))
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist counit))
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist adjunction))
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist idempotent))
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist leftRoute))
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist rightRoute))
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist stream))
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist dyadic))
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist realRegular))
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist transport))
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist replay))
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist provenance))
            (cauchyCompletionTriangleIdentityDecodeBHist
              (cauchyCompletionTriangleIdentityEncodeBHist nameCert))) =
          some
            (CauchyCompletionTriangleIdentityUp.mk monad unit counit adjunction
              idempotent leftRoute rightRoute stream dyadic realRegular transport
              replay provenance nameCert)
      rw [CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
          monad,
        CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
          unit,
        CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
          counit,
        CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
          adjunction,
        CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
          idempotent,
        CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
          leftRoute,
        CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
          rightRoute,
        CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
          stream,
        CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
          dyadic,
        CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
          realRegular,
        CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
          transport,
        CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode replay,
        CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
          provenance,
        CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
          nameCert]

private theorem CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_injective
    {x y : CauchyCompletionTriangleIdentityUp} :
    cauchyCompletionTriangleIdentityToEventFlow x =
        cauchyCompletionTriangleIdentityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionTriangleIdentityFromEventFlow
          (cauchyCompletionTriangleIdentityToEventFlow x) =
        cauchyCompletionTriangleIdentityFromEventFlow
          (cauchyCompletionTriangleIdentityToEventFlow y) :=
    congrArg cauchyCompletionTriangleIdentityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyCompletionTriangleIdentity_field_faithful :
    ∀ x y : CauchyCompletionTriangleIdentityUp,
      cauchyCompletionTriangleIdentityFields x =
          cauchyCompletionTriangleIdentityFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk monad1 unit1 counit1 adjunction1 idempotent1 leftRoute1 rightRoute1 stream1
      dyadic1 realRegular1 transport1 replay1 provenance1 nameCert1 =>
      cases y with
      | mk monad2 unit2 counit2 adjunction2 idempotent2 leftRoute2 rightRoute2
          stream2 dyadic2 realRegular2 transport2 replay2 provenance2 nameCert2 =>
          cases h
          rfl

instance cauchyCompletionTriangleIdentityBHistCarrier :
    BHistCarrier CauchyCompletionTriangleIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionTriangleIdentityToEventFlow
  fromEventFlow := cauchyCompletionTriangleIdentityFromEventFlow

instance cauchyCompletionTriangleIdentityChapterTasteGate :
    ChapterTasteGate CauchyCompletionTriangleIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionTriangleIdentityFromEventFlow
          (cauchyCompletionTriangleIdentityToEventFlow x) =
        some x
    exact CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_injective heq)

instance cauchyCompletionTriangleIdentityFieldFaithful :
    FieldFaithful CauchyCompletionTriangleIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionTriangleIdentityFields
  field_faithful := cauchyCompletionTriangleIdentity_field_faithful

instance cauchyCompletionTriangleIdentityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyCompletionTriangleIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionTriangleIdentityUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionTriangleIdentityUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCompletionTriangleIdentityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionTriangleIdentityChapterTasteGate

theorem CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionTriangleIdentityDecodeBHist
          (cauchyCompletionTriangleIdentityEncodeBHist h) =
        h) ∧
      (∀ x : CauchyCompletionTriangleIdentityUp,
        cauchyCompletionTriangleIdentityFromEventFlow
            (cauchyCompletionTriangleIdentityToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyCompletionTriangleIdentityUp,
          cauchyCompletionTriangleIdentityToEventFlow x =
              cauchyCompletionTriangleIdentityToEventFlow y →
            x = y) ∧
          cauchyCompletionTriangleIdentityEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_decode
  · constructor
    · exact CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CauchyCompletionTriangleIdentityTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.CauchyCompletionTriangleIdentityUp
