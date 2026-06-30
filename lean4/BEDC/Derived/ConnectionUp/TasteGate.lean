import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConnectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConnectionUp : Type where
  | mk :
      (bundle manifold base fibre sectionRow tangent derivative bundleName manifoldName
        provenance : BHist) ->
        ConnectionUp
  deriving DecidableEq

def connectionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: connectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: connectionEncodeBHist h

def connectionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (connectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (connectionDecodeBHist tail)

private theorem ConnectionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, connectionDecodeBHist (connectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def connectionFields : ConnectionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConnectionUp.mk bundle manifold base fibre sectionRow tangent derivative bundleName
      manifoldName provenance =>
      [bundle, manifold, base, fibre, sectionRow, tangent, derivative, bundleName, manifoldName,
        provenance]

def connectionToEventFlow : ConnectionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (connectionFields x).map connectionEncodeBHist

def connectionEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => connectionEventAt index rest

def connectionFromEventFlow (ef : EventFlow) : Option ConnectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConnectionUp.mk
      (connectionDecodeBHist (connectionEventAt 0 ef))
      (connectionDecodeBHist (connectionEventAt 1 ef))
      (connectionDecodeBHist (connectionEventAt 2 ef))
      (connectionDecodeBHist (connectionEventAt 3 ef))
      (connectionDecodeBHist (connectionEventAt 4 ef))
      (connectionDecodeBHist (connectionEventAt 5 ef))
      (connectionDecodeBHist (connectionEventAt 6 ef))
      (connectionDecodeBHist (connectionEventAt 7 ef))
      (connectionDecodeBHist (connectionEventAt 8 ef))
      (connectionDecodeBHist (connectionEventAt 9 ef)))

private theorem connection_round_trip :
    forall x : ConnectionUp, connectionFromEventFlow (connectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk bundle manifold base fibre sectionRow tangent derivative bundleName manifoldName provenance =>
      change
        some
          (ConnectionUp.mk
            (connectionDecodeBHist (connectionEncodeBHist bundle))
            (connectionDecodeBHist (connectionEncodeBHist manifold))
            (connectionDecodeBHist (connectionEncodeBHist base))
            (connectionDecodeBHist (connectionEncodeBHist fibre))
            (connectionDecodeBHist (connectionEncodeBHist sectionRow))
            (connectionDecodeBHist (connectionEncodeBHist tangent))
            (connectionDecodeBHist (connectionEncodeBHist derivative))
            (connectionDecodeBHist (connectionEncodeBHist bundleName))
            (connectionDecodeBHist (connectionEncodeBHist manifoldName))
            (connectionDecodeBHist (connectionEncodeBHist provenance))) =
          some
            (ConnectionUp.mk bundle manifold base fibre sectionRow tangent derivative bundleName
              manifoldName provenance)
      rw [ConnectionTasteGate_single_carrier_alignment_decode_encode bundle,
        ConnectionTasteGate_single_carrier_alignment_decode_encode manifold,
        ConnectionTasteGate_single_carrier_alignment_decode_encode base,
        ConnectionTasteGate_single_carrier_alignment_decode_encode fibre,
        ConnectionTasteGate_single_carrier_alignment_decode_encode sectionRow,
        ConnectionTasteGate_single_carrier_alignment_decode_encode tangent,
        ConnectionTasteGate_single_carrier_alignment_decode_encode derivative,
        ConnectionTasteGate_single_carrier_alignment_decode_encode bundleName,
        ConnectionTasteGate_single_carrier_alignment_decode_encode manifoldName,
        ConnectionTasteGate_single_carrier_alignment_decode_encode provenance]

private theorem connectionToEventFlow_injective {x y : ConnectionUp} :
    connectionToEventFlow x = connectionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      connectionFromEventFlow (connectionToEventFlow x) =
        connectionFromEventFlow (connectionToEventFlow y) :=
    congrArg connectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (connection_round_trip x).symm (Eq.trans hread (connection_round_trip y)))

private theorem connection_field_faithful :
    forall x y : ConnectionUp, connectionFields x = connectionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk bundle₁ manifold₁ base₁ fibre₁ sectionRow₁ tangent₁ derivative₁ bundleName₁
      manifoldName₁ provenance₁ =>
      cases y with
      | mk bundle₂ manifold₂ base₂ fibre₂ sectionRow₂ tangent₂ derivative₂ bundleName₂
          manifoldName₂ provenance₂ =>
          cases hfields
          rfl

instance connectionBHistCarrier : BHistCarrier ConnectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := connectionToEventFlow
  fromEventFlow := connectionFromEventFlow

instance connectionChapterTasteGate : ChapterTasteGate ConnectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => connection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (connectionToEventFlow_injective heq)

instance connectionFieldFaithful : FieldFaithful ConnectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := connectionFields
  field_faithful := connection_field_faithful

instance connectionNontrivial : BEDC.Meta.TasteGate.Nontrivial ConnectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConnectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ConnectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def connectionTasteGate : ChapterTasteGate ConnectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  connectionChapterTasteGate

theorem ConnectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, connectionDecodeBHist (connectionEncodeBHist h) = h) ∧
      (∀ x : ConnectionUp, connectionFromEventFlow (connectionToEventFlow x) = some x) ∧
        (∀ x y : ConnectionUp, connectionToEventFlow x = connectionToEventFlow y → x = y) ∧
          connectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ConnectionTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact connection_round_trip
    · constructor
      · intro x y heq
        exact connectionToEventFlow_injective heq
      · rfl

end BEDC.Derived.ConnectionUp
