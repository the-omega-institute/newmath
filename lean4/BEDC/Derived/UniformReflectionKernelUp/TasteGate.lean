import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformReflectionKernelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformReflectionKernelUp : Type where
  | mk (source separated handoff transport route provenance localCert : BHist) :
      UniformReflectionKernelUp
  deriving DecidableEq

def uniformReflectionKernelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformReflectionKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformReflectionKernelEncodeBHist h

def uniformReflectionKernelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformReflectionKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformReflectionKernelDecodeBHist tail)

private theorem uniformReflectionKernel_decode_encode_bhist :
    ∀ h : BHist,
      uniformReflectionKernelDecodeBHist (uniformReflectionKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def uniformReflectionKernelFields :
    UniformReflectionKernelUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformReflectionKernelUp.mk source separated handoff transport route provenance
      localCert =>
      [source, separated, handoff, transport, route, provenance, localCert]

def uniformReflectionKernelToEventFlow :
    UniformReflectionKernelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformReflectionKernelFields x).map uniformReflectionKernelEncodeBHist

private def uniformReflectionKernelEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformReflectionKernelEventAtDefault index rest

def uniformReflectionKernelFromEventFlow (ef : EventFlow) : Option UniformReflectionKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformReflectionKernelUp.mk
      (uniformReflectionKernelDecodeBHist (uniformReflectionKernelEventAtDefault 0 ef))
      (uniformReflectionKernelDecodeBHist (uniformReflectionKernelEventAtDefault 1 ef))
      (uniformReflectionKernelDecodeBHist (uniformReflectionKernelEventAtDefault 2 ef))
      (uniformReflectionKernelDecodeBHist (uniformReflectionKernelEventAtDefault 3 ef))
      (uniformReflectionKernelDecodeBHist (uniformReflectionKernelEventAtDefault 4 ef))
      (uniformReflectionKernelDecodeBHist (uniformReflectionKernelEventAtDefault 5 ef))
      (uniformReflectionKernelDecodeBHist (uniformReflectionKernelEventAtDefault 6 ef)))

private theorem uniformReflectionKernel_round_trip :
    ∀ x : UniformReflectionKernelUp,
      uniformReflectionKernelFromEventFlow (uniformReflectionKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source separated handoff transport route provenance localCert =>
      change
        some
            (UniformReflectionKernelUp.mk
              (uniformReflectionKernelDecodeBHist (uniformReflectionKernelEncodeBHist source))
              (uniformReflectionKernelDecodeBHist
                (uniformReflectionKernelEncodeBHist separated))
              (uniformReflectionKernelDecodeBHist (uniformReflectionKernelEncodeBHist handoff))
              (uniformReflectionKernelDecodeBHist
                (uniformReflectionKernelEncodeBHist transport))
              (uniformReflectionKernelDecodeBHist (uniformReflectionKernelEncodeBHist route))
              (uniformReflectionKernelDecodeBHist
                (uniformReflectionKernelEncodeBHist provenance))
              (uniformReflectionKernelDecodeBHist
                (uniformReflectionKernelEncodeBHist localCert))) =
          some
            (UniformReflectionKernelUp.mk source separated handoff transport route provenance
              localCert)
      rw [uniformReflectionKernel_decode_encode_bhist source,
        uniformReflectionKernel_decode_encode_bhist separated,
        uniformReflectionKernel_decode_encode_bhist handoff,
        uniformReflectionKernel_decode_encode_bhist transport,
        uniformReflectionKernel_decode_encode_bhist route,
        uniformReflectionKernel_decode_encode_bhist provenance,
        uniformReflectionKernel_decode_encode_bhist localCert]

private theorem uniformReflectionKernelToEventFlow_injective
    {x y : UniformReflectionKernelUp} :
    uniformReflectionKernelToEventFlow x = uniformReflectionKernelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformReflectionKernelFromEventFlow (uniformReflectionKernelToEventFlow x) =
        uniformReflectionKernelFromEventFlow (uniformReflectionKernelToEventFlow y) :=
    congrArg uniformReflectionKernelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformReflectionKernel_round_trip x).symm
      (Eq.trans hread (uniformReflectionKernel_round_trip y)))

private theorem uniformReflectionKernel_field_faithful :
    ∀ x y : UniformReflectionKernelUp,
      uniformReflectionKernelFields x = uniformReflectionKernelFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ separated₁ handoff₁ transport₁ route₁ provenance₁ localCert₁ =>
      cases y with
      | mk source₂ separated₂ handoff₂ transport₂ route₂ provenance₂ localCert₂ =>
          injection hfields with hsource tail0
          injection tail0 with hseparated tail1
          injection tail1 with hhandoff tail2
          injection tail2 with htransport tail3
          injection tail3 with hroute tail4
          injection tail4 with hprovenance tail5
          injection tail5 with hlocalCert _
          subst hsource
          subst hseparated
          subst hhandoff
          subst htransport
          subst hroute
          subst hprovenance
          subst hlocalCert
          rfl

instance uniformReflectionKernelBHistCarrier :
    BHistCarrier UniformReflectionKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformReflectionKernelToEventFlow
  fromEventFlow := uniformReflectionKernelFromEventFlow

instance uniformReflectionKernelChapterTasteGate :
    ChapterTasteGate UniformReflectionKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformReflectionKernelFromEventFlow (uniformReflectionKernelToEventFlow x) = some x
    exact uniformReflectionKernel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformReflectionKernelToEventFlow_injective heq)

instance uniformReflectionKernelFieldFaithful :
    FieldFaithful UniformReflectionKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformReflectionKernelFields
  field_faithful := uniformReflectionKernel_field_faithful

instance uniformReflectionKernelNontrivial :
    Nontrivial UniformReflectionKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformReflectionKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      UniformReflectionKernelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformReflectionKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformReflectionKernelChapterTasteGate

theorem UniformReflectionKernelTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformReflectionKernelDecodeBHist (uniformReflectionKernelEncodeBHist h) = h) ∧
      (∀ x : UniformReflectionKernelUp,
        uniformReflectionKernelFromEventFlow (uniformReflectionKernelToEventFlow x) = some x) ∧
        uniformReflectionKernelEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨uniformReflectionKernel_decode_encode_bhist, uniformReflectionKernel_round_trip, rfl⟩

end BEDC.Derived.UniformReflectionKernelUp
