import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HashDigestFiberBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HashDigestFiberBoundaryUp : Type where
  | mk :
      (digest digestSameness fiber gap refusal transport continuation provenance
        name : BHist) →
      HashDigestFiberBoundaryUp
  deriving DecidableEq

def hashDigestFiberBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hashDigestFiberBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hashDigestFiberBoundaryEncodeBHist h

def hashDigestFiberBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hashDigestFiberBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hashDigestFiberBoundaryDecodeBHist tail)

private theorem hashDigestFiberBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem hashDigestFiberBoundary_mk_congr
    {digest digest' digestSameness digestSameness' fiber fiber' gap gap' refusal refusal'
      transport transport' continuation continuation' provenance provenance' name name' : BHist}
    (hDigest : digest' = digest)
    (hDigestSameness : digestSameness' = digestSameness)
    (hFiber : fiber' = fiber)
    (hGap : gap' = gap)
    (hRefusal : refusal' = refusal)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    HashDigestFiberBoundaryUp.mk digest' digestSameness' fiber' gap' refusal' transport'
        continuation' provenance' name' =
      HashDigestFiberBoundaryUp.mk digest digestSameness fiber gap refusal transport
        continuation provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hDigest
  cases hDigestSameness
  cases hFiber
  cases hGap
  cases hRefusal
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

def hashDigestFiberBoundaryFields : HashDigestFiberBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HashDigestFiberBoundaryUp.mk digest digestSameness fiber gap refusal transport
      continuation provenance name =>
      [digest, digestSameness, fiber, gap, refusal, transport, continuation, provenance, name]

def hashDigestFiberBoundaryToEventFlow : HashDigestFiberBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hashDigestFiberBoundaryFields x).map hashDigestFiberBoundaryEncodeBHist

private def hashDigestFiberBoundaryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hashDigestFiberBoundaryEventAtDefault index rest

def hashDigestFiberBoundaryFromEventFlow (ef : EventFlow) : Option HashDigestFiberBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HashDigestFiberBoundaryUp.mk
      (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEventAtDefault 0 ef))
      (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEventAtDefault 1 ef))
      (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEventAtDefault 2 ef))
      (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEventAtDefault 3 ef))
      (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEventAtDefault 4 ef))
      (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEventAtDefault 5 ef))
      (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEventAtDefault 6 ef))
      (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEventAtDefault 7 ef))
      (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEventAtDefault 8 ef)))

private theorem hashDigestFiberBoundary_round_trip :
    ∀ x : HashDigestFiberBoundaryUp,
      hashDigestFiberBoundaryFromEventFlow (hashDigestFiberBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk digest digestSameness fiber gap refusal transport continuation provenance name =>
      change
        some
          (HashDigestFiberBoundaryUp.mk
            (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEncodeBHist digest))
            (hashDigestFiberBoundaryDecodeBHist
              (hashDigestFiberBoundaryEncodeBHist digestSameness))
            (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEncodeBHist fiber))
            (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEncodeBHist gap))
            (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEncodeBHist refusal))
            (hashDigestFiberBoundaryDecodeBHist
              (hashDigestFiberBoundaryEncodeBHist transport))
            (hashDigestFiberBoundaryDecodeBHist
              (hashDigestFiberBoundaryEncodeBHist continuation))
            (hashDigestFiberBoundaryDecodeBHist
              (hashDigestFiberBoundaryEncodeBHist provenance))
            (hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEncodeBHist name))) =
          some
            (HashDigestFiberBoundaryUp.mk digest digestSameness fiber gap refusal transport
              continuation provenance name)
      exact
        congrArg some
          (hashDigestFiberBoundary_mk_congr
            (hashDigestFiberBoundaryDecode_encode_bhist digest)
            (hashDigestFiberBoundaryDecode_encode_bhist digestSameness)
            (hashDigestFiberBoundaryDecode_encode_bhist fiber)
            (hashDigestFiberBoundaryDecode_encode_bhist gap)
            (hashDigestFiberBoundaryDecode_encode_bhist refusal)
            (hashDigestFiberBoundaryDecode_encode_bhist transport)
            (hashDigestFiberBoundaryDecode_encode_bhist continuation)
            (hashDigestFiberBoundaryDecode_encode_bhist provenance)
            (hashDigestFiberBoundaryDecode_encode_bhist name))

private theorem hashDigestFiberBoundaryToEventFlow_injective {x y : HashDigestFiberBoundaryUp} :
    hashDigestFiberBoundaryToEventFlow x = hashDigestFiberBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hashDigestFiberBoundaryFromEventFlow (hashDigestFiberBoundaryToEventFlow x) =
        hashDigestFiberBoundaryFromEventFlow (hashDigestFiberBoundaryToEventFlow y) :=
    congrArg hashDigestFiberBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hashDigestFiberBoundary_round_trip x).symm
      (Eq.trans hread (hashDigestFiberBoundary_round_trip y)))

private theorem hashDigestFiberBoundary_fields_faithful :
    ∀ x y : HashDigestFiberBoundaryUp,
      hashDigestFiberBoundaryFields x = hashDigestFiberBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk digest₁ digestSameness₁ fiber₁ gap₁ refusal₁ transport₁ continuation₁ provenance₁
      name₁ =>
      cases y with
      | mk digest₂ digestSameness₂ fiber₂ gap₂ refusal₂ transport₂ continuation₂ provenance₂
          name₂ =>
          cases hfields
          rfl

instance hashDigestFiberBoundaryBHistCarrier : BHistCarrier HashDigestFiberBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hashDigestFiberBoundaryToEventFlow
  fromEventFlow := hashDigestFiberBoundaryFromEventFlow

instance hashDigestFiberBoundaryChapterTasteGate :
    ChapterTasteGate HashDigestFiberBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hashDigestFiberBoundaryFromEventFlow (hashDigestFiberBoundaryToEventFlow x) = some x
    exact hashDigestFiberBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hashDigestFiberBoundaryToEventFlow_injective heq)

instance hashDigestFiberBoundaryFieldFaithful :
    FieldFaithful HashDigestFiberBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hashDigestFiberBoundaryFields
  field_faithful := hashDigestFiberBoundary_fields_faithful

instance hashDigestFiberBoundaryNontrivial : Nontrivial HashDigestFiberBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HashDigestFiberBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HashDigestFiberBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HashDigestFiberBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hashDigestFiberBoundaryChapterTasteGate

theorem HashDigestFiberBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hashDigestFiberBoundaryDecodeBHist (hashDigestFiberBoundaryEncodeBHist h) = h) ∧
      (∀ x : HashDigestFiberBoundaryUp,
        hashDigestFiberBoundaryFromEventFlow (hashDigestFiberBoundaryToEventFlow x) = some x) ∧
        (∀ x y : HashDigestFiberBoundaryUp,
          hashDigestFiberBoundaryToEventFlow x = hashDigestFiberBoundaryToEventFlow y →
            x = y) ∧
          hashDigestFiberBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact hashDigestFiberBoundaryDecode_encode_bhist
  · constructor
    · exact hashDigestFiberBoundary_round_trip
    · constructor
      · intro x y heq
        exact hashDigestFiberBoundaryToEventFlow_injective heq
      · rfl

theorem HashDigestFiberBoundary_nonescape (Bdry : HashDigestFiberBoundaryUp) :
    ∃ D E F G R H C P N : BHist,
      Bdry = HashDigestFiberBoundaryUp.mk D E F G R H C P N ∧
        SemanticNameCert
          (fun row : BHist =>
            hsame row D ∨ hsame row E ∨ hsame row F ∨ hsame row G ∨ hsame row R ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            hsame row D ∨ hsame row E ∨ hsame row F ∨ hsame row G ∨ hsame row R ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            hsame row D ∨ hsame row E ∨ hsame row F ∨ hsame row G ∨ hsame row R ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          hsame := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame NameCert
  cases Bdry with
  | mk D E F G R H C P N =>
      refine ⟨D, E, F, G, R, H, C, P, N, rfl, ?_⟩
      exact {
        core := {
          carrier_inhabited := ⟨D, Or.inl (hsame_refl D)⟩
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other sameRows
            exact hsame_symm sameRows
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro _row _other sameRows source
            cases sameRows
            exact source
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.HashDigestFiberBoundaryUp
