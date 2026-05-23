import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExternalSupplyWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExternalSupplyWitnessUp : Type where
  | mk (S R G L H C P N : BHist) : ExternalSupplyWitnessUp
  deriving DecidableEq

def externalSupplyWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: externalSupplyWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: externalSupplyWitnessEncodeBHist h

def externalSupplyWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (externalSupplyWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (externalSupplyWitnessDecodeBHist tail)

private theorem externalSupplyWitness_decode_encode_bhist :
    ∀ h : BHist, externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def externalSupplyWitnessFields : ExternalSupplyWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ExternalSupplyWitnessUp.mk S R G L H C P N => [S, R, G, L, H, C, P, N]

def externalSupplyWitnessToEventFlow : ExternalSupplyWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (externalSupplyWitnessFields x).map externalSupplyWitnessEncodeBHist

private def externalSupplyWitnessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => externalSupplyWitnessEventAtDefault index rest

def externalSupplyWitnessFromEventFlow : EventFlow → Option ExternalSupplyWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ExternalSupplyWitnessUp.mk
        (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEventAtDefault 0 ef))
        (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEventAtDefault 1 ef))
        (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEventAtDefault 2 ef))
        (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEventAtDefault 3 ef))
        (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEventAtDefault 4 ef))
        (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEventAtDefault 5 ef))
        (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEventAtDefault 6 ef))
        (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEventAtDefault 7 ef)))

private theorem externalSupplyWitness_round_trip :
    ∀ x : ExternalSupplyWitnessUp,
      externalSupplyWitnessFromEventFlow (externalSupplyWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R G L H C P N =>
      change
        some
          (ExternalSupplyWitnessUp.mk
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist S))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist R))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist G))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist L))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist H))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist C))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist P))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist N))) =
          some (ExternalSupplyWitnessUp.mk S R G L H C P N)
      rw [externalSupplyWitness_decode_encode_bhist S, externalSupplyWitness_decode_encode_bhist R,
        externalSupplyWitness_decode_encode_bhist G, externalSupplyWitness_decode_encode_bhist L,
        externalSupplyWitness_decode_encode_bhist H, externalSupplyWitness_decode_encode_bhist C,
        externalSupplyWitness_decode_encode_bhist P, externalSupplyWitness_decode_encode_bhist N]

private theorem externalSupplyWitnessToEventFlow_injective
    {x y : ExternalSupplyWitnessUp} :
    externalSupplyWitnessToEventFlow x = externalSupplyWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      externalSupplyWitnessFromEventFlow (externalSupplyWitnessToEventFlow x) =
        externalSupplyWitnessFromEventFlow (externalSupplyWitnessToEventFlow y) :=
    congrArg externalSupplyWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (externalSupplyWitness_round_trip x).symm
      (Eq.trans hread (externalSupplyWitness_round_trip y)))

private theorem externalSupplyWitness_field_faithful :
    ∀ x y : ExternalSupplyWitnessUp,
      externalSupplyWitnessFields x = externalSupplyWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ R₁ G₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ R₂ G₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance externalSupplyWitnessBHistCarrier : BHistCarrier ExternalSupplyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := externalSupplyWitnessToEventFlow
  fromEventFlow := externalSupplyWitnessFromEventFlow

instance externalSupplyWitnessChapterTasteGate : ChapterTasteGate ExternalSupplyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change externalSupplyWitnessFromEventFlow (externalSupplyWitnessToEventFlow x) = some x
    exact externalSupplyWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (externalSupplyWitnessToEventFlow_injective heq)

instance externalSupplyWitnessFieldFaithful : FieldFaithful ExternalSupplyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := externalSupplyWitnessFields
  field_faithful := externalSupplyWitness_field_faithful

instance externalSupplyWitnessNontrivial : Nontrivial ExternalSupplyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ExternalSupplyWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ExternalSupplyWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ExternalSupplyWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  externalSupplyWitnessChapterTasteGate

theorem ExternalSupplyWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist h) = h) ∧
      (∀ x : ExternalSupplyWitnessUp,
        externalSupplyWitnessFromEventFlow (externalSupplyWitnessToEventFlow x) = some x) ∧
        (∀ x y : ExternalSupplyWitnessUp,
          externalSupplyWitnessToEventFlow x = externalSupplyWitnessToEventFlow y → x = y) ∧
          externalSupplyWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨externalSupplyWitness_decode_encode_bhist,
      externalSupplyWitness_round_trip,
      (fun _ _ heq => externalSupplyWitnessToEventFlow_injective heq),
      rfl⟩

theorem ExternalSupplyWitness_namecert_obligations {S R G L H C P N : BHist} :
    SemanticNameCert
      (fun row : BHist =>
        ∃ packet : ExternalSupplyWitnessUp,
          packet = ExternalSupplyWitnessUp.mk S R G L H C P N ∧ hsame row N)
      (fun row : BHist =>
        externalSupplyWitnessFields (ExternalSupplyWitnessUp.mk S R G L H C P N) =
            [S, R, G, L, H, C, P, N] ∧
          hsame row N)
      (fun row : BHist =>
        hsame row N ∧ externalSupplyWitnessEncodeBHist BHist.Empty = ([] : List BMark))
      hsame := by
  -- BEDC touchpoint anchor: BHist BMark NameCert SemanticNameCert hsame
  refine
    { core := ?core
      pattern_sound := ?pattern_sound
      ledger_sound := ?ledger_sound }
  · refine
      { carrier_inhabited := ?carrier_inhabited
        equiv_refl := ?equiv_refl
        equiv_symm := ?equiv_symm
        equiv_trans := ?equiv_trans
        carrier_respects_equiv := ?carrier_respects_equiv }
    · exact
        Exists.intro N
          (Exists.intro (ExternalSupplyWitnessUp.mk S R G L H C P N)
            (And.intro rfl (hsame_refl N)))
    · intro h _source
      exact hsame_refl h
    · intro h k hhk
      exact hsame_symm hhk
    · intro h k r hhk hkr
      exact hsame_trans hhk hkr
    · intro h k hhk source
      cases source with
      | intro packet packetRows =>
          cases packetRows with
          | intro packetEq rowName =>
              exact
                Exists.intro packet
                  (And.intro packetEq (hsame_trans (hsame_symm hhk) rowName))
  · intro row source
    cases source with
    | intro _packet packetRows =>
        cases packetRows with
        | intro _packetEq rowName =>
            exact And.intro rfl rowName
  · intro row source
    cases source with
    | intro _packet packetRows =>
        cases packetRows with
        | intro _packetEq rowName =>
            exact And.intro rowName rfl

theorem ExternalSupplyWitness_socket_factorization {S R G L H C P N row mid routed : BHist} :
    hsame row mid →
      hsame mid routed →
        (∃ packet : ExternalSupplyWitnessUp,
          packet = ExternalSupplyWitnessUp.mk S R G L H C P N ∧ hsame row N) →
          (externalSupplyWitnessFields (ExternalSupplyWitnessUp.mk S R G L H C P N) =
              [S, R, G, L, H, C, P, N] ∧ hsame routed N) ∧
            (hsame routed N ∧
              externalSupplyWitnessEncodeBHist BHist.Empty = ([] : List BMark)) := by
  -- BEDC touchpoint anchor: BHist BMark SemanticNameCert hsame
  intro rowMid midRouted source
  exact
    semanticNameCert_classifier_chain_transport
      (ExternalSupplyWitness_namecert_obligations (S := S) (R := R) (G := G) (L := L)
        (H := H) (C := C) (P := P) (N := N))
      rowMid midRouted source

end BEDC.Derived.ExternalSupplyWitnessUp
