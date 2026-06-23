import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def MetacicCandidateNormalizationConfluenceHandoffEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: MetacicCandidateNormalizationConfluenceHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: MetacicCandidateNormalizationConfluenceHandoffEncodeBHist h

def MetacicCandidateNormalizationConfluenceHandoffDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist tail)

private theorem MetacicCandidateNormalizationConfluenceHandoff_decode_encode_bhist :
    ∀ h : BHist,
      MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
        (MetacicCandidateNormalizationConfluenceHandoffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def MetacicCandidateNormalizationConfluenceHandoffFields :
    MetacicCandidateNormalizationConfluenceHandoffUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetacicCandidateNormalizationConfluenceHandoffUp.mk A K N F C D B H R P L =>
      [A, K, N, F, C, D, B, H, R, P, L]

def MetacicCandidateNormalizationConfluenceHandoffToEventFlow :
    MetacicCandidateNormalizationConfluenceHandoffUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (MetacicCandidateNormalizationConfluenceHandoffFields x).map
        MetacicCandidateNormalizationConfluenceHandoffEncodeBHist

private def MetacicCandidateNormalizationConfluenceHandoffEventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      MetacicCandidateNormalizationConfluenceHandoffEventAt index rest

def MetacicCandidateNormalizationConfluenceHandoffFromEventFlow
    (ef : EventFlow) : Option MetacicCandidateNormalizationConfluenceHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetacicCandidateNormalizationConfluenceHandoffUp.mk
      (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
        (MetacicCandidateNormalizationConfluenceHandoffEventAt 0 ef))
      (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
        (MetacicCandidateNormalizationConfluenceHandoffEventAt 1 ef))
      (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
        (MetacicCandidateNormalizationConfluenceHandoffEventAt 2 ef))
      (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
        (MetacicCandidateNormalizationConfluenceHandoffEventAt 3 ef))
      (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
        (MetacicCandidateNormalizationConfluenceHandoffEventAt 4 ef))
      (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
        (MetacicCandidateNormalizationConfluenceHandoffEventAt 5 ef))
      (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
        (MetacicCandidateNormalizationConfluenceHandoffEventAt 6 ef))
      (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
        (MetacicCandidateNormalizationConfluenceHandoffEventAt 7 ef))
      (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
        (MetacicCandidateNormalizationConfluenceHandoffEventAt 8 ef))
      (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
        (MetacicCandidateNormalizationConfluenceHandoffEventAt 9 ef))
      (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
        (MetacicCandidateNormalizationConfluenceHandoffEventAt 10 ef)))

private theorem MetacicCandidateNormalizationConfluenceHandoff_round_trip
    (x : MetacicCandidateNormalizationConfluenceHandoffUp) :
    MetacicCandidateNormalizationConfluenceHandoffFromEventFlow
      (MetacicCandidateNormalizationConfluenceHandoffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A K N F C D B H R P L =>
      change
        some
          (MetacicCandidateNormalizationConfluenceHandoffUp.mk
            (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
              (MetacicCandidateNormalizationConfluenceHandoffEncodeBHist A))
            (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
              (MetacicCandidateNormalizationConfluenceHandoffEncodeBHist K))
            (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
              (MetacicCandidateNormalizationConfluenceHandoffEncodeBHist N))
            (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
              (MetacicCandidateNormalizationConfluenceHandoffEncodeBHist F))
            (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
              (MetacicCandidateNormalizationConfluenceHandoffEncodeBHist C))
            (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
              (MetacicCandidateNormalizationConfluenceHandoffEncodeBHist D))
            (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
              (MetacicCandidateNormalizationConfluenceHandoffEncodeBHist B))
            (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
              (MetacicCandidateNormalizationConfluenceHandoffEncodeBHist H))
            (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
              (MetacicCandidateNormalizationConfluenceHandoffEncodeBHist R))
            (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
              (MetacicCandidateNormalizationConfluenceHandoffEncodeBHist P))
            (MetacicCandidateNormalizationConfluenceHandoffDecodeBHist
              (MetacicCandidateNormalizationConfluenceHandoffEncodeBHist L))) =
          some (MetacicCandidateNormalizationConfluenceHandoffUp.mk A K N F C D B H R P L)
      rw [MetacicCandidateNormalizationConfluenceHandoff_decode_encode_bhist A,
        MetacicCandidateNormalizationConfluenceHandoff_decode_encode_bhist K,
        MetacicCandidateNormalizationConfluenceHandoff_decode_encode_bhist N,
        MetacicCandidateNormalizationConfluenceHandoff_decode_encode_bhist F,
        MetacicCandidateNormalizationConfluenceHandoff_decode_encode_bhist C,
        MetacicCandidateNormalizationConfluenceHandoff_decode_encode_bhist D,
        MetacicCandidateNormalizationConfluenceHandoff_decode_encode_bhist B,
        MetacicCandidateNormalizationConfluenceHandoff_decode_encode_bhist H,
        MetacicCandidateNormalizationConfluenceHandoff_decode_encode_bhist R,
        MetacicCandidateNormalizationConfluenceHandoff_decode_encode_bhist P,
        MetacicCandidateNormalizationConfluenceHandoff_decode_encode_bhist L]

private theorem MetacicCandidateNormalizationConfluenceHandoffToEventFlow_injective
    {x y : MetacicCandidateNormalizationConfluenceHandoffUp} :
    MetacicCandidateNormalizationConfluenceHandoffToEventFlow x =
        MetacicCandidateNormalizationConfluenceHandoffToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      MetacicCandidateNormalizationConfluenceHandoffFromEventFlow
          (MetacicCandidateNormalizationConfluenceHandoffToEventFlow x) =
        MetacicCandidateNormalizationConfluenceHandoffFromEventFlow
          (MetacicCandidateNormalizationConfluenceHandoffToEventFlow y) :=
    congrArg MetacicCandidateNormalizationConfluenceHandoffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetacicCandidateNormalizationConfluenceHandoff_round_trip x).symm
      (Eq.trans hread (MetacicCandidateNormalizationConfluenceHandoff_round_trip y)))

private theorem MetacicCandidateNormalizationConfluenceHandoff_field_faithful :
    ∀ x y : MetacicCandidateNormalizationConfluenceHandoffUp,
      MetacicCandidateNormalizationConfluenceHandoffFields x =
        MetacicCandidateNormalizationConfluenceHandoffFields y →
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ K₁ N₁ F₁ C₁ D₁ B₁ H₁ R₁ P₁ L₁ =>
      cases y with
      | mk A₂ K₂ N₂ F₂ C₂ D₂ B₂ H₂ R₂ P₂ L₂ =>
          cases hfields
          rfl

instance metacicCandidateNormalizationConfluenceHandoffBHistCarrier :
    BHistCarrier MetacicCandidateNormalizationConfluenceHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := MetacicCandidateNormalizationConfluenceHandoffToEventFlow
  fromEventFlow := MetacicCandidateNormalizationConfluenceHandoffFromEventFlow

instance metacicCandidateNormalizationConfluenceHandoffChapterTasteGate :
    ChapterTasteGate MetacicCandidateNormalizationConfluenceHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      MetacicCandidateNormalizationConfluenceHandoffFromEventFlow
        (MetacicCandidateNormalizationConfluenceHandoffToEventFlow x) = some x
    exact MetacicCandidateNormalizationConfluenceHandoff_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetacicCandidateNormalizationConfluenceHandoffToEventFlow_injective heq)

instance metacicCandidateNormalizationConfluenceHandoffFieldFaithful :
    FieldFaithful MetacicCandidateNormalizationConfluenceHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := MetacicCandidateNormalizationConfluenceHandoffFields
  field_faithful := MetacicCandidateNormalizationConfluenceHandoff_field_faithful

instance metacicCandidateNormalizationConfluenceHandoffNontrivial :
    Nontrivial MetacicCandidateNormalizationConfluenceHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetacicCandidateNormalizationConfluenceHandoffUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MetacicCandidateNormalizationConfluenceHandoffUp.mk (BHist.e0 BHist.Empty)
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def MetacicCandidateNormalizationConfluenceHandoff_taste_gate :
    ChapterTasteGate MetacicCandidateNormalizationConfluenceHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metacicCandidateNormalizationConfluenceHandoffChapterTasteGate

end BEDC.Derived
