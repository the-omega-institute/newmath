import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PortmanteauUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PortmanteauUp : Type where
  | mk
      (probabilitySource distribution measure tightness boundedTest realComparison transport
        tolerance componentTransport replay provenance localName : BHist) :
      PortmanteauUp
  deriving DecidableEq

def portmanteauEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: portmanteauEncodeBHist h
  | BHist.e1 h => BMark.b1 :: portmanteauEncodeBHist h

def portmanteauDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (portmanteauDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (portmanteauDecodeBHist tail)

private theorem PortmanteauTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, portmanteauDecodeBHist (portmanteauEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def portmanteauRows : PortmanteauUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PortmanteauUp.mk probabilitySource distribution measure tightness boundedTest
      realComparison transport tolerance componentTransport replay provenance localName =>
      [probabilitySource, distribution, measure, tightness, boundedTest, realComparison,
        transport, tolerance, componentTransport, replay, provenance, localName]

def portmanteauToEventFlow : PortmanteauUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (portmanteauRows x).map portmanteauEncodeBHist

private def portmanteauEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => portmanteauEventAtDefault index rest

def portmanteauFromEventFlow (ef : EventFlow) : Option PortmanteauUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PortmanteauUp.mk
      (portmanteauDecodeBHist (portmanteauEventAtDefault 0 ef))
      (portmanteauDecodeBHist (portmanteauEventAtDefault 1 ef))
      (portmanteauDecodeBHist (portmanteauEventAtDefault 2 ef))
      (portmanteauDecodeBHist (portmanteauEventAtDefault 3 ef))
      (portmanteauDecodeBHist (portmanteauEventAtDefault 4 ef))
      (portmanteauDecodeBHist (portmanteauEventAtDefault 5 ef))
      (portmanteauDecodeBHist (portmanteauEventAtDefault 6 ef))
      (portmanteauDecodeBHist (portmanteauEventAtDefault 7 ef))
      (portmanteauDecodeBHist (portmanteauEventAtDefault 8 ef))
      (portmanteauDecodeBHist (portmanteauEventAtDefault 9 ef))
      (portmanteauDecodeBHist (portmanteauEventAtDefault 10 ef))
      (portmanteauDecodeBHist (portmanteauEventAtDefault 11 ef)))

private theorem PortmanteauTasteGate_single_carrier_alignment_round_trip :
    forall x : PortmanteauUp, portmanteauFromEventFlow (portmanteauToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk probabilitySource distribution measure tightness boundedTest realComparison transport
      tolerance componentTransport replay provenance localName =>
      change
        some
          (PortmanteauUp.mk
            (portmanteauDecodeBHist (portmanteauEncodeBHist probabilitySource))
            (portmanteauDecodeBHist (portmanteauEncodeBHist distribution))
            (portmanteauDecodeBHist (portmanteauEncodeBHist measure))
            (portmanteauDecodeBHist (portmanteauEncodeBHist tightness))
            (portmanteauDecodeBHist (portmanteauEncodeBHist boundedTest))
            (portmanteauDecodeBHist (portmanteauEncodeBHist realComparison))
            (portmanteauDecodeBHist (portmanteauEncodeBHist transport))
            (portmanteauDecodeBHist (portmanteauEncodeBHist tolerance))
            (portmanteauDecodeBHist (portmanteauEncodeBHist componentTransport))
            (portmanteauDecodeBHist (portmanteauEncodeBHist replay))
            (portmanteauDecodeBHist (portmanteauEncodeBHist provenance))
            (portmanteauDecodeBHist (portmanteauEncodeBHist localName))) =
          some
            (PortmanteauUp.mk probabilitySource distribution measure tightness boundedTest
              realComparison transport tolerance componentTransport replay provenance localName)
      rw [PortmanteauTasteGate_single_carrier_alignment_decode_encode probabilitySource,
        PortmanteauTasteGate_single_carrier_alignment_decode_encode distribution,
        PortmanteauTasteGate_single_carrier_alignment_decode_encode measure,
        PortmanteauTasteGate_single_carrier_alignment_decode_encode tightness,
        PortmanteauTasteGate_single_carrier_alignment_decode_encode boundedTest,
        PortmanteauTasteGate_single_carrier_alignment_decode_encode realComparison,
        PortmanteauTasteGate_single_carrier_alignment_decode_encode transport,
        PortmanteauTasteGate_single_carrier_alignment_decode_encode tolerance,
        PortmanteauTasteGate_single_carrier_alignment_decode_encode componentTransport,
        PortmanteauTasteGate_single_carrier_alignment_decode_encode replay,
        PortmanteauTasteGate_single_carrier_alignment_decode_encode provenance,
        PortmanteauTasteGate_single_carrier_alignment_decode_encode localName]

private theorem PortmanteauTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PortmanteauUp} :
    portmanteauToEventFlow x = portmanteauToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      portmanteauFromEventFlow (portmanteauToEventFlow x) =
        portmanteauFromEventFlow (portmanteauToEventFlow y) :=
    congrArg portmanteauFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PortmanteauTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PortmanteauTasteGate_single_carrier_alignment_round_trip y)))

private theorem PortmanteauTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : PortmanteauUp, portmanteauRows x = portmanteauRows y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk probabilitySource₁ distribution₁ measure₁ tightness₁ boundedTest₁ realComparison₁
      transport₁ tolerance₁ componentTransport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk probabilitySource₂ distribution₂ measure₂ tightness₂ boundedTest₂ realComparison₂
          transport₂ tolerance₂ componentTransport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance portmanteauBHistCarrier : BHistCarrier PortmanteauUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := portmanteauToEventFlow
  fromEventFlow := portmanteauFromEventFlow

instance portmanteauChapterTasteGate : ChapterTasteGate PortmanteauUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => PortmanteauTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PortmanteauTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance portmanteauFieldFaithful : FieldFaithful PortmanteauUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := portmanteauRows
  field_faithful := PortmanteauTasteGate_single_carrier_alignment_fields_faithful

instance portmanteauNontrivial : BEDC.Meta.TasteGate.Nontrivial PortmanteauUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PortmanteauUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PortmanteauUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem PortmanteauTasteGate_single_carrier_alignment :
    (∀ h : BHist, portmanteauDecodeBHist (portmanteauEncodeBHist h) = h) ∧
      (∀ x : PortmanteauUp, portmanteauFromEventFlow (portmanteauToEventFlow x) = some x) ∧
        (∀ x y : PortmanteauUp, portmanteauToEventFlow x = portmanteauToEventFlow y -> x = y) ∧
          portmanteauEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact PortmanteauTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact PortmanteauTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact PortmanteauTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

theorem PortmanteauCarrier_namecert_obligations
    (P D M T B R A E H C Q N : BHist) :
    portmanteauRows (PortmanteauUp.mk P D M T B R A E H C Q N) =
        [P, D, M, T, B, R, A, E, H, C, Q, N] ∧
      hsame T T ∧ hsame B B ∧ hsame R R ∧
        Cont A H (append A H) ∧ Cont C Q (append C Q) := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  constructor
  · rfl
  · constructor
    · exact hsame_refl T
    · constructor
      · exact hsame_refl B
      · constructor
        · exact hsame_refl R
        · constructor
          · exact cont_intro rfl
          · exact cont_intro rfl

theorem PortmanteauCarrier_continuousmap_forward_link
    (P D M T B R A E H C Q N probeRead realRead : BHist) :
    portmanteauRows (PortmanteauUp.mk P D M T B R A E H C Q N) =
        [P, D, M, T, B, R, A, E, H, C, Q, N] ->
      Cont B R probeRead ->
        Cont probeRead E realRead ->
          hsame probeRead probeRead ∧ hsame realRead realRead ∧
            Cont B R probeRead ∧ Cont probeRead E realRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame PortmanteauUp
  intro rows boundedContinuousRoute realComparisonRoute
  have displayedRows :
      portmanteauRows (PortmanteauUp.mk P D M T B R A E H C Q N) =
        [P, D, M, T, B, R, A, E, H, C, Q, N] :=
    rows
  cases displayedRows
  exact
    ⟨hsame_refl probeRead, hsame_refl realRead, boundedContinuousRoute,
      realComparisonRoute⟩

end BEDC.Derived.PortmanteauUp
