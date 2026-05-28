import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DoobUpcrossingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DoobUpcrossingUp : Type where
  | mk (Ω M a b N U E B H C P Q : BHist) : DoobUpcrossingUp
  deriving DecidableEq

def doobUpcrossingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: doobUpcrossingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: doobUpcrossingEncodeBHist h

def doobUpcrossingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (doobUpcrossingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (doobUpcrossingDecodeBHist tail)

private theorem DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def doobUpcrossingFields : DoobUpcrossingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DoobUpcrossingUp.mk Ω M a b N U E B H C P Q =>
      [Ω, M, a, b, N, U, E, B, H, C, P, Q]

def doobUpcrossingToEventFlow : DoobUpcrossingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (doobUpcrossingFields x).map doobUpcrossingEncodeBHist

private def doobUpcrossingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => doobUpcrossingEventAt index rest

def doobUpcrossingFromEventFlow (ef : EventFlow) : Option DoobUpcrossingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DoobUpcrossingUp.mk
      (doobUpcrossingDecodeBHist (doobUpcrossingEventAt 0 ef))
      (doobUpcrossingDecodeBHist (doobUpcrossingEventAt 1 ef))
      (doobUpcrossingDecodeBHist (doobUpcrossingEventAt 2 ef))
      (doobUpcrossingDecodeBHist (doobUpcrossingEventAt 3 ef))
      (doobUpcrossingDecodeBHist (doobUpcrossingEventAt 4 ef))
      (doobUpcrossingDecodeBHist (doobUpcrossingEventAt 5 ef))
      (doobUpcrossingDecodeBHist (doobUpcrossingEventAt 6 ef))
      (doobUpcrossingDecodeBHist (doobUpcrossingEventAt 7 ef))
      (doobUpcrossingDecodeBHist (doobUpcrossingEventAt 8 ef))
      (doobUpcrossingDecodeBHist (doobUpcrossingEventAt 9 ef))
      (doobUpcrossingDecodeBHist (doobUpcrossingEventAt 10 ef))
      (doobUpcrossingDecodeBHist (doobUpcrossingEventAt 11 ef)))

private theorem DoobUpcrossingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DoobUpcrossingUp,
      doobUpcrossingFromEventFlow (doobUpcrossingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Ω M a b N U E B H C P Q =>
      change
        some
          (DoobUpcrossingUp.mk
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist Ω))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist M))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist a))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist b))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist N))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist U))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist E))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist B))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist H))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist C))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist P))
            (doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist Q))) =
          some (DoobUpcrossingUp.mk Ω M a b N U E B H C P Q)
      rw [DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode Ω,
        DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode M,
        DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode a,
        DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode b,
        DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode N,
        DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode U,
        DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode E,
        DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode B,
        DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode H,
        DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode C,
        DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode P,
        DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode Q]

private theorem doobUpcrossingToEventFlow_injective {x y : DoobUpcrossingUp} :
    doobUpcrossingToEventFlow x = doobUpcrossingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      doobUpcrossingFromEventFlow (doobUpcrossingToEventFlow x) =
        doobUpcrossingFromEventFlow (doobUpcrossingToEventFlow y) :=
    congrArg doobUpcrossingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DoobUpcrossingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DoobUpcrossingTasteGate_single_carrier_alignment_round_trip y)))

private theorem doobUpcrossingFields_faithful :
    ∀ x y : DoobUpcrossingUp, doobUpcrossingFields x = doobUpcrossingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Ω₁ M₁ a₁ b₁ N₁ U₁ E₁ B₁ H₁ C₁ P₁ Q₁ =>
      cases y with
      | mk Ω₂ M₂ a₂ b₂ N₂ U₂ E₂ B₂ H₂ C₂ P₂ Q₂ =>
          injection hfields with hΩ tail0
          injection tail0 with hM tail1
          injection tail1 with ha tail2
          injection tail2 with hb tail3
          injection tail3 with hN tail4
          injection tail4 with hU tail5
          injection tail5 with hE tail6
          injection tail6 with hB tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hQ _
          subst hΩ
          subst hM
          subst ha
          subst hb
          subst hN
          subst hU
          subst hE
          subst hB
          subst hH
          subst hC
          subst hP
          subst hQ
          rfl

instance doobUpcrossingBHistCarrier : BHistCarrier DoobUpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := doobUpcrossingToEventFlow
  fromEventFlow := doobUpcrossingFromEventFlow

instance doobUpcrossingChapterTasteGate : ChapterTasteGate DoobUpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change doobUpcrossingFromEventFlow (doobUpcrossingToEventFlow x) = some x
    exact DoobUpcrossingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (doobUpcrossingToEventFlow_injective heq)

instance doobUpcrossingFieldFaithful : FieldFaithful DoobUpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := doobUpcrossingFields
  field_faithful := doobUpcrossingFields_faithful

instance doobUpcrossingNontrivial : Nontrivial DoobUpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DoobUpcrossingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DoobUpcrossingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DoobUpcrossingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  doobUpcrossingChapterTasteGate

theorem DoobUpcrossingTasteGate_single_carrier_alignment :
    (∀ h : BHist, doobUpcrossingDecodeBHist (doobUpcrossingEncodeBHist h) = h) ∧
      (∀ x : DoobUpcrossingUp,
        doobUpcrossingFromEventFlow (doobUpcrossingToEventFlow x) = some x) ∧
        (∀ x y : DoobUpcrossingUp,
          doobUpcrossingToEventFlow x = doobUpcrossingToEventFlow y → x = y) ∧
          doobUpcrossingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨DoobUpcrossingTasteGate_single_carrier_alignment_decode_encode,
      DoobUpcrossingTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => doobUpcrossingToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DoobUpcrossingUp
