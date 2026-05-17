import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TermStratumChoiceClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TermStratumChoiceClosureUp : Type where
  | mk (I F W M R H C P N : BHist) : TermStratumChoiceClosureUp
  deriving DecidableEq

def termStratumChoiceClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: termStratumChoiceClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: termStratumChoiceClosureEncodeBHist h

def termStratumChoiceClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (termStratumChoiceClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (termStratumChoiceClosureDecodeBHist tail)

private theorem termStratumChoiceClosure_decode_encode_bhist :
    ∀ h : BHist, termStratumChoiceClosureDecodeBHist
      (termStratumChoiceClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem termStratumChoiceClosure_mk_congr
    {I I' F F' W W' M M' R R' H H' C C' P P' N N' : BHist}
    (hI : I' = I) (hF : F' = F) (hW : W' = W) (hM : M' = M) (hR : R' = R)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    TermStratumChoiceClosureUp.mk I' F' W' M' R' H' C' P' N' =
      TermStratumChoiceClosureUp.mk I F W M R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hI
  cases hF
  cases hW
  cases hM
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private def termStratumChoiceClosureFields :
    TermStratumChoiceClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TermStratumChoiceClosureUp.mk I F W M R H C P N => [I, F, W, M, R, H, C, P, N]

def termStratumChoiceClosureToEventFlow :
    TermStratumChoiceClosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (termStratumChoiceClosureFields x).map termStratumChoiceClosureEncodeBHist

private def termStratumChoiceClosureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => termStratumChoiceClosureEventAtDefault index rest

def termStratumChoiceClosureFromEventFlow :
    EventFlow → Option TermStratumChoiceClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (TermStratumChoiceClosureUp.mk
        (termStratumChoiceClosureDecodeBHist (termStratumChoiceClosureEventAtDefault 0 ef))
        (termStratumChoiceClosureDecodeBHist (termStratumChoiceClosureEventAtDefault 1 ef))
        (termStratumChoiceClosureDecodeBHist (termStratumChoiceClosureEventAtDefault 2 ef))
        (termStratumChoiceClosureDecodeBHist (termStratumChoiceClosureEventAtDefault 3 ef))
        (termStratumChoiceClosureDecodeBHist (termStratumChoiceClosureEventAtDefault 4 ef))
        (termStratumChoiceClosureDecodeBHist (termStratumChoiceClosureEventAtDefault 5 ef))
        (termStratumChoiceClosureDecodeBHist (termStratumChoiceClosureEventAtDefault 6 ef))
        (termStratumChoiceClosureDecodeBHist (termStratumChoiceClosureEventAtDefault 7 ef))
        (termStratumChoiceClosureDecodeBHist (termStratumChoiceClosureEventAtDefault 8 ef)))

private theorem termStratumChoiceClosure_round_trip :
    ∀ x : TermStratumChoiceClosureUp,
      termStratumChoiceClosureFromEventFlow
        (termStratumChoiceClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F W M R H C P N =>
      exact
        congrArg some
          (termStratumChoiceClosure_mk_congr
            (termStratumChoiceClosure_decode_encode_bhist I)
            (termStratumChoiceClosure_decode_encode_bhist F)
            (termStratumChoiceClosure_decode_encode_bhist W)
            (termStratumChoiceClosure_decode_encode_bhist M)
            (termStratumChoiceClosure_decode_encode_bhist R)
            (termStratumChoiceClosure_decode_encode_bhist H)
            (termStratumChoiceClosure_decode_encode_bhist C)
            (termStratumChoiceClosure_decode_encode_bhist P)
            (termStratumChoiceClosure_decode_encode_bhist N))

private theorem termStratumChoiceClosureToEventFlow_injective
    {x y : TermStratumChoiceClosureUp} :
    termStratumChoiceClosureToEventFlow x = termStratumChoiceClosureToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      termStratumChoiceClosureFromEventFlow (termStratumChoiceClosureToEventFlow x) =
        termStratumChoiceClosureFromEventFlow (termStratumChoiceClosureToEventFlow y) :=
    congrArg termStratumChoiceClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (termStratumChoiceClosure_round_trip x).symm
      (Eq.trans hread (termStratumChoiceClosure_round_trip y)))

private theorem termStratumChoiceClosure_field_faithful :
    ∀ x y : TermStratumChoiceClosureUp,
      termStratumChoiceClosureFields x = termStratumChoiceClosureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I F W M R H C P N =>
      cases y with
      | mk I' F' W' M' R' H' C' P' N' =>
          cases hfields
          rfl

instance termStratumChoiceClosureBHistCarrier :
    BHistCarrier TermStratumChoiceClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := termStratumChoiceClosureToEventFlow
  fromEventFlow := termStratumChoiceClosureFromEventFlow

instance termStratumChoiceClosureChapterTasteGate :
    ChapterTasteGate TermStratumChoiceClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change termStratumChoiceClosureFromEventFlow
      (termStratumChoiceClosureToEventFlow x) = some x
    exact termStratumChoiceClosure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (termStratumChoiceClosureToEventFlow_injective heq)

instance termStratumChoiceClosureFieldFaithful :
    FieldFaithful TermStratumChoiceClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := termStratumChoiceClosureFields
  field_faithful := termStratumChoiceClosure_field_faithful

instance termStratumChoiceClosureNontrivial :
    Nontrivial TermStratumChoiceClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TermStratumChoiceClosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TermStratumChoiceClosureUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TermStratumChoiceClosureTasteGate_single_carrier_alignment :
    (∀ h : BHist, termStratumChoiceClosureDecodeBHist
      (termStratumChoiceClosureEncodeBHist h) = h) ∧
      (∀ x : TermStratumChoiceClosureUp,
        termStratumChoiceClosureFromEventFlow
          (termStratumChoiceClosureToEventFlow x) = some x) ∧
        (∀ x y : TermStratumChoiceClosureUp,
          termStratumChoiceClosureToEventFlow x =
              termStratumChoiceClosureToEventFlow y →
            x = y) ∧
          Nonempty (ChapterTasteGate TermStratumChoiceClosureUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨termStratumChoiceClosure_decode_encode_bhist,
      termStratumChoiceClosure_round_trip,
      (fun _ _ heq => termStratumChoiceClosureToEventFlow_injective heq),
      ⟨termStratumChoiceClosureChapterTasteGate⟩⟩

end BEDC.Derived.TermStratumChoiceClosureUp
