import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DecidableBetaFrontierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DecidableBetaFrontierUp : Type where
  | mk (audit lambdaRow window checker refusal compiler redex transport replay provenance name :
      BHist) : DecidableBetaFrontierUp
  deriving DecidableEq

def decidableBetaFrontierEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: decidableBetaFrontierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: decidableBetaFrontierEncodeBHist h

def decidableBetaFrontierDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decidableBetaFrontierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decidableBetaFrontierDecodeBHist tail)

private theorem decidableBetaFrontierDecode_encode_bhist :
    forall h : BHist,
      decidableBetaFrontierDecodeBHist (decidableBetaFrontierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def decidableBetaFrontierToEventFlow : DecidableBetaFrontierUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DecidableBetaFrontierUp.mk audit lambdaRow window checker refusal compiler redex transport
      replay provenance name =>
      [[BMark.b0],
        decidableBetaFrontierEncodeBHist audit,
        [BMark.b1, BMark.b0],
        decidableBetaFrontierEncodeBHist lambdaRow,
        [BMark.b1, BMark.b1, BMark.b0],
        decidableBetaFrontierEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        decidableBetaFrontierEncodeBHist checker,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        decidableBetaFrontierEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        decidableBetaFrontierEncodeBHist compiler,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        decidableBetaFrontierEncodeBHist redex,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        decidableBetaFrontierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        decidableBetaFrontierEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        decidableBetaFrontierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        decidableBetaFrontierEncodeBHist name]

private def decidableBetaFrontierEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => decidableBetaFrontierEventAt index rest

def decidableBetaFrontierFromEventFlow (ef : EventFlow) : Option DecidableBetaFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DecidableBetaFrontierUp.mk
      (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEventAt 1 ef))
      (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEventAt 3 ef))
      (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEventAt 5 ef))
      (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEventAt 7 ef))
      (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEventAt 9 ef))
      (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEventAt 11 ef))
      (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEventAt 13 ef))
      (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEventAt 15 ef))
      (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEventAt 17 ef))
      (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEventAt 19 ef))
      (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEventAt 21 ef)))

private theorem decidableBetaFrontier_round_trip :
    forall x : DecidableBetaFrontierUp,
      decidableBetaFrontierFromEventFlow (decidableBetaFrontierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk audit lambdaRow window checker refusal compiler redex transport replay provenance name =>
      change
        some
          (DecidableBetaFrontierUp.mk
            (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEncodeBHist audit))
            (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEncodeBHist lambdaRow))
            (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEncodeBHist window))
            (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEncodeBHist checker))
            (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEncodeBHist refusal))
            (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEncodeBHist compiler))
            (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEncodeBHist redex))
            (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEncodeBHist transport))
            (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEncodeBHist replay))
            (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEncodeBHist provenance))
            (decidableBetaFrontierDecodeBHist (decidableBetaFrontierEncodeBHist name))) =
          some
            (DecidableBetaFrontierUp.mk audit lambdaRow window checker refusal compiler redex
              transport replay provenance name)
      rw [decidableBetaFrontierDecode_encode_bhist audit,
        decidableBetaFrontierDecode_encode_bhist lambdaRow,
        decidableBetaFrontierDecode_encode_bhist window,
        decidableBetaFrontierDecode_encode_bhist checker,
        decidableBetaFrontierDecode_encode_bhist refusal,
        decidableBetaFrontierDecode_encode_bhist compiler,
        decidableBetaFrontierDecode_encode_bhist redex,
        decidableBetaFrontierDecode_encode_bhist transport,
        decidableBetaFrontierDecode_encode_bhist replay,
        decidableBetaFrontierDecode_encode_bhist provenance,
        decidableBetaFrontierDecode_encode_bhist name]

private theorem decidableBetaFrontierToEventFlow_injective {x y : DecidableBetaFrontierUp} :
    decidableBetaFrontierToEventFlow x = decidableBetaFrontierToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      decidableBetaFrontierFromEventFlow (decidableBetaFrontierToEventFlow x) =
        decidableBetaFrontierFromEventFlow (decidableBetaFrontierToEventFlow y) :=
    congrArg decidableBetaFrontierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (decidableBetaFrontier_round_trip x).symm
      (Eq.trans hread (decidableBetaFrontier_round_trip y)))

instance decidableBetaFrontierBHistCarrier : BHistCarrier DecidableBetaFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := decidableBetaFrontierToEventFlow
  fromEventFlow := decidableBetaFrontierFromEventFlow

instance decidableBetaFrontierChapterTasteGate : ChapterTasteGate DecidableBetaFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change decidableBetaFrontierFromEventFlow (decidableBetaFrontierToEventFlow x) = some x
    exact decidableBetaFrontier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (decidableBetaFrontierToEventFlow_injective heq)

instance decidableBetaFrontierFieldFaithful : FieldFaithful DecidableBetaFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | DecidableBetaFrontierUp.mk audit lambdaRow window checker refusal compiler redex transport
        replay provenance name =>
        [audit, lambdaRow, window, checker, refusal, compiler, redex, transport, replay,
          provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk audit₁ lambdaRow₁ window₁ checker₁ refusal₁ compiler₁ redex₁ transport₁ replay₁
        provenance₁ name₁ =>
        cases y with
        | mk audit₂ lambdaRow₂ window₂ checker₂ refusal₂ compiler₂ redex₂ transport₂ replay₂
            provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

instance decidableBetaFrontierNontrivial : Nontrivial DecidableBetaFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DecidableBetaFrontierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DecidableBetaFrontierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DecidableBetaFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  decidableBetaFrontierChapterTasteGate

theorem DecidableBetaFrontierTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DecidableBetaFrontierUp) ∧
      Nonempty (FieldFaithful DecidableBetaFrontierUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial DecidableBetaFrontierUp) ∧
      (∀ h : BHist, decidableBetaFrontierDecodeBHist (decidableBetaFrontierEncodeBHist h) = h) ∧
      (∀ x : DecidableBetaFrontierUp,
        decidableBetaFrontierFromEventFlow (decidableBetaFrontierToEventFlow x) = some x) ∧
      decidableBetaFrontierEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨decidableBetaFrontierChapterTasteGate⟩
  · constructor
    · exact ⟨decidableBetaFrontierFieldFaithful⟩
    · constructor
      · exact ⟨decidableBetaFrontierNontrivial⟩
      · constructor
        · exact decidableBetaFrontierDecode_encode_bhist
        · constructor
          · exact decidableBetaFrontier_round_trip
          · rfl

end BEDC.Derived.DecidableBetaFrontierUp
