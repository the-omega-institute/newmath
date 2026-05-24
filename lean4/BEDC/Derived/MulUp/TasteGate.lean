import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MulUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MulUp : Type where
  | mk
      (multiplicand multiplier product additiveLedger recursionLedger provenance
        localNameCert : BHist) :
        MulUp
  deriving DecidableEq

def mulUpEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mulUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mulUpEncodeBHist h

def mulUpDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mulUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mulUpDecodeBHist tail)

private theorem mulUpDecode_encode_bhist :
    ∀ h : BHist, mulUpDecodeBHist (mulUpEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def mulUpFields : MulUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MulUp.mk multiplicand multiplier product additiveLedger recursionLedger provenance
      localNameCert =>
      [multiplicand, multiplier, product, additiveLedger, recursionLedger, provenance,
        localNameCert]

def mulUpToEventFlow : MulUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MulUp.mk multiplicand multiplier product additiveLedger recursionLedger provenance
      localNameCert =>
      [[BMark.b1, BMark.b0, BMark.b0],
        mulUpEncodeBHist multiplicand,
        mulUpEncodeBHist multiplier,
        mulUpEncodeBHist product,
        mulUpEncodeBHist additiveLedger,
        mulUpEncodeBHist recursionLedger,
        mulUpEncodeBHist provenance,
        mulUpEncodeBHist localNameCert]

private def mulUpEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mulUpEventAt index rest

def mulUpFromEventFlow : EventFlow → Option MulUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (MulUp.mk
          (mulUpDecodeBHist (mulUpEventAt 1 ef))
          (mulUpDecodeBHist (mulUpEventAt 2 ef))
          (mulUpDecodeBHist (mulUpEventAt 3 ef))
          (mulUpDecodeBHist (mulUpEventAt 4 ef))
          (mulUpDecodeBHist (mulUpEventAt 5 ef))
          (mulUpDecodeBHist (mulUpEventAt 6 ef))
          (mulUpDecodeBHist (mulUpEventAt 7 ef)))

private theorem mulUp_round_trip :
    ∀ x : MulUp, mulUpFromEventFlow (mulUpToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk multiplicand multiplier product additiveLedger recursionLedger provenance
      localNameCert =>
      change
        some
          (MulUp.mk
            (mulUpDecodeBHist (mulUpEncodeBHist multiplicand))
            (mulUpDecodeBHist (mulUpEncodeBHist multiplier))
            (mulUpDecodeBHist (mulUpEncodeBHist product))
            (mulUpDecodeBHist (mulUpEncodeBHist additiveLedger))
            (mulUpDecodeBHist (mulUpEncodeBHist recursionLedger))
            (mulUpDecodeBHist (mulUpEncodeBHist provenance))
            (mulUpDecodeBHist (mulUpEncodeBHist localNameCert))) =
          some
            (MulUp.mk multiplicand multiplier product additiveLedger recursionLedger provenance
              localNameCert)
      rw [mulUpDecode_encode_bhist multiplicand, mulUpDecode_encode_bhist multiplier,
        mulUpDecode_encode_bhist product, mulUpDecode_encode_bhist additiveLedger,
        mulUpDecode_encode_bhist recursionLedger, mulUpDecode_encode_bhist provenance,
        mulUpDecode_encode_bhist localNameCert]

private theorem mulUpToEventFlow_injective {x y : MulUp} :
    mulUpToEventFlow x = mulUpToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mulUpFromEventFlow (mulUpToEventFlow x) =
        mulUpFromEventFlow (mulUpToEventFlow y) :=
    congrArg mulUpFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (mulUp_round_trip x).symm (Eq.trans hread (mulUp_round_trip y)))

private theorem mulUp_fields_faithful :
    ∀ x y : MulUp, mulUpFields x = mulUpFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk multiplicand₁ multiplier₁ product₁ additiveLedger₁ recursionLedger₁ provenance₁
      localNameCert₁ =>
      cases y with
      | mk multiplicand₂ multiplier₂ product₂ additiveLedger₂ recursionLedger₂ provenance₂
          localNameCert₂ =>
          injection h with hmultiplicand rest₁
          injection rest₁ with hmultiplier rest₂
          injection rest₂ with hproduct rest₃
          injection rest₃ with hadditiveLedger rest₄
          injection rest₄ with hrecursionLedger rest₅
          injection rest₅ with hprovenance rest₆
          injection rest₆ with hlocalNameCert _
          cases hmultiplicand
          cases hmultiplier
          cases hproduct
          cases hadditiveLedger
          cases hrecursionLedger
          cases hprovenance
          cases hlocalNameCert
          rfl

instance mulUpBHistCarrier : BHistCarrier MulUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mulUpToEventFlow
  fromEventFlow := mulUpFromEventFlow

instance mulUpChapterTasteGate : ChapterTasteGate MulUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mulUpFromEventFlow (mulUpToEventFlow x) = some x
    exact mulUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (mulUpToEventFlow_injective heq)

instance mulUpFieldFaithful : FieldFaithful MulUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := mulUpFields
  field_faithful := mulUp_fields_faithful

instance mulUpNontrivial : Nontrivial MulUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MulUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MulUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MulUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MulUp) ∧
      Nonempty (FieldFaithful MulUp) ∧
        Nonempty (Nontrivial MulUp) ∧
          (∀ h : BHist, mulUpDecodeBHist (mulUpEncodeBHist h) = h) ∧
            (∀ x : MulUp, mulUpFromEventFlow (mulUpToEventFlow x) = some x) ∧
              (∀ x y : MulUp, mulUpToEventFlow x = mulUpToEventFlow y → x = y) ∧
                mulUpEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro mulUpChapterTasteGate,
      Nonempty.intro mulUpFieldFaithful,
      Nonempty.intro mulUpNontrivial,
      mulUpDecode_encode_bhist,
      mulUp_round_trip,
      by
        intro x y heq
        exact mulUpToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.MulUp.TasteGate
