import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CayleyHamiltonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CayleyHamiltonUp : Type where
  | mk
      (coefficientSource squareSize matrixRow characteristicPolynomial evaluationRow
        zeroComparison transport replay provenance localNameCert : BHist) :
      CayleyHamiltonUp
  deriving DecidableEq

def cayleyHamiltonTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0, BMark.b0]

def cayleyHamiltonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cayleyHamiltonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cayleyHamiltonEncodeBHist h

def cayleyHamiltonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cayleyHamiltonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cayleyHamiltonDecodeBHist tail)

private theorem cayleyHamiltonDecodeEncode :
    ∀ h : BHist, cayleyHamiltonDecodeBHist (cayleyHamiltonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cayleyHamiltonFields : CayleyHamiltonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CayleyHamiltonUp.mk coefficientSource squareSize matrixRow characteristicPolynomial
      evaluationRow zeroComparison transport replay provenance localNameCert =>
      [coefficientSource, squareSize, matrixRow, characteristicPolynomial, evaluationRow,
        zeroComparison, transport, replay, provenance, localNameCert]

def cayleyHamiltonToEventFlow : CayleyHamiltonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CayleyHamiltonUp.mk coefficientSource squareSize matrixRow characteristicPolynomial
      evaluationRow zeroComparison transport replay provenance localNameCert =>
      [cayleyHamiltonTag,
        cayleyHamiltonEncodeBHist coefficientSource,
        cayleyHamiltonEncodeBHist squareSize,
        cayleyHamiltonEncodeBHist matrixRow,
        cayleyHamiltonEncodeBHist characteristicPolynomial,
        cayleyHamiltonEncodeBHist evaluationRow,
        cayleyHamiltonEncodeBHist zeroComparison,
        cayleyHamiltonEncodeBHist transport,
        cayleyHamiltonEncodeBHist replay,
        cayleyHamiltonEncodeBHist provenance,
        cayleyHamiltonEncodeBHist localNameCert]

private def cayleyHamiltonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cayleyHamiltonEventAtDefault index rest

def cayleyHamiltonFromEventFlow : EventFlow → Option CayleyHamiltonUp := fun ef =>
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CayleyHamiltonUp.mk
      (cayleyHamiltonDecodeBHist (cayleyHamiltonEventAtDefault 1 ef))
      (cayleyHamiltonDecodeBHist (cayleyHamiltonEventAtDefault 2 ef))
      (cayleyHamiltonDecodeBHist (cayleyHamiltonEventAtDefault 3 ef))
      (cayleyHamiltonDecodeBHist (cayleyHamiltonEventAtDefault 4 ef))
      (cayleyHamiltonDecodeBHist (cayleyHamiltonEventAtDefault 5 ef))
      (cayleyHamiltonDecodeBHist (cayleyHamiltonEventAtDefault 6 ef))
      (cayleyHamiltonDecodeBHist (cayleyHamiltonEventAtDefault 7 ef))
      (cayleyHamiltonDecodeBHist (cayleyHamiltonEventAtDefault 8 ef))
      (cayleyHamiltonDecodeBHist (cayleyHamiltonEventAtDefault 9 ef))
      (cayleyHamiltonDecodeBHist (cayleyHamiltonEventAtDefault 10 ef)))

private theorem cayleyHamiltonRoundTrip :
    ∀ x : CayleyHamiltonUp, cayleyHamiltonFromEventFlow (cayleyHamiltonToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk coefficientSource squareSize matrixRow characteristicPolynomial evaluationRow
      zeroComparison transport replay provenance localNameCert =>
      change
        some
          (CayleyHamiltonUp.mk
            (cayleyHamiltonDecodeBHist (cayleyHamiltonEncodeBHist coefficientSource))
            (cayleyHamiltonDecodeBHist (cayleyHamiltonEncodeBHist squareSize))
            (cayleyHamiltonDecodeBHist (cayleyHamiltonEncodeBHist matrixRow))
            (cayleyHamiltonDecodeBHist (cayleyHamiltonEncodeBHist characteristicPolynomial))
            (cayleyHamiltonDecodeBHist (cayleyHamiltonEncodeBHist evaluationRow))
            (cayleyHamiltonDecodeBHist (cayleyHamiltonEncodeBHist zeroComparison))
            (cayleyHamiltonDecodeBHist (cayleyHamiltonEncodeBHist transport))
            (cayleyHamiltonDecodeBHist (cayleyHamiltonEncodeBHist replay))
            (cayleyHamiltonDecodeBHist (cayleyHamiltonEncodeBHist provenance))
            (cayleyHamiltonDecodeBHist (cayleyHamiltonEncodeBHist localNameCert))) =
          some
            (CayleyHamiltonUp.mk coefficientSource squareSize matrixRow
              characteristicPolynomial evaluationRow zeroComparison transport replay provenance
              localNameCert)
      rw [cayleyHamiltonDecodeEncode coefficientSource,
        cayleyHamiltonDecodeEncode squareSize,
        cayleyHamiltonDecodeEncode matrixRow,
        cayleyHamiltonDecodeEncode characteristicPolynomial,
        cayleyHamiltonDecodeEncode evaluationRow,
        cayleyHamiltonDecodeEncode zeroComparison,
        cayleyHamiltonDecodeEncode transport,
        cayleyHamiltonDecodeEncode replay,
        cayleyHamiltonDecodeEncode provenance,
        cayleyHamiltonDecodeEncode localNameCert]

private theorem cayleyHamiltonToEventFlow_injective {x y : CayleyHamiltonUp} :
    cayleyHamiltonToEventFlow x = cayleyHamiltonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cayleyHamiltonFromEventFlow (cayleyHamiltonToEventFlow x) =
        cayleyHamiltonFromEventFlow (cayleyHamiltonToEventFlow y) :=
    congrArg cayleyHamiltonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (cayleyHamiltonRoundTrip x).symm
      (Eq.trans hread (cayleyHamiltonRoundTrip y)))

private theorem cayleyHamiltonFieldFaithfulProof :
    ∀ x y : CayleyHamiltonUp, cayleyHamiltonFields x = cayleyHamiltonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk coefficientSource1 squareSize1 matrixRow1 characteristicPolynomial1 evaluationRow1
      zeroComparison1 transport1 replay1 provenance1 localNameCert1 =>
      cases y with
      | mk coefficientSource2 squareSize2 matrixRow2 characteristicPolynomial2 evaluationRow2
          zeroComparison2 transport2 replay2 provenance2 localNameCert2 =>
          cases hfields
          rfl

instance cayleyHamiltonBHistCarrier : BHistCarrier CayleyHamiltonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cayleyHamiltonToEventFlow
  fromEventFlow := cayleyHamiltonFromEventFlow

instance cayleyHamiltonChapterTasteGate : ChapterTasteGate CayleyHamiltonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cayleyHamiltonFromEventFlow (cayleyHamiltonToEventFlow x) = some x
    exact cayleyHamiltonRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cayleyHamiltonToEventFlow_injective heq)

instance cayleyHamiltonFieldFaithful : FieldFaithful CayleyHamiltonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cayleyHamiltonFields
  field_faithful := cayleyHamiltonFieldFaithfulProof

instance cayleyHamiltonNontrivial : Nontrivial CayleyHamiltonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CayleyHamiltonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CayleyHamiltonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CayleyHamiltonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cayleyHamiltonChapterTasteGate

theorem CayleyHamiltonTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CayleyHamiltonUp) ∧
      Nonempty (FieldFaithful CayleyHamiltonUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CayleyHamiltonUp) ∧
          (∀ h : BHist, cayleyHamiltonDecodeBHist (cayleyHamiltonEncodeBHist h) = h) ∧
            (∀ x : CayleyHamiltonUp,
              cayleyHamiltonFromEventFlow (cayleyHamiltonToEventFlow x) = some x) ∧
              (∀ x y : CayleyHamiltonUp,
                cayleyHamiltonToEventFlow x = cayleyHamiltonToEventFlow y → x = y) ∧
                cayleyHamiltonEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro cayleyHamiltonChapterTasteGate,
      Nonempty.intro cayleyHamiltonFieldFaithful,
      Nonempty.intro cayleyHamiltonNontrivial,
      cayleyHamiltonDecodeEncode,
      cayleyHamiltonRoundTrip,
      (fun _ _ heq => cayleyHamiltonToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CayleyHamiltonUp
