import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySealBudgetSynchronizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySealBudgetSynchronizerUp : Type where
  | mk :
      (request sealRow budget tail selector compatibility transport route provenance nameCert :
        BHist) →
      CauchySealBudgetSynchronizerUp
  deriving DecidableEq

def cauchySealBudgetSynchronizerEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySealBudgetSynchronizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySealBudgetSynchronizerEncodeBHist h

def cauchySealBudgetSynchronizerDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySealBudgetSynchronizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySealBudgetSynchronizerDecodeBHist tail)

private theorem cauchySealBudgetSynchronizerDecode_encode_bhist :
    ∀ h : BHist,
      cauchySealBudgetSynchronizerDecodeBHist
        (cauchySealBudgetSynchronizerEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchySealBudgetSynchronizerToEventFlow :
    CauchySealBudgetSynchronizerUp → EventFlow
  | CauchySealBudgetSynchronizerUp.mk request sealRow budget tail selector compatibility
      transport route provenance nameCert =>
      [[BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist request,
        [BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist tail,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist selector,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist compatibility,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist nameCert]

private def cauchySealBudgetSynchronizerRawAt : Nat → EventFlow → RawEvent
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cauchySealBudgetSynchronizerRawAt n rest

private def cauchySealBudgetSynchronizerLengthEq : Nat → EventFlow → Bool
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cauchySealBudgetSynchronizerLengthEq n rest

def cauchySealBudgetSynchronizerFromEventFlow :
    EventFlow → Option CauchySealBudgetSynchronizerUp
  | flow =>
      match cauchySealBudgetSynchronizerLengthEq 20 flow with
      | true =>
      some
        (CauchySealBudgetSynchronizerUp.mk
          (cauchySealBudgetSynchronizerDecodeBHist
            (cauchySealBudgetSynchronizerRawAt 1 flow))
          (cauchySealBudgetSynchronizerDecodeBHist
            (cauchySealBudgetSynchronizerRawAt 3 flow))
          (cauchySealBudgetSynchronizerDecodeBHist
            (cauchySealBudgetSynchronizerRawAt 5 flow))
          (cauchySealBudgetSynchronizerDecodeBHist
            (cauchySealBudgetSynchronizerRawAt 7 flow))
          (cauchySealBudgetSynchronizerDecodeBHist
            (cauchySealBudgetSynchronizerRawAt 9 flow))
          (cauchySealBudgetSynchronizerDecodeBHist
            (cauchySealBudgetSynchronizerRawAt 11 flow))
          (cauchySealBudgetSynchronizerDecodeBHist
            (cauchySealBudgetSynchronizerRawAt 13 flow))
          (cauchySealBudgetSynchronizerDecodeBHist
            (cauchySealBudgetSynchronizerRawAt 15 flow))
          (cauchySealBudgetSynchronizerDecodeBHist
            (cauchySealBudgetSynchronizerRawAt 17 flow))
          (cauchySealBudgetSynchronizerDecodeBHist
            (cauchySealBudgetSynchronizerRawAt 19 flow)))
      | false => none

private theorem cauchySealBudgetSynchronizer_round_trip :
    ∀ x : CauchySealBudgetSynchronizerUp,
      cauchySealBudgetSynchronizerFromEventFlow
        (cauchySealBudgetSynchronizerToEventFlow x) = some x := by
  intro x
  cases x with
  | mk request sealRow budget tail selector compatibility transport route provenance nameCert =>
      change
        some
          (CauchySealBudgetSynchronizerUp.mk
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist request))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist sealRow))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist budget))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist tail))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist selector))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist compatibility))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist transport))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist route))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist provenance))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist nameCert))) =
          some
            (CauchySealBudgetSynchronizerUp.mk request sealRow budget tail selector
              compatibility transport route provenance nameCert)
      let mkCongr
          {request' sealRow' budget' tail' selector' compatibility' transport' route'
            provenance' nameCert' : BHist}
          (hRequest : request' = request)
          (hSealRow : sealRow' = sealRow)
          (hBudget : budget' = budget)
          (hTail : tail' = tail)
          (hSelector : selector' = selector)
          (hCompatibility : compatibility' = compatibility)
          (hTransport : transport' = transport)
          (hRoute : route' = route)
          (hProvenance : provenance' = provenance)
          (hNameCert : nameCert' = nameCert) :
          CauchySealBudgetSynchronizerUp.mk request' sealRow' budget' tail' selector'
              compatibility' transport' route' provenance' nameCert' =
            CauchySealBudgetSynchronizerUp.mk request sealRow budget tail selector
              compatibility transport route provenance nameCert := by
        cases hRequest
        cases hSealRow
        cases hBudget
        cases hTail
        cases hSelector
        cases hCompatibility
        cases hTransport
        cases hRoute
        cases hProvenance
        cases hNameCert
        rfl
      exact
        congrArg some
          (mkCongr
            (cauchySealBudgetSynchronizerDecode_encode_bhist request)
            (cauchySealBudgetSynchronizerDecode_encode_bhist sealRow)
            (cauchySealBudgetSynchronizerDecode_encode_bhist budget)
            (cauchySealBudgetSynchronizerDecode_encode_bhist tail)
            (cauchySealBudgetSynchronizerDecode_encode_bhist selector)
            (cauchySealBudgetSynchronizerDecode_encode_bhist compatibility)
            (cauchySealBudgetSynchronizerDecode_encode_bhist transport)
            (cauchySealBudgetSynchronizerDecode_encode_bhist route)
            (cauchySealBudgetSynchronizerDecode_encode_bhist provenance)
            (cauchySealBudgetSynchronizerDecode_encode_bhist nameCert))

private theorem cauchySealBudgetSynchronizerToEventFlow_injective
    {x y : CauchySealBudgetSynchronizerUp} :
    cauchySealBudgetSynchronizerToEventFlow x =
      cauchySealBudgetSynchronizerToEventFlow y → x = y := by
  intro heq
  have hread :
      cauchySealBudgetSynchronizerFromEventFlow
          (cauchySealBudgetSynchronizerToEventFlow x) =
        cauchySealBudgetSynchronizerFromEventFlow
          (cauchySealBudgetSynchronizerToEventFlow y) :=
    congrArg cauchySealBudgetSynchronizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySealBudgetSynchronizer_round_trip x).symm
      (Eq.trans hread (cauchySealBudgetSynchronizer_round_trip y)))

instance cauchySealBudgetSynchronizerBHistCarrier :
    BHistCarrier CauchySealBudgetSynchronizerUp where
  toEventFlow := cauchySealBudgetSynchronizerToEventFlow
  fromEventFlow := cauchySealBudgetSynchronizerFromEventFlow

instance cauchySealBudgetSynchronizerChapterTasteGate :
    ChapterTasteGate CauchySealBudgetSynchronizerUp where
  round_trip := by
    intro x
    change
      cauchySealBudgetSynchronizerFromEventFlow
          (cauchySealBudgetSynchronizerToEventFlow x) =
        some x
    exact cauchySealBudgetSynchronizer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySealBudgetSynchronizerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchySealBudgetSynchronizerUp :=
  cauchySealBudgetSynchronizerChapterTasteGate

private def cauchySealBudgetSynchronizer_nontrivial_witness :
    Σ' (x : CauchySealBudgetSynchronizerUp) (y : CauchySealBudgetSynchronizerUp),
      x ≠ y :=
  ⟨CauchySealBudgetSynchronizerUp.mk BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty,
    CauchySealBudgetSynchronizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty,
    by
      intro h
      cases h⟩

private theorem cauchySealBudgetSynchronizer_nontrivial_concrete :
    ∃ x y : CauchySealBudgetSynchronizerUp, x ≠ y :=
  ⟨cauchySealBudgetSynchronizer_nontrivial_witness.1,
    cauchySealBudgetSynchronizer_nontrivial_witness.2.1,
    cauchySealBudgetSynchronizer_nontrivial_witness.2.2⟩

instance cauchySealBudgetSynchronizerNontrivial :
    Nontrivial CauchySealBudgetSynchronizerUp where
  witness_pair := cauchySealBudgetSynchronizer_nontrivial_witness

def cauchySealBudgetSynchronizerFields :
    CauchySealBudgetSynchronizerUp → List BHist
  | CauchySealBudgetSynchronizerUp.mk request sealRow budget tail selector compatibility
      transport route provenance nameCert =>
      [request, sealRow, budget, tail, selector, compatibility, transport, route, provenance,
        nameCert]

private theorem cauchySealBudgetSynchronizer_field_faithful_concrete :
    ∀ x y : CauchySealBudgetSynchronizerUp,
      cauchySealBudgetSynchronizerFields x =
        cauchySealBudgetSynchronizerFields y → x = y := by
  intro x y hfields
  cases x with
  | mk request sealRow budget tail selector compatibility transport route provenance nameCert =>
      cases y with
      | mk request' sealRow' budget' tail' selector' compatibility' transport route'
          provenance' nameCert' =>
          injection hfields with hRequest hTail0
          injection hTail0 with hSealRow hTail1
          injection hTail1 with hBudget hTail2
          injection hTail2 with hTail hTail3
          injection hTail3 with hSelector hTail4
          injection hTail4 with hCompatibility hTail5
          injection hTail5 with hTransport hTail6
          injection hTail6 with hRoute hTail7
          injection hTail7 with hProvenance hTail8
          injection hTail8 with hNameCert _hNil
          cases hRequest
          cases hSealRow
          cases hBudget
          cases hTail
          cases hSelector
          cases hCompatibility
          cases hTransport
          cases hRoute
          cases hProvenance
          cases hNameCert
          rfl

instance cauchySealBudgetSynchronizerFieldFaithful :
    FieldFaithful CauchySealBudgetSynchronizerUp where
  fields := cauchySealBudgetSynchronizerFields
  field_faithful := cauchySealBudgetSynchronizer_field_faithful_concrete

instance cauchySealBudgetSynchronizerStructurallyAtomic :
    StructurallyAtomic CauchySealBudgetSynchronizerUp where
  nearest_siblings :=
    ["CauchyLimitSealUp", "CauchyDiagonalBudgetUp", "RealObservationBudgetUp",
      "TailCofinalityScheduleUp", "DiagonalTailSelectorUp"]
  not_reducible_witness :=
    "joint compatibility row ties selector, budget, shared threshold, and sealRow rows"

theorem CauchySealBudgetSynchronizerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchySealBudgetSynchronizerDecodeBHist
        (cauchySealBudgetSynchronizerEncodeBHist h) = h) ∧
      (∀ x : CauchySealBudgetSynchronizerUp,
        cauchySealBudgetSynchronizerFromEventFlow
          (cauchySealBudgetSynchronizerToEventFlow x) = some x) ∧
        (∀ x y : CauchySealBudgetSynchronizerUp,
          cauchySealBudgetSynchronizerToEventFlow x =
            cauchySealBudgetSynchronizerToEventFlow y → x = y) ∧
          (∀ x y : CauchySealBudgetSynchronizerUp,
            cauchySealBudgetSynchronizerFields x =
              cauchySealBudgetSynchronizerFields y → x = y) ∧
            (∃ x y : CauchySealBudgetSynchronizerUp, x ≠ y) := by
  constructor
  · exact cauchySealBudgetSynchronizerDecode_encode_bhist
  · constructor
    · exact cauchySealBudgetSynchronizer_round_trip
    · constructor
      · intro x y heq
        exact cauchySealBudgetSynchronizerToEventFlow_injective heq
      · constructor
        · exact cauchySealBudgetSynchronizer_field_faithful_concrete
        · exact cauchySealBudgetSynchronizer_nontrivial_concrete

end BEDC.Derived.CauchySealBudgetSynchronizerUp
