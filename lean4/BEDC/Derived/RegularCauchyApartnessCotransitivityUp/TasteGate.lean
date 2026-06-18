import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessCotransitivityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyApartnessCotransitivityUp : Type where
  | mk
      (sourceLeft sourceRight thirdName sourceApartness locatedOrder leftBranch rightBranch
        window dyadic readback realSeal transport replay provenance localName : BHist) :
      RegularCauchyApartnessCotransitivityUp
  deriving DecidableEq

private def regularCauchyApartnessCotransitivityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyApartnessCotransitivityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyApartnessCotransitivityEncodeBHist h

private def regularCauchyApartnessCotransitivityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyApartnessCotransitivityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyApartnessCotransitivityDecodeBHist tail)

private theorem regularCauchyApartnessCotransitivityDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyApartnessCotransitivityDecodeBHist
        (regularCauchyApartnessCotransitivityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regularCauchyApartnessCotransitivity_mk_congr
    {sourceLeft₁ sourceRight₁ thirdName₁ sourceApartness₁ locatedOrder₁ leftBranch₁
      rightBranch₁ window₁ dyadic₁ readback₁ realSeal₁ transport₁ replay₁ provenance₁
      localName₁ sourceLeft₂ sourceRight₂ thirdName₂ sourceApartness₂ locatedOrder₂
      leftBranch₂ rightBranch₂ window₂ dyadic₂ readback₂ realSeal₂ transport₂ replay₂
      provenance₂ localName₂ : BHist} :
    sourceLeft₁ = sourceLeft₂ ->
      sourceRight₁ = sourceRight₂ ->
        thirdName₁ = thirdName₂ ->
          sourceApartness₁ = sourceApartness₂ ->
            locatedOrder₁ = locatedOrder₂ ->
              leftBranch₁ = leftBranch₂ ->
                rightBranch₁ = rightBranch₂ ->
                  window₁ = window₂ ->
                    dyadic₁ = dyadic₂ ->
                      readback₁ = readback₂ ->
                        realSeal₁ = realSeal₂ ->
                          transport₁ = transport₂ ->
                            replay₁ = replay₂ ->
                              provenance₁ = provenance₂ ->
                                localName₁ = localName₂ ->
                                  RegularCauchyApartnessCotransitivityUp.mk sourceLeft₁
                                      sourceRight₁ thirdName₁ sourceApartness₁ locatedOrder₁
                                      leftBranch₁ rightBranch₁ window₁ dyadic₁ readback₁ realSeal₁
                                      transport₁ replay₁ provenance₁ localName₁ =
                                    RegularCauchyApartnessCotransitivityUp.mk sourceLeft₂
                                      sourceRight₂ thirdName₂ sourceApartness₂ locatedOrder₂
                                      leftBranch₂ rightBranch₂ window₂ dyadic₂ readback₂ realSeal₂
                                      transport₂ replay₂ provenance₂ localName₂ := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  cases h0
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  cases h7
  cases h8
  cases h9
  cases h10
  cases h11
  cases h12
  cases h13
  cases h14
  rfl

private def regularCauchyApartnessCotransitivityToEventFlow :
    RegularCauchyApartnessCotransitivityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyApartnessCotransitivityUp.mk sourceLeft sourceRight thirdName
      sourceApartness locatedOrder leftBranch rightBranch window dyadic readback realSeal
      transport replay provenance localName =>
      [[BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist sourceLeft,
        [BMark.b1, BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist sourceRight,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist thirdName,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist sourceApartness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist locatedOrder,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist leftBranch,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist rightBranch,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b0],
        regularCauchyApartnessCotransitivityEncodeBHist localName]

private def regularCauchyApartnessCotransitivityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyApartnessCotransitivityEventAt index rest

private def regularCauchyApartnessCotransitivityFromEventFlow :
    EventFlow → Option RegularCauchyApartnessCotransitivityUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RegularCauchyApartnessCotransitivityUp.mk
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 1 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 3 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 5 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 7 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 9 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 11 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 13 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 15 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 17 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 19 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 21 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 23 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 25 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 27 ef))
          (regularCauchyApartnessCotransitivityDecodeBHist
            (regularCauchyApartnessCotransitivityEventAt 29 ef)))

private theorem regularCauchyApartnessCotransitivity_round_trip :
    ∀ x : RegularCauchyApartnessCotransitivityUp,
      regularCauchyApartnessCotransitivityFromEventFlow
        (regularCauchyApartnessCotransitivityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceLeft sourceRight thirdName sourceApartness locatedOrder leftBranch rightBranch
      window dyadic readback realSeal transport replay provenance localName =>
      exact
        congrArg some
          (regularCauchyApartnessCotransitivity_mk_congr
            (regularCauchyApartnessCotransitivityDecode_encode_bhist sourceLeft)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist sourceRight)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist thirdName)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist sourceApartness)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist locatedOrder)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist leftBranch)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist rightBranch)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist window)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist dyadic)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist readback)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist realSeal)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist transport)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist replay)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist provenance)
            (regularCauchyApartnessCotransitivityDecode_encode_bhist localName))

private theorem regularCauchyApartnessCotransitivityToEventFlow_injective
    {x y : RegularCauchyApartnessCotransitivityUp} :
    regularCauchyApartnessCotransitivityToEventFlow x =
      regularCauchyApartnessCotransitivityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyApartnessCotransitivityFromEventFlow
          (regularCauchyApartnessCotransitivityToEventFlow x) =
        regularCauchyApartnessCotransitivityFromEventFlow
          (regularCauchyApartnessCotransitivityToEventFlow y) :=
    congrArg regularCauchyApartnessCotransitivityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyApartnessCotransitivity_round_trip x).symm
      (Eq.trans hread (regularCauchyApartnessCotransitivity_round_trip y)))

def regularCauchyApartnessCotransitivityFields :
    RegularCauchyApartnessCotransitivityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyApartnessCotransitivityUp.mk sourceLeft sourceRight thirdName
      sourceApartness locatedOrder leftBranch rightBranch window dyadic readback realSeal
      transport replay provenance localName =>
      [sourceLeft, sourceRight, thirdName, sourceApartness, locatedOrder, leftBranch,
        rightBranch, window, dyadic, readback, realSeal, transport, replay, provenance,
        localName]

private theorem regularCauchyApartnessCotransitivity_field_faithful :
    ∀ x y : RegularCauchyApartnessCotransitivityUp,
      regularCauchyApartnessCotransitivityFields x =
        regularCauchyApartnessCotransitivityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk sourceLeft₁ sourceRight₁ thirdName₁ sourceApartness₁ locatedOrder₁ leftBranch₁
      rightBranch₁ window₁ dyadic₁ readback₁ realSeal₁ transport₁ replay₁ provenance₁
      localName₁ =>
      cases y with
      | mk sourceLeft₂ sourceRight₂ thirdName₂ sourceApartness₂ locatedOrder₂ leftBranch₂
          rightBranch₂ window₂ dyadic₂ readback₂ realSeal₂ transport₂ replay₂ provenance₂
          localName₂ =>
          cases h
          rfl

instance regularCauchyApartnessCotransitivityBHistCarrier :
    BHistCarrier RegularCauchyApartnessCotransitivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyApartnessCotransitivityToEventFlow
  fromEventFlow := regularCauchyApartnessCotransitivityFromEventFlow

instance regularCauchyApartnessCotransitivityChapterTasteGate :
    ChapterTasteGate RegularCauchyApartnessCotransitivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyApartnessCotransitivityFromEventFlow
          (regularCauchyApartnessCotransitivityToEventFlow x) =
        some x
    exact regularCauchyApartnessCotransitivity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyApartnessCotransitivityToEventFlow_injective heq)

instance regularCauchyApartnessCotransitivityFieldFaithful :
    FieldFaithful RegularCauchyApartnessCotransitivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyApartnessCotransitivityFields
  field_faithful := regularCauchyApartnessCotransitivity_field_faithful

instance regularCauchyApartnessCotransitivityNontrivial :
    Nontrivial RegularCauchyApartnessCotransitivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyApartnessCotransitivityUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RegularCauchyApartnessCotransitivityUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyApartnessCotransitivityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyApartnessCotransitivityChapterTasteGate

theorem RegularCauchyApartnessCotransitivityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyApartnessCotransitivityDecodeBHist
        (regularCauchyApartnessCotransitivityEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyApartnessCotransitivityUp,
        regularCauchyApartnessCotransitivityFromEventFlow
          (regularCauchyApartnessCotransitivityToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyApartnessCotransitivityUp,
          regularCauchyApartnessCotransitivityToEventFlow x =
              regularCauchyApartnessCotransitivityToEventFlow y →
            x = y) ∧
          (∀ x y : RegularCauchyApartnessCotransitivityUp,
            regularCauchyApartnessCotransitivityFields x =
                regularCauchyApartnessCotransitivityFields y →
              x = y) ∧
            ∃ x y : RegularCauchyApartnessCotransitivityUp, x ≠ y := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  refine
    ⟨regularCauchyApartnessCotransitivityDecode_encode_bhist,
      regularCauchyApartnessCotransitivity_round_trip,
      ?injective, regularCauchyApartnessCotransitivity_field_faithful, ?nontrivial⟩
  · intro x y heq
    exact regularCauchyApartnessCotransitivityToEventFlow_injective heq
  · exact
      ⟨RegularCauchyApartnessCotransitivityUp.mk (BHist.e0 BHist.Empty) BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        RegularCauchyApartnessCotransitivityUp.mk BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩

end BEDC.Derived.RegularCauchyApartnessCotransitivityUp
