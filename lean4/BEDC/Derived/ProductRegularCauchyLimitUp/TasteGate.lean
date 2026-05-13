import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProductRegularCauchyLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProductRegularCauchyLimitUp : Type where
  | mk :
      (product classifier windows regular dyadic realSeal history contRoutes provenance
        nameCert : BHist) →
      ProductRegularCauchyLimitUp
  deriving DecidableEq

def productRegularCauchyLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: productRegularCauchyLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: productRegularCauchyLimitEncodeBHist h

def productRegularCauchyLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (productRegularCauchyLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (productRegularCauchyLimitDecodeBHist tail)

private theorem productRegularCauchyLimitDecode_encode_bhist :
    ∀ h : BHist,
      productRegularCauchyLimitDecodeBHist (productRegularCauchyLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem productRegularCauchyLimit_mk_congr
    {product product' classifier classifier' windows windows' regular regular' dyadic dyadic'
      realSeal realSeal' history history' contRoutes contRoutes' provenance provenance'
      nameCert nameCert' : BHist}
    (hProduct : product' = product)
    (hClassifier : classifier' = classifier)
    (hWindows : windows' = windows)
    (hRegular : regular' = regular)
    (hDyadic : dyadic' = dyadic)
    (hRealSeal : realSeal' = realSeal)
    (hHistory : history' = history)
    (hContRoutes : contRoutes' = contRoutes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    ProductRegularCauchyLimitUp.mk product' classifier' windows' regular' dyadic' realSeal'
        history' contRoutes' provenance' nameCert' =
      ProductRegularCauchyLimitUp.mk product classifier windows regular dyadic realSeal history
        contRoutes provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hProduct
  cases hClassifier
  cases hWindows
  cases hRegular
  cases hDyadic
  cases hRealSeal
  cases hHistory
  cases hContRoutes
  cases hProvenance
  cases hNameCert
  rfl

def productRegularCauchyLimitToEventFlow : ProductRegularCauchyLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ProductRegularCauchyLimitUp.mk product classifier windows regular dyadic realSeal history
      contRoutes provenance nameCert =>
      [[BMark.b0],
        productRegularCauchyLimitEncodeBHist product,
        [BMark.b1, BMark.b0],
        productRegularCauchyLimitEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b0],
        productRegularCauchyLimitEncodeBHist windows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        productRegularCauchyLimitEncodeBHist regular,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        productRegularCauchyLimitEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        productRegularCauchyLimitEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        productRegularCauchyLimitEncodeBHist history,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        productRegularCauchyLimitEncodeBHist contRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        productRegularCauchyLimitEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        productRegularCauchyLimitEncodeBHist nameCert]

def productRegularCauchyLimitFromEventFlow :
    EventFlow → Option ProductRegularCauchyLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | product :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | classifier :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | windows :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | regular :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | dyadic :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | realSeal :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | history :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | contRoutes :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | nameCert :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (ProductRegularCauchyLimitUp.mk
                                                                                          (productRegularCauchyLimitDecodeBHist
                                                                                            product)
                                                                                          (productRegularCauchyLimitDecodeBHist
                                                                                            classifier)
                                                                                          (productRegularCauchyLimitDecodeBHist
                                                                                            windows)
                                                                                          (productRegularCauchyLimitDecodeBHist
                                                                                            regular)
                                                                                          (productRegularCauchyLimitDecodeBHist
                                                                                            dyadic)
                                                                                          (productRegularCauchyLimitDecodeBHist
                                                                                            realSeal)
                                                                                          (productRegularCauchyLimitDecodeBHist
                                                                                            history)
                                                                                          (productRegularCauchyLimitDecodeBHist
                                                                                            contRoutes)
                                                                                          (productRegularCauchyLimitDecodeBHist
                                                                                            provenance)
                                                                                          (productRegularCauchyLimitDecodeBHist
                                                                                            nameCert))
                                                                                  | _ :: _ => none

private theorem productRegularCauchyLimit_round_trip :
    ∀ x : ProductRegularCauchyLimitUp,
      productRegularCauchyLimitFromEventFlow (productRegularCauchyLimitToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk product classifier windows regular dyadic realSeal history contRoutes provenance
      nameCert =>
      change
        some
          (ProductRegularCauchyLimitUp.mk
            (productRegularCauchyLimitDecodeBHist
              (productRegularCauchyLimitEncodeBHist product))
            (productRegularCauchyLimitDecodeBHist
              (productRegularCauchyLimitEncodeBHist classifier))
            (productRegularCauchyLimitDecodeBHist
              (productRegularCauchyLimitEncodeBHist windows))
            (productRegularCauchyLimitDecodeBHist
              (productRegularCauchyLimitEncodeBHist regular))
            (productRegularCauchyLimitDecodeBHist
              (productRegularCauchyLimitEncodeBHist dyadic))
            (productRegularCauchyLimitDecodeBHist
              (productRegularCauchyLimitEncodeBHist realSeal))
            (productRegularCauchyLimitDecodeBHist
              (productRegularCauchyLimitEncodeBHist history))
            (productRegularCauchyLimitDecodeBHist
              (productRegularCauchyLimitEncodeBHist contRoutes))
            (productRegularCauchyLimitDecodeBHist
              (productRegularCauchyLimitEncodeBHist provenance))
            (productRegularCauchyLimitDecodeBHist
              (productRegularCauchyLimitEncodeBHist nameCert))) =
          some
            (ProductRegularCauchyLimitUp.mk product classifier windows regular dyadic realSeal
              history contRoutes provenance nameCert)
      exact
        congrArg some
          (productRegularCauchyLimit_mk_congr
            (productRegularCauchyLimitDecode_encode_bhist product)
            (productRegularCauchyLimitDecode_encode_bhist classifier)
            (productRegularCauchyLimitDecode_encode_bhist windows)
            (productRegularCauchyLimitDecode_encode_bhist regular)
            (productRegularCauchyLimitDecode_encode_bhist dyadic)
            (productRegularCauchyLimitDecode_encode_bhist realSeal)
            (productRegularCauchyLimitDecode_encode_bhist history)
            (productRegularCauchyLimitDecode_encode_bhist contRoutes)
            (productRegularCauchyLimitDecode_encode_bhist provenance)
            (productRegularCauchyLimitDecode_encode_bhist nameCert))

private theorem productRegularCauchyLimitToEventFlow_injective
    {x y : ProductRegularCauchyLimitUp} :
    productRegularCauchyLimitToEventFlow x = productRegularCauchyLimitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      productRegularCauchyLimitFromEventFlow (productRegularCauchyLimitToEventFlow x) =
        productRegularCauchyLimitFromEventFlow (productRegularCauchyLimitToEventFlow y) :=
    congrArg productRegularCauchyLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (productRegularCauchyLimit_round_trip x).symm
      (Eq.trans hread (productRegularCauchyLimit_round_trip y)))

instance productRegularCauchyLimitBHistCarrier :
    BHistCarrier ProductRegularCauchyLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := productRegularCauchyLimitToEventFlow
  fromEventFlow := productRegularCauchyLimitFromEventFlow

instance productRegularCauchyLimitChapterTasteGate :
    ChapterTasteGate ProductRegularCauchyLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change productRegularCauchyLimitFromEventFlow
        (productRegularCauchyLimitToEventFlow x) = some x
    exact productRegularCauchyLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (productRegularCauchyLimitToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ProductRegularCauchyLimitUp :=
  inferInstance

theorem ProductRegularCauchyLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      productRegularCauchyLimitDecodeBHist (productRegularCauchyLimitEncodeBHist h) = h) ∧
      (∀ x : ProductRegularCauchyLimitUp,
        productRegularCauchyLimitFromEventFlow
          (productRegularCauchyLimitToEventFlow x) = some x) ∧
        (∀ x y : ProductRegularCauchyLimitUp,
          productRegularCauchyLimitToEventFlow x =
            productRegularCauchyLimitToEventFlow y → x = y) ∧
          (∀ (x : ProductRegularCauchyLimitUp) w m,
            List.Mem w (productRegularCauchyLimitToEventFlow x) → List.Mem m w →
              m = BMark.b0 ∨ m = BMark.b1) ∧
            productRegularCauchyLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact productRegularCauchyLimitDecode_encode_bhist
  · constructor
    · exact productRegularCauchyLimit_round_trip
    · constructor
      · intro x y heq
        exact productRegularCauchyLimitToEventFlow_injective heq
      · constructor
        · intro x w m hw hm
          cases m with
          | b0 =>
              exact Or.inl rfl
          | b1 =>
              exact Or.inr rfl
        · rfl

end BEDC.Derived.ProductRegularCauchyLimitUp
