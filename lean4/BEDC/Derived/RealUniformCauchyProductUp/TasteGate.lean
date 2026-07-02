import BEDC.Derived.RealUniformCauchyProductUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformCauchyProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def realUniformCauchyProductEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realUniformCauchyProductEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realUniformCauchyProductEncodeBHist h

def realUniformCauchyProductDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realUniformCauchyProductDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realUniformCauchyProductDecodeBHist tail)

private theorem realUniformCauchyProductDecode_encode :
    ∀ h : BHist,
      realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realUniformCauchyProductFields : RealUniformCauchyProductUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformCauchyProductUp.mk F G M WF WG D U K R E H C Q N =>
      [F, G, M, WF, WG, D, U, K, R, E, H, C, Q, N]

def realUniformCauchyProductToEventFlow : RealUniformCauchyProductUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realUniformCauchyProductFields x).map realUniformCauchyProductEncodeBHist

noncomputable def realUniformCauchyProductFromEventFlow :
    EventFlow → Option RealUniformCauchyProductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    List.rec none
      (fun F restF _ =>
        List.rec none
          (fun G restG _ =>
            List.rec none
              (fun M restM _ =>
                List.rec none
                  (fun WF restWF _ =>
                    List.rec none
                      (fun WG restWG _ =>
                        List.rec none
                          (fun D restD _ =>
                            List.rec none
                              (fun U restU _ =>
                                List.rec none
                                  (fun K restK _ =>
                                    List.rec none
                                      (fun R restR _ =>
                                        List.rec none
                                          (fun E restE _ =>
                                            List.rec none
                                              (fun H restH _ =>
                                                List.rec none
                                                  (fun C restC _ =>
                                                    List.rec none
                                                      (fun Q restQ _ =>
                                                        List.rec none
                                                          (fun N restN _ =>
                                                            List.rec
                                                              (some
                                                                (RealUniformCauchyProductUp.mk
                                                                  (realUniformCauchyProductDecodeBHist F)
                                                                  (realUniformCauchyProductDecodeBHist G)
                                                                  (realUniformCauchyProductDecodeBHist M)
                                                                  (realUniformCauchyProductDecodeBHist WF)
                                                                  (realUniformCauchyProductDecodeBHist WG)
                                                                  (realUniformCauchyProductDecodeBHist D)
                                                                  (realUniformCauchyProductDecodeBHist U)
                                                                  (realUniformCauchyProductDecodeBHist K)
                                                                  (realUniformCauchyProductDecodeBHist R)
                                                                  (realUniformCauchyProductDecodeBHist E)
                                                                  (realUniformCauchyProductDecodeBHist H)
                                                                  (realUniformCauchyProductDecodeBHist C)
                                                                  (realUniformCauchyProductDecodeBHist Q)
                                                                  (realUniformCauchyProductDecodeBHist N)))
                                                              (fun _ _ _ => none) restN)
                                                          restQ)
                                                      restC)
                                                  restH)
                                              restE)
                                          restR)
                                      restK)
                                  restU)
                              restD)
                          restWG)
                      restWF)
                  restM)
              restG)
          restF)
      flow

private theorem realUniformCauchyProduct_round_trip :
    ∀ x : RealUniformCauchyProductUp,
      realUniformCauchyProductFromEventFlow (realUniformCauchyProductToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F G M WF WG D U K R E H C Q N =>
      change
        some
          (RealUniformCauchyProductUp.mk
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist F))
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist G))
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist M))
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist WF))
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist WG))
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist D))
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist U))
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist K))
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist R))
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist E))
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist H))
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist C))
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist Q))
            (realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist N))) =
          some (RealUniformCauchyProductUp.mk F G M WF WG D U K R E H C Q N)
      rw [realUniformCauchyProductDecode_encode F, realUniformCauchyProductDecode_encode G,
        realUniformCauchyProductDecode_encode M, realUniformCauchyProductDecode_encode WF,
        realUniformCauchyProductDecode_encode WG, realUniformCauchyProductDecode_encode D,
        realUniformCauchyProductDecode_encode U, realUniformCauchyProductDecode_encode K,
        realUniformCauchyProductDecode_encode R, realUniformCauchyProductDecode_encode E,
        realUniformCauchyProductDecode_encode H, realUniformCauchyProductDecode_encode C,
        realUniformCauchyProductDecode_encode Q, realUniformCauchyProductDecode_encode N]

private theorem realUniformCauchyProductToEventFlow_injective
    {x y : RealUniformCauchyProductUp} :
    realUniformCauchyProductToEventFlow x = realUniformCauchyProductToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = realUniformCauchyProductFromEventFlow (realUniformCauchyProductToEventFlow x) :=
        (realUniformCauchyProduct_round_trip x).symm
      _ = realUniformCauchyProductFromEventFlow (realUniformCauchyProductToEventFlow y) :=
        congrArg realUniformCauchyProductFromEventFlow hxy
      _ = some y := realUniformCauchyProduct_round_trip y
  exact Option.some.inj optionEq

noncomputable instance realUniformCauchyProductBHistCarrier :
    BHistCarrier RealUniformCauchyProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realUniformCauchyProductToEventFlow
  fromEventFlow := realUniformCauchyProductFromEventFlow

noncomputable instance realUniformCauchyProductChapterTasteGate :
    ChapterTasteGate RealUniformCauchyProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realUniformCauchyProductFromEventFlow (realUniformCauchyProductToEventFlow x) =
      some x
    exact realUniformCauchyProduct_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realUniformCauchyProductToEventFlow_injective heq)

instance realUniformCauchyProductNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RealUniformCauchyProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair := by
    refine ⟨RealUniformCauchyProductUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RealUniformCauchyProductUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty, ?_⟩
    intro h
    cases h

theorem RealUniformCauchyProductTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realUniformCauchyProductDecodeBHist (realUniformCauchyProductEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealUniformCauchyProductUp) ∧
        Nonempty (ChapterTasteGate RealUniformCauchyProductUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial RealUniformCauchyProductUp) ∧
            realUniformCauchyProductEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨realUniformCauchyProductDecode_encode,
      ⟨realUniformCauchyProductBHistCarrier⟩,
      ⟨realUniformCauchyProductChapterTasteGate⟩,
      ⟨realUniformCauchyProductNontrivial⟩,
      rfl⟩

end BEDC.Derived.RealUniformCauchyProductUp
