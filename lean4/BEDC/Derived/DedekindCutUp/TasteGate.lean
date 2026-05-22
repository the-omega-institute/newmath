import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindCutUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindCutUp : Type where
  | mk :
      (lower upper inhabited rounded located disjoint embedding transport routes provenance
        nameCert : BHist) →
        DedekindCutUp
  deriving DecidableEq

def dedekindCutEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindCutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindCutEncodeBHist h

def dedekindCutDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindCutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindCutDecodeBHist tail)

private theorem DedekindCutTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, dedekindCutDecodeBHist (dedekindCutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dedekindCutFields : DedekindCutUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindCutUp.mk lower upper inhabited rounded located disjoint embedding transport routes
      provenance nameCert =>
        [lower, upper, inhabited, rounded, located, disjoint, embedding, transport, routes,
          provenance, nameCert]

def dedekindCutToEventFlow : DedekindCutUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dedekindCutFields x).map dedekindCutEncodeBHist

def dedekindCutFromEventFlow : EventFlow → Option DedekindCutUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | lower :: restLower =>
      match restLower with
      | upper :: restUpper =>
          match restUpper with
          | inhabited :: restInhabited =>
              match restInhabited with
              | rounded :: restRounded =>
                  match restRounded with
                  | located :: restLocated =>
                      match restLocated with
                      | disjoint :: restDisjoint =>
                          match restDisjoint with
                          | embedding :: restEmbedding =>
                              match restEmbedding with
                              | transport :: restTransport =>
                                  match restTransport with
                                  | routes :: restRoutes =>
                                      match restRoutes with
                                      | provenance :: restProvenance =>
                                          match restProvenance with
                                          | nameCert :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (DedekindCutUp.mk
                                                      (dedekindCutDecodeBHist lower)
                                                      (dedekindCutDecodeBHist upper)
                                                      (dedekindCutDecodeBHist inhabited)
                                                      (dedekindCutDecodeBHist rounded)
                                                      (dedekindCutDecodeBHist located)
                                                      (dedekindCutDecodeBHist disjoint)
                                                      (dedekindCutDecodeBHist embedding)
                                                      (dedekindCutDecodeBHist transport)
                                                      (dedekindCutDecodeBHist routes)
                                                      (dedekindCutDecodeBHist provenance)
                                                      (dedekindCutDecodeBHist nameCert))
                                              | _ :: _ => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none

private theorem dedekindCut_mk_congr
    {L L' U U' I I' R R' O O' E E' Q Q' H H' T T' P P' N N' : BHist}
    (hL : L' = L) (hU : U' = U) (hI : I' = I) (hR : R' = R) (hO : O' = O)
    (hE : E' = E) (hQ : Q' = Q) (hH : H' = H) (hT : T' = T)
    (hP : P' = P) (hN : N' = N) :
    DedekindCutUp.mk L' U' I' R' O' E' Q' H' T' P' N' =
      DedekindCutUp.mk L U I R O E Q H T P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hL
  cases hU
  cases hI
  cases hR
  cases hO
  cases hE
  cases hQ
  cases hH
  cases hT
  cases hP
  cases hN
  rfl

private theorem DedekindCutTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DedekindCutUp, dedekindCutFromEventFlow (dedekindCutToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk lower upper inhabited rounded located disjoint embedding transport routes provenance
      nameCert =>
        exact
          congrArg some
            (dedekindCut_mk_congr
              (DedekindCutTasteGate_single_carrier_alignment_decode lower)
              (DedekindCutTasteGate_single_carrier_alignment_decode upper)
              (DedekindCutTasteGate_single_carrier_alignment_decode inhabited)
              (DedekindCutTasteGate_single_carrier_alignment_decode rounded)
              (DedekindCutTasteGate_single_carrier_alignment_decode located)
              (DedekindCutTasteGate_single_carrier_alignment_decode disjoint)
              (DedekindCutTasteGate_single_carrier_alignment_decode embedding)
              (DedekindCutTasteGate_single_carrier_alignment_decode transport)
              (DedekindCutTasteGate_single_carrier_alignment_decode routes)
              (DedekindCutTasteGate_single_carrier_alignment_decode provenance)
              (DedekindCutTasteGate_single_carrier_alignment_decode nameCert))

private theorem dedekindCutToEventFlow_injective {x y : DedekindCutUp} :
    dedekindCutToEventFlow x = dedekindCutToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindCutFromEventFlow (dedekindCutToEventFlow x) =
        dedekindCutFromEventFlow (dedekindCutToEventFlow y) :=
    congrArg dedekindCutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DedekindCutTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DedekindCutTasteGate_single_carrier_alignment_round_trip y)))

private theorem dedekindCut_field_faithful :
    ∀ x y : DedekindCutUp, dedekindCutFields x = dedekindCutFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk lower upper inhabited rounded located disjoint embedding transport routes provenance
      nameCert =>
        cases y with
        | mk lower' upper' inhabited' rounded' located' disjoint' embedding' transport' routes'
            provenance' nameCert' =>
              cases hfields
              rfl

instance dedekindCutBHistCarrier : BHistCarrier DedekindCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindCutToEventFlow
  fromEventFlow := dedekindCutFromEventFlow

instance dedekindCutChapterTasteGate : ChapterTasteGate DedekindCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dedekindCutFromEventFlow (dedekindCutToEventFlow x) = some x
    exact DedekindCutTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dedekindCutToEventFlow_injective heq)

instance dedekindCutFieldFaithful : FieldFaithful DedekindCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dedekindCutFields
  field_faithful := dedekindCut_field_faithful

instance dedekindCutNontrivial : BEDC.Meta.TasteGate.Nontrivial DedekindCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DedekindCutUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DedekindCutUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DedekindCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindCutChapterTasteGate

theorem DedekindCutTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DedekindCutUp) ∧
      Nonempty (FieldFaithful DedekindCutUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial DedekindCutUp) ∧
      (∀ h : BHist, dedekindCutDecodeBHist (dedekindCutEncodeBHist h) = h) ∧
      dedekindCutEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨dedekindCutChapterTasteGate⟩
  constructor
  · exact ⟨dedekindCutFieldFaithful⟩
  constructor
  · exact ⟨dedekindCutNontrivial⟩
  constructor
  · exact DedekindCutTasteGate_single_carrier_alignment_decode
  · rfl

end BEDC.Derived.DedekindCutUp
