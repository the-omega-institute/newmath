import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatednessPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatednessPrincipleUp : Type where
  | mk (Q Am Ap I O B R E H C P N : BHist) : LocatednessPrincipleUp
  deriving DecidableEq

def locatednessPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatednessPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatednessPrincipleEncodeBHist h

def locatednessPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatednessPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatednessPrincipleDecodeBHist tail)

private theorem LocatednessPrincipleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatednessPrincipleDecodeBHist (locatednessPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatednessPrincipleFields : LocatednessPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatednessPrincipleUp.mk Q Am Ap I O B R E H C P N =>
      [Q, Am, Ap, I, O, B, R, E, H, C, P, N]

def locatednessPrincipleToEventFlow : LocatednessPrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatednessPrincipleFields x).map locatednessPrincipleEncodeBHist

def locatednessPrincipleFromEventFlow : EventFlow → Option LocatednessPrincipleUp
  -- BEDC touchpoint anchor: BHist BMark
  | Q :: restQ =>
      match restQ with
      | Am :: restAm =>
          match restAm with
          | Ap :: restAp =>
              match restAp with
              | I :: restI =>
                  match restI with
                  | O :: restO =>
                      match restO with
                      | B :: restB =>
                          match restB with
                          | R :: restR =>
                              match restR with
                              | E :: restE =>
                                  match restE with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          match restC with
                                          | P :: restP =>
                                              match restP with
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (LocatednessPrincipleUp.mk
                                                          (locatednessPrincipleDecodeBHist Q)
                                                          (locatednessPrincipleDecodeBHist Am)
                                                          (locatednessPrincipleDecodeBHist Ap)
                                                          (locatednessPrincipleDecodeBHist I)
                                                          (locatednessPrincipleDecodeBHist O)
                                                          (locatednessPrincipleDecodeBHist B)
                                                          (locatednessPrincipleDecodeBHist R)
                                                          (locatednessPrincipleDecodeBHist E)
                                                          (locatednessPrincipleDecodeBHist H)
                                                          (locatednessPrincipleDecodeBHist C)
                                                          (locatednessPrincipleDecodeBHist P)
                                                          (locatednessPrincipleDecodeBHist N))
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
      | [] => none
  | [] => none

private theorem locatednessPrinciple_mk_congr
    {Q Q' Am Am' Ap Ap' I I' O O' B B' R R' E E' H H' C C' P P' N N' : BHist}
    (hQ : Q' = Q) (hAm : Am' = Am) (hAp : Ap' = Ap) (hI : I' = I)
    (hO : O' = O) (hB : B' = B) (hR : R' = R) (hE : E' = E)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    LocatednessPrincipleUp.mk Q' Am' Ap' I' O' B' R' E' H' C' P' N' =
      LocatednessPrincipleUp.mk Q Am Ap I O B R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hAm
  cases hAp
  cases hI
  cases hO
  cases hB
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem LocatednessPrincipleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatednessPrincipleUp,
      locatednessPrincipleFromEventFlow (locatednessPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q Am Ap I O B R E H C P N =>
      exact
        congrArg some
          (locatednessPrinciple_mk_congr
            (LocatednessPrincipleTasteGate_single_carrier_alignment_decode Q)
            (LocatednessPrincipleTasteGate_single_carrier_alignment_decode Am)
            (LocatednessPrincipleTasteGate_single_carrier_alignment_decode Ap)
            (LocatednessPrincipleTasteGate_single_carrier_alignment_decode I)
            (LocatednessPrincipleTasteGate_single_carrier_alignment_decode O)
            (LocatednessPrincipleTasteGate_single_carrier_alignment_decode B)
            (LocatednessPrincipleTasteGate_single_carrier_alignment_decode R)
            (LocatednessPrincipleTasteGate_single_carrier_alignment_decode E)
            (LocatednessPrincipleTasteGate_single_carrier_alignment_decode H)
            (LocatednessPrincipleTasteGate_single_carrier_alignment_decode C)
            (LocatednessPrincipleTasteGate_single_carrier_alignment_decode P)
            (LocatednessPrincipleTasteGate_single_carrier_alignment_decode N))

private theorem locatednessPrincipleToEventFlow_injective
    {x y : LocatednessPrincipleUp} :
    locatednessPrincipleToEventFlow x = locatednessPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatednessPrincipleFromEventFlow (locatednessPrincipleToEventFlow x) =
        locatednessPrincipleFromEventFlow (locatednessPrincipleToEventFlow y) :=
    congrArg locatednessPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatednessPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatednessPrincipleTasteGate_single_carrier_alignment_round_trip y)))

instance locatednessPrincipleBHistCarrier : BHistCarrier LocatednessPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatednessPrincipleToEventFlow
  fromEventFlow := locatednessPrincipleFromEventFlow

instance locatednessPrincipleChapterTasteGate :
    ChapterTasteGate LocatednessPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatednessPrincipleFromEventFlow (locatednessPrincipleToEventFlow x) = some x
    exact LocatednessPrincipleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatednessPrincipleToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatednessPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatednessPrincipleChapterTasteGate

theorem LocatednessPrincipleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatednessPrincipleDecodeBHist (locatednessPrincipleEncodeBHist h) = h) ∧
      (∀ x : LocatednessPrincipleUp,
        locatednessPrincipleFromEventFlow (locatednessPrincipleToEventFlow x) = some x) ∧
      (∀ x y : LocatednessPrincipleUp,
        locatednessPrincipleToEventFlow x = locatednessPrincipleToEventFlow y → x = y) ∧
      locatednessPrincipleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · intro x
    exact LocatednessPrincipleTasteGate_single_carrier_alignment_round_trip x
  constructor
  · intro x y heq
    have hread :
        locatednessPrincipleFromEventFlow (locatednessPrincipleToEventFlow x) =
          locatednessPrincipleFromEventFlow (locatednessPrincipleToEventFlow y) :=
      congrArg locatednessPrincipleFromEventFlow heq
    exact Option.some.inj
      (Eq.trans (LocatednessPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
        (Eq.trans hread
          (LocatednessPrincipleTasteGate_single_carrier_alignment_round_trip y)))
  · rfl

end BEDC.Derived.LocatednessPrincipleUp
