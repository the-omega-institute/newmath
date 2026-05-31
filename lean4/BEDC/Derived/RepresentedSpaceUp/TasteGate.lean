import BEDC.Derived.RepresentedSpaceUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RepresentedSpaceUp : Type where
  | mk (S W rho X T H C P N : BHist) : RepresentedSpaceUp
  deriving DecidableEq

def representedSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: representedSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: representedSpaceEncodeBHist h

def representedSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (representedSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (representedSpaceDecodeBHist tail)

private theorem RepresentedSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, representedSpaceDecodeBHist (representedSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem RepresentedSpaceTasteGate_single_carrier_alignment_mk_congr
    {S S' W W' rho rho' X X' T T' H H' C C' P P' N N' : BHist}
    (hS : S' = S)
    (hW : W' = W)
    (hRho : rho' = rho)
    (hX : X' = X)
    (hT : T' = T)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    RepresentedSpaceUp.mk S' W' rho' X' T' H' C' P' N' =
      RepresentedSpaceUp.mk S W rho X T H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hW
  cases hRho
  cases hX
  cases hT
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def representedSpaceFields : RepresentedSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RepresentedSpaceUp.mk S W rho X T H C P N => [S, W, rho, X, T, H, C, P, N]

def representedSpaceToEventFlow : RepresentedSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (representedSpaceFields x).map representedSpaceEncodeBHist

noncomputable def representedSpaceFromEventFlow : EventFlow → Option RepresentedSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  List.rec none
    (fun S rest0 _ =>
      List.rec none
        (fun W rest1 _ =>
          List.rec none
            (fun rho rest2 _ =>
              List.rec none
                (fun X rest3 _ =>
                  List.rec none
                    (fun T rest4 _ =>
                      List.rec none
                        (fun H rest5 _ =>
                          List.rec none
                            (fun C rest6 _ =>
                              List.rec none
                                (fun P rest7 _ =>
                                  List.rec none
                                    (fun N rest8 _ =>
                                      List.rec
                                        (some
                                          (RepresentedSpaceUp.mk
                                            (representedSpaceDecodeBHist S)
                                            (representedSpaceDecodeBHist W)
                                            (representedSpaceDecodeBHist rho)
                                            (representedSpaceDecodeBHist X)
                                            (representedSpaceDecodeBHist T)
                                            (representedSpaceDecodeBHist H)
                                            (representedSpaceDecodeBHist C)
                                            (representedSpaceDecodeBHist P)
                                            (representedSpaceDecodeBHist N)))
                                        (fun _ _ _ => none)
                                        rest8)
                                    rest7)
                                rest6)
                            rest5)
                        rest4)
                    rest3)
                rest2)
            rest1)
        rest0)

private theorem RepresentedSpaceTasteGate_single_carrier_alignment_round_trip
    (x : RepresentedSpaceUp) :
    representedSpaceFromEventFlow (representedSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S W rho X T H C P N =>
      change
        some
          (RepresentedSpaceUp.mk
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist S))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist W))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist rho))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist X))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist T))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist H))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist C))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist P))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist N))) =
          some (RepresentedSpaceUp.mk S W rho X T H C P N)
      exact
        congrArg some
          (RepresentedSpaceTasteGate_single_carrier_alignment_mk_congr
            (RepresentedSpaceTasteGate_single_carrier_alignment_decode S)
            (RepresentedSpaceTasteGate_single_carrier_alignment_decode W)
            (RepresentedSpaceTasteGate_single_carrier_alignment_decode rho)
            (RepresentedSpaceTasteGate_single_carrier_alignment_decode X)
            (RepresentedSpaceTasteGate_single_carrier_alignment_decode T)
            (RepresentedSpaceTasteGate_single_carrier_alignment_decode H)
            (RepresentedSpaceTasteGate_single_carrier_alignment_decode C)
            (RepresentedSpaceTasteGate_single_carrier_alignment_decode P)
            (RepresentedSpaceTasteGate_single_carrier_alignment_decode N))

private theorem RepresentedSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RepresentedSpaceUp} :
    representedSpaceToEventFlow x = representedSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = representedSpaceFromEventFlow (representedSpaceToEventFlow x) :=
        (RepresentedSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      _ = representedSpaceFromEventFlow (representedSpaceToEventFlow y) :=
        congrArg representedSpaceFromEventFlow hxy
      _ = some y := RepresentedSpaceTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

noncomputable instance representedSpaceBHistCarrier : BHistCarrier RepresentedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := representedSpaceToEventFlow
  fromEventFlow := representedSpaceFromEventFlow

noncomputable instance representedSpaceChapterTasteGate : ChapterTasteGate RepresentedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change representedSpaceFromEventFlow (representedSpaceToEventFlow x) = some x
    exact RepresentedSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RepresentedSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

noncomputable def taste_gate : ChapterTasteGate RepresentedSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  representedSpaceChapterTasteGate

theorem RepresentedSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, representedSpaceDecodeBHist (representedSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RepresentedSpaceUp) ∧
        Nonempty (ChapterTasteGate RepresentedSpaceUp) ∧
          representedSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · exact ⟨representedSpaceBHistCarrier⟩
    · constructor
      · exact ⟨representedSpaceChapterTasteGate⟩
      · rfl

end BEDC.Derived.RepresentedSpaceUp
