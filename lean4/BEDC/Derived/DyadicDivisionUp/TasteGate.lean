import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicDivisionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicDivisionUp : Type where
  | mk (A B L R T E H C P N : BHist) : DyadicDivisionUp
  deriving DecidableEq

def dyadicDivisionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicDivisionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicDivisionEncodeBHist h

def dyadicDivisionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicDivisionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicDivisionDecodeBHist tail)

private theorem DyadicDivisionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem DyadicDivisionTasteGate_single_carrier_alignment_mk_congr
    {A A' B B' L L' R R' T T' E E' H H' C C' P P' N N' : BHist}
    (hA : A' = A)
    (hB : B' = B)
    (hL : L' = L)
    (hR : R' = R)
    (hT : T' = T)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    DyadicDivisionUp.mk A' B' L' R' T' E' H' C' P' N' =
      DyadicDivisionUp.mk A B L R T E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hB
  cases hL
  cases hR
  cases hT
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem DyadicDivisionTasteGate_single_carrier_alignment_encode_injective
    {a b : BHist} :
    dyadicDivisionEncodeBHist a = dyadicDivisionEncodeBHist b → a = b := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  have hd :
      dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist a) =
        dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist b) :=
    congrArg dyadicDivisionDecodeBHist h
  exact Eq.trans
    (DyadicDivisionTasteGate_single_carrier_alignment_decode a).symm
    (Eq.trans hd (DyadicDivisionTasteGate_single_carrier_alignment_decode b))

def dyadicDivisionFields : DyadicDivisionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicDivisionUp.mk A B L R T E H C P N => [A, B, L, R, T, E, H, C, P, N]

def dyadicDivisionToEventFlow : DyadicDivisionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicDivisionFields x).map dyadicDivisionEncodeBHist

def dyadicDivisionFromEventFlow : EventFlow → Option DyadicDivisionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | L :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (DyadicDivisionUp.mk
                                                  (dyadicDivisionDecodeBHist A)
                                                  (dyadicDivisionDecodeBHist B)
                                                  (dyadicDivisionDecodeBHist L)
                                                  (dyadicDivisionDecodeBHist R)
                                                  (dyadicDivisionDecodeBHist T)
                                                  (dyadicDivisionDecodeBHist E)
                                                  (dyadicDivisionDecodeBHist H)
                                                  (dyadicDivisionDecodeBHist C)
                                                  (dyadicDivisionDecodeBHist P)
                                                  (dyadicDivisionDecodeBHist N))
                                          | _ :: _ => none

private theorem DyadicDivisionTasteGate_single_carrier_alignment_round_trip
    (x : DyadicDivisionUp) :
    dyadicDivisionFromEventFlow (dyadicDivisionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A B L R T E H C P N =>
      change
        some
          (DyadicDivisionUp.mk
            (dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist A))
            (dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist B))
            (dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist L))
            (dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist R))
            (dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist T))
            (dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist E))
            (dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist H))
            (dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist C))
            (dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist P))
            (dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist N))) =
          some (DyadicDivisionUp.mk A B L R T E H C P N)
      exact
        congrArg some
          (DyadicDivisionTasteGate_single_carrier_alignment_mk_congr
            (DyadicDivisionTasteGate_single_carrier_alignment_decode A)
            (DyadicDivisionTasteGate_single_carrier_alignment_decode B)
            (DyadicDivisionTasteGate_single_carrier_alignment_decode L)
            (DyadicDivisionTasteGate_single_carrier_alignment_decode R)
            (DyadicDivisionTasteGate_single_carrier_alignment_decode T)
            (DyadicDivisionTasteGate_single_carrier_alignment_decode E)
            (DyadicDivisionTasteGate_single_carrier_alignment_decode H)
            (DyadicDivisionTasteGate_single_carrier_alignment_decode C)
            (DyadicDivisionTasteGate_single_carrier_alignment_decode P)
            (DyadicDivisionTasteGate_single_carrier_alignment_decode N))

private theorem DyadicDivisionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicDivisionUp} :
    dyadicDivisionToEventFlow x = dyadicDivisionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk A₁ B₁ L₁ R₁ T₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ B₂ L₂ R₂ T₂ E₂ H₂ C₂ P₂ N₂ =>
          injection heq with hA tailA
          injection tailA with hB tailB
          injection tailB with hL tailL
          injection tailL with hR tailR
          injection tailR with hT tailT
          injection tailT with hE tailE
          injection tailE with hH tailH
          injection tailH with hC tailC
          injection tailC with hP tailP
          injection tailP with hN _
          cases DyadicDivisionTasteGate_single_carrier_alignment_encode_injective hA
          cases DyadicDivisionTasteGate_single_carrier_alignment_encode_injective hB
          cases DyadicDivisionTasteGate_single_carrier_alignment_encode_injective hL
          cases DyadicDivisionTasteGate_single_carrier_alignment_encode_injective hR
          cases DyadicDivisionTasteGate_single_carrier_alignment_encode_injective hT
          cases DyadicDivisionTasteGate_single_carrier_alignment_encode_injective hE
          cases DyadicDivisionTasteGate_single_carrier_alignment_encode_injective hH
          cases DyadicDivisionTasteGate_single_carrier_alignment_encode_injective hC
          cases DyadicDivisionTasteGate_single_carrier_alignment_encode_injective hP
          cases DyadicDivisionTasteGate_single_carrier_alignment_encode_injective hN
          rfl

private theorem DyadicDivisionTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : DyadicDivisionUp, dyadicDivisionFields x = dyadicDivisionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ B₁ L₁ R₁ T₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ B₂ L₂ R₂ T₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance dyadicDivisionBHistCarrier : BHistCarrier DyadicDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicDivisionToEventFlow
  fromEventFlow := dyadicDivisionFromEventFlow

instance dyadicDivisionChapterTasteGate : ChapterTasteGate DyadicDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicDivisionFromEventFlow (dyadicDivisionToEventFlow x) = some x
    exact DyadicDivisionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicDivisionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicDivisionFieldFaithful : FieldFaithful DyadicDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicDivisionFields
  field_faithful := DyadicDivisionTasteGate_single_carrier_alignment_field_faithful

instance dyadicDivisionNontrivial : Nontrivial DyadicDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicDivisionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicDivisionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicDivisionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicDivisionChapterTasteGate

theorem DyadicDivisionTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicDivisionDecodeBHist (dyadicDivisionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DyadicDivisionUp) ∧
        Nonempty (ChapterTasteGate DyadicDivisionUp) ∧
          dyadicDivisionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨DyadicDivisionTasteGate_single_carrier_alignment_decode, ⟨dyadicDivisionBHistCarrier⟩,
      ⟨dyadicDivisionChapterTasteGate⟩, rfl⟩

end BEDC.Derived.DyadicDivisionUp
