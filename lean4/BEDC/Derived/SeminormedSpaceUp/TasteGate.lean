import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeminormedSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeminormedSpaceUp : Type where
  | mk (V R I F Z T A U M H C P N : BHist) : SeminormedSpaceUp
  deriving DecidableEq

def seminormedSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: seminormedSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: seminormedSpaceEncodeBHist h

def seminormedSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (seminormedSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (seminormedSpaceDecodeBHist tail)

private theorem seminormedSpaceDecode_encode_bhist :
    ∀ h : BHist, seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem seminormedSpace_mk_congr
    {V V' R R' I I' F F' Z Z' T T' A A' U U' M M' H H' C C' P P' N N' :
      BHist}
    (hV : V' = V) (hR : R' = R) (hI : I' = I) (hF : F' = F) (hZ : Z' = Z)
    (hT : T' = T) (hA : A' = A) (hU : U' = U) (hM : M' = M) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    SeminormedSpaceUp.mk V' R' I' F' Z' T' A' U' M' H' C' P' N' =
      SeminormedSpaceUp.mk V R I F Z T A U M H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hV
  cases hR
  cases hI
  cases hF
  cases hZ
  cases hT
  cases hA
  cases hU
  cases hM
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def seminormedSpaceFields : SeminormedSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeminormedSpaceUp.mk V R I F Z T A U M H C P N => [V, R, I, F, Z, T, A, U, M, H, C, P, N]

def seminormedSpaceToEventFlow : SeminormedSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (seminormedSpaceFields x).map seminormedSpaceEncodeBHist

private def seminormedSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => seminormedSpaceEventAtDefault index rest

def seminormedSpaceFromEventFlow : EventFlow → Option SeminormedSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (SeminormedSpaceUp.mk
        (seminormedSpaceDecodeBHist (seminormedSpaceEventAtDefault 0 ef))
        (seminormedSpaceDecodeBHist (seminormedSpaceEventAtDefault 1 ef))
        (seminormedSpaceDecodeBHist (seminormedSpaceEventAtDefault 2 ef))
        (seminormedSpaceDecodeBHist (seminormedSpaceEventAtDefault 3 ef))
        (seminormedSpaceDecodeBHist (seminormedSpaceEventAtDefault 4 ef))
        (seminormedSpaceDecodeBHist (seminormedSpaceEventAtDefault 5 ef))
        (seminormedSpaceDecodeBHist (seminormedSpaceEventAtDefault 6 ef))
        (seminormedSpaceDecodeBHist (seminormedSpaceEventAtDefault 7 ef))
        (seminormedSpaceDecodeBHist (seminormedSpaceEventAtDefault 8 ef))
        (seminormedSpaceDecodeBHist (seminormedSpaceEventAtDefault 9 ef))
        (seminormedSpaceDecodeBHist (seminormedSpaceEventAtDefault 10 ef))
        (seminormedSpaceDecodeBHist (seminormedSpaceEventAtDefault 11 ef))
        (seminormedSpaceDecodeBHist (seminormedSpaceEventAtDefault 12 ef)))

private theorem seminormedSpace_round_trip :
    ∀ x : SeminormedSpaceUp,
      seminormedSpaceFromEventFlow (seminormedSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V R I F Z T A U M H C P N =>
      change
        some
          (SeminormedSpaceUp.mk
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist V))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist R))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist I))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist F))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist Z))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist T))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist A))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist U))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist M))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist H))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist C))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist P))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist N))) =
          some (SeminormedSpaceUp.mk V R I F Z T A U M H C P N)
      rw [seminormedSpaceDecode_encode_bhist V, seminormedSpaceDecode_encode_bhist R,
        seminormedSpaceDecode_encode_bhist I, seminormedSpaceDecode_encode_bhist F,
        seminormedSpaceDecode_encode_bhist Z, seminormedSpaceDecode_encode_bhist T,
        seminormedSpaceDecode_encode_bhist A, seminormedSpaceDecode_encode_bhist U,
        seminormedSpaceDecode_encode_bhist M, seminormedSpaceDecode_encode_bhist H,
        seminormedSpaceDecode_encode_bhist C, seminormedSpaceDecode_encode_bhist P,
        seminormedSpaceDecode_encode_bhist N]

private theorem seminormedSpaceToEventFlow_injective
    {x y : SeminormedSpaceUp} :
    seminormedSpaceToEventFlow x = seminormedSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      seminormedSpaceFromEventFlow (seminormedSpaceToEventFlow x) =
        seminormedSpaceFromEventFlow (seminormedSpaceToEventFlow y) :=
    congrArg seminormedSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (seminormedSpace_round_trip x).symm
      (Eq.trans hread (seminormedSpace_round_trip y)))

private theorem seminormedSpace_field_faithful :
    ∀ x y : SeminormedSpaceUp, seminormedSpaceFields x = seminormedSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk V R I F Z T A U M H C P N =>
      cases y with
      | mk V' R' I' F' Z' T' A' U' M' H' C' P' N' =>
          cases hfields
          rfl

instance seminormedSpaceBHistCarrier : BHistCarrier SeminormedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := seminormedSpaceToEventFlow
  fromEventFlow := seminormedSpaceFromEventFlow

instance seminormedSpaceChapterTasteGate : ChapterTasteGate SeminormedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change seminormedSpaceFromEventFlow (seminormedSpaceToEventFlow x) = some x
    exact seminormedSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (seminormedSpaceToEventFlow_injective heq)

instance seminormedSpaceFieldFaithful : FieldFaithful SeminormedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := seminormedSpaceFields
  field_faithful := seminormedSpace_field_faithful

instance seminormedSpaceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SeminormedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SeminormedSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      SeminormedSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SeminormedSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  seminormedSpaceChapterTasteGate

theorem SeminormedSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist h) = h) ∧
      (∀ x : SeminormedSpaceUp,
        seminormedSpaceFromEventFlow (seminormedSpaceToEventFlow x) = some x) ∧
        (∀ x y : SeminormedSpaceUp,
          seminormedSpaceToEventFlow x = seminormedSpaceToEventFlow y → x = y) ∧
          seminormedSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk V R I F Z T A U M H C P N =>
          change
            some
              (SeminormedSpaceUp.mk
                (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist V))
                (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist R))
                (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist I))
                (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist F))
                (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist Z))
                (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist T))
                (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist A))
                (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist U))
                (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist M))
                (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist H))
                (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist C))
                (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist P))
                (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist N))) =
              some (SeminormedSpaceUp.mk V R I F Z T A U M H C P N)
          exact
            congrArg some
              (seminormedSpace_mk_congr
                (seminormedSpaceDecode_encode_bhist V)
                (seminormedSpaceDecode_encode_bhist R)
                (seminormedSpaceDecode_encode_bhist I)
                (seminormedSpaceDecode_encode_bhist F)
                (seminormedSpaceDecode_encode_bhist Z)
                (seminormedSpaceDecode_encode_bhist T)
                (seminormedSpaceDecode_encode_bhist A)
                (seminormedSpaceDecode_encode_bhist U)
                (seminormedSpaceDecode_encode_bhist M)
                (seminormedSpaceDecode_encode_bhist H)
                (seminormedSpaceDecode_encode_bhist C)
                (seminormedSpaceDecode_encode_bhist P)
                (seminormedSpaceDecode_encode_bhist N))
    · constructor
      · intro x y heq
        cases x with
        | mk V R I F Z T A U M H C P N =>
            cases y with
            | mk V' R' I' F' Z' T' A' U' M' H' C' P' N' =>
                change
                  [seminormedSpaceEncodeBHist V, seminormedSpaceEncodeBHist R,
                    seminormedSpaceEncodeBHist I, seminormedSpaceEncodeBHist F,
                    seminormedSpaceEncodeBHist Z, seminormedSpaceEncodeBHist T,
                    seminormedSpaceEncodeBHist A, seminormedSpaceEncodeBHist U,
                    seminormedSpaceEncodeBHist M, seminormedSpaceEncodeBHist H,
                    seminormedSpaceEncodeBHist C, seminormedSpaceEncodeBHist P,
                    seminormedSpaceEncodeBHist N] =
                  [seminormedSpaceEncodeBHist V', seminormedSpaceEncodeBHist R',
                    seminormedSpaceEncodeBHist I', seminormedSpaceEncodeBHist F',
                    seminormedSpaceEncodeBHist Z', seminormedSpaceEncodeBHist T',
                    seminormedSpaceEncodeBHist A', seminormedSpaceEncodeBHist U',
                    seminormedSpaceEncodeBHist M', seminormedSpaceEncodeBHist H',
                    seminormedSpaceEncodeBHist C', seminormedSpaceEncodeBHist P',
                    seminormedSpaceEncodeBHist N'] at heq
                injection heq with hV tail0
                injection tail0 with hR tail1
                injection tail1 with hI tail2
                injection tail2 with hF tail3
                injection tail3 with hZ tail4
                injection tail4 with hT tail5
                injection tail5 with hA tail6
                injection tail6 with hU tail7
                injection tail7 with hM tail8
                injection tail8 with hH tail9
                injection tail9 with hC tail10
                injection tail10 with hP tail11
                injection tail11 with hN _
                have eV : V = V' := by
                  have h := congrArg seminormedSpaceDecodeBHist hV
                  exact
                    Eq.trans (seminormedSpaceDecode_encode_bhist V).symm
                      (Eq.trans h (seminormedSpaceDecode_encode_bhist V'))
                have eR : R = R' := by
                  have h := congrArg seminormedSpaceDecodeBHist hR
                  exact
                    Eq.trans (seminormedSpaceDecode_encode_bhist R).symm
                      (Eq.trans h (seminormedSpaceDecode_encode_bhist R'))
                have eI : I = I' := by
                  have h := congrArg seminormedSpaceDecodeBHist hI
                  exact
                    Eq.trans (seminormedSpaceDecode_encode_bhist I).symm
                      (Eq.trans h (seminormedSpaceDecode_encode_bhist I'))
                have eF : F = F' := by
                  have h := congrArg seminormedSpaceDecodeBHist hF
                  exact
                    Eq.trans (seminormedSpaceDecode_encode_bhist F).symm
                      (Eq.trans h (seminormedSpaceDecode_encode_bhist F'))
                have eZ : Z = Z' := by
                  have h := congrArg seminormedSpaceDecodeBHist hZ
                  exact
                    Eq.trans (seminormedSpaceDecode_encode_bhist Z).symm
                      (Eq.trans h (seminormedSpaceDecode_encode_bhist Z'))
                have eT : T = T' := by
                  have h := congrArg seminormedSpaceDecodeBHist hT
                  exact
                    Eq.trans (seminormedSpaceDecode_encode_bhist T).symm
                      (Eq.trans h (seminormedSpaceDecode_encode_bhist T'))
                have eA : A = A' := by
                  have h := congrArg seminormedSpaceDecodeBHist hA
                  exact
                    Eq.trans (seminormedSpaceDecode_encode_bhist A).symm
                      (Eq.trans h (seminormedSpaceDecode_encode_bhist A'))
                have eU : U = U' := by
                  have h := congrArg seminormedSpaceDecodeBHist hU
                  exact
                    Eq.trans (seminormedSpaceDecode_encode_bhist U).symm
                      (Eq.trans h (seminormedSpaceDecode_encode_bhist U'))
                have eM : M = M' := by
                  have h := congrArg seminormedSpaceDecodeBHist hM
                  exact
                    Eq.trans (seminormedSpaceDecode_encode_bhist M).symm
                      (Eq.trans h (seminormedSpaceDecode_encode_bhist M'))
                have eH : H = H' := by
                  have h := congrArg seminormedSpaceDecodeBHist hH
                  exact
                    Eq.trans (seminormedSpaceDecode_encode_bhist H).symm
                      (Eq.trans h (seminormedSpaceDecode_encode_bhist H'))
                have eC : C = C' := by
                  have h := congrArg seminormedSpaceDecodeBHist hC
                  exact
                    Eq.trans (seminormedSpaceDecode_encode_bhist C).symm
                      (Eq.trans h (seminormedSpaceDecode_encode_bhist C'))
                have eP : P = P' := by
                  have h := congrArg seminormedSpaceDecodeBHist hP
                  exact
                    Eq.trans (seminormedSpaceDecode_encode_bhist P).symm
                      (Eq.trans h (seminormedSpaceDecode_encode_bhist P'))
                have eN : N = N' := by
                  have h := congrArg seminormedSpaceDecodeBHist hN
                  exact
                    Eq.trans (seminormedSpaceDecode_encode_bhist N).symm
                      (Eq.trans h (seminormedSpaceDecode_encode_bhist N'))
                cases eV
                cases eR
                cases eI
                cases eF
                cases eZ
                cases eT
                cases eA
                cases eU
                cases eM
                cases eH
                cases eC
                cases eP
                cases eN
                rfl
      · rfl

end BEDC.Derived.SeminormedSpaceUp.TasteGate
