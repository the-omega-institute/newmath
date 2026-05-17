import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PackageGovernanceExportUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PackageGovernanceExportUp : Type where
  | mk :
      (P R A C E F T M H K Q N : BHist) →
      PackageGovernanceExportUp
  deriving DecidableEq

def packageGovernanceExportEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: packageGovernanceExportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: packageGovernanceExportEncodeBHist h

def packageGovernanceExportDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (packageGovernanceExportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (packageGovernanceExportDecodeBHist tail)

private theorem PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux :
    ∀ h : BHist,
      packageGovernanceExportDecodeBHist (packageGovernanceExportEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem PackageGovernanceExportTasteGate_single_carrier_alignment_mk_aux
    {P P' R R' A A' C C' E E' F F' T T' M M' H H' K K' Q Q' N N' : BHist}
    (hP : P' = P)
    (hR : R' = R)
    (hA : A' = A)
    (hC : C' = C)
    (hE : E' = E)
    (hF : F' = F)
    (hT : T' = T)
    (hM : M' = M)
    (hH : H' = H)
    (hK : K' = K)
    (hQ : Q' = Q)
    (hN : N' = N) :
    PackageGovernanceExportUp.mk P' R' A' C' E' F' T' M' H' K' Q' N' =
      PackageGovernanceExportUp.mk P R A C E F T M H K Q N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hP
  cases hR
  cases hA
  cases hC
  cases hE
  cases hF
  cases hT
  cases hM
  cases hH
  cases hK
  cases hQ
  cases hN
  rfl

def packageGovernanceExportFields : PackageGovernanceExportUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PackageGovernanceExportUp.mk P R A C E F T M H K Q N =>
      [P, R, A, C, E, F, T, M, H, K, Q, N]

def packageGovernanceExportToEventFlow : PackageGovernanceExportUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PackageGovernanceExportUp.mk P R A C E F T M H K Q N =>
      [packageGovernanceExportEncodeBHist P,
        packageGovernanceExportEncodeBHist R,
        packageGovernanceExportEncodeBHist A,
        packageGovernanceExportEncodeBHist C,
        packageGovernanceExportEncodeBHist E,
        packageGovernanceExportEncodeBHist F,
        packageGovernanceExportEncodeBHist T,
        packageGovernanceExportEncodeBHist M,
        packageGovernanceExportEncodeBHist H,
        packageGovernanceExportEncodeBHist K,
        packageGovernanceExportEncodeBHist Q,
        packageGovernanceExportEncodeBHist N]

def packageGovernanceExportFromEventFlow :
    EventFlow → Option PackageGovernanceExportUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | P :: restP =>
      match restP with
      | [] => none
      | R :: restR =>
          match restR with
          | [] => none
          | A :: restA =>
              match restA with
              | [] => none
              | C :: restC =>
                  match restC with
                  | [] => none
                  | E :: restE =>
                      match restE with
                      | [] => none
                      | F :: restF =>
                          match restF with
                          | [] => none
                          | T :: restT =>
                              match restT with
                              | [] => none
                              | M :: restM =>
                                  match restM with
                                  | [] => none
                                  | H :: restH =>
                                      match restH with
                                      | [] => none
                                      | K :: restK =>
                                          match restK with
                                          | [] => none
                                          | Q :: restQ =>
                                              match restQ with
                                              | [] => none
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (PackageGovernanceExportUp.mk
                                                          (packageGovernanceExportDecodeBHist P)
                                                          (packageGovernanceExportDecodeBHist R)
                                                          (packageGovernanceExportDecodeBHist A)
                                                          (packageGovernanceExportDecodeBHist C)
                                                          (packageGovernanceExportDecodeBHist E)
                                                          (packageGovernanceExportDecodeBHist F)
                                                          (packageGovernanceExportDecodeBHist T)
                                                          (packageGovernanceExportDecodeBHist M)
                                                          (packageGovernanceExportDecodeBHist H)
                                                          (packageGovernanceExportDecodeBHist K)
                                                          (packageGovernanceExportDecodeBHist Q)
                                                          (packageGovernanceExportDecodeBHist N))
                                                  | _ :: _ => none

private theorem PackageGovernanceExportTasteGate_single_carrier_alignment_round_trip_aux :
    ∀ x : PackageGovernanceExportUp,
      packageGovernanceExportFromEventFlow (packageGovernanceExportToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P R A C E F T M H K Q N =>
      exact
        congrArg some
          (PackageGovernanceExportTasteGate_single_carrier_alignment_mk_aux
            (PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux P)
            (PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux R)
            (PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux A)
            (PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux C)
            (PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux E)
            (PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux F)
            (PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux T)
            (PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux M)
            (PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux H)
            (PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux K)
            (PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux Q)
            (PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux N))

private theorem PackageGovernanceExportTasteGate_single_carrier_alignment_injective_aux
    {x y : PackageGovernanceExportUp} :
    packageGovernanceExportToEventFlow x = packageGovernanceExportToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      packageGovernanceExportFromEventFlow (packageGovernanceExportToEventFlow x) =
        packageGovernanceExportFromEventFlow (packageGovernanceExportToEventFlow y) :=
    congrArg packageGovernanceExportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PackageGovernanceExportTasteGate_single_carrier_alignment_round_trip_aux x).symm
      (Eq.trans hread
        (PackageGovernanceExportTasteGate_single_carrier_alignment_round_trip_aux y)))

private theorem PackageGovernanceExportTasteGate_single_carrier_alignment_fields_aux :
    ∀ x y : PackageGovernanceExportUp,
      packageGovernanceExportFields x = packageGovernanceExportFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P₁ R₁ A₁ C₁ E₁ F₁ T₁ M₁ H₁ K₁ Q₁ N₁ =>
      cases y with
      | mk P₂ R₂ A₂ C₂ E₂ F₂ T₂ M₂ H₂ K₂ Q₂ N₂ =>
          cases hfields
          rfl

instance packageGovernanceExportBHistCarrier :
    BHistCarrier PackageGovernanceExportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := packageGovernanceExportToEventFlow
  fromEventFlow := packageGovernanceExportFromEventFlow

instance packageGovernanceExportChapterTasteGate :
    ChapterTasteGate PackageGovernanceExportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      packageGovernanceExportFromEventFlow (packageGovernanceExportToEventFlow x) =
        some x
    exact PackageGovernanceExportTasteGate_single_carrier_alignment_round_trip_aux x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PackageGovernanceExportTasteGate_single_carrier_alignment_injective_aux heq)

instance packageGovernanceExportFieldFaithful :
    FieldFaithful PackageGovernanceExportUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := packageGovernanceExportFields
  field_faithful := by
    intro x y hfields
    exact PackageGovernanceExportTasteGate_single_carrier_alignment_fields_aux x y hfields

instance packageGovernanceExportNontrivial :
    Nontrivial PackageGovernanceExportUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PackageGovernanceExportUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      PackageGovernanceExportUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PackageGovernanceExportTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        packageGovernanceExportDecodeBHist (packageGovernanceExportEncodeBHist h) = h) ∧
      (∀ x : PackageGovernanceExportUp,
        packageGovernanceExportFromEventFlow (packageGovernanceExportToEventFlow x) =
          some x) ∧
      (∀ x y : PackageGovernanceExportUp,
        packageGovernanceExportFields x = packageGovernanceExportFields y → x = y) ∧
      (∃ x y : PackageGovernanceExportUp, x ≠ y) ∧
      packageGovernanceExportEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact PackageGovernanceExportTasteGate_single_carrier_alignment_decode_aux
  · constructor
    · exact PackageGovernanceExportTasteGate_single_carrier_alignment_round_trip_aux
    · constructor
      · exact PackageGovernanceExportTasteGate_single_carrier_alignment_fields_aux
      · constructor
        · exact
            ⟨PackageGovernanceExportUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty,
              PackageGovernanceExportUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
              by
                intro h
                cases h⟩
        · rfl

end BEDC.Derived.PackageGovernanceExportUp
