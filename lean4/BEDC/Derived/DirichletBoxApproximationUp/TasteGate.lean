import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DirichletBoxApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DirichletBoxApproximationUp : Type where
  | mk (Q L F A D W G E H C P N : BHist) : DirichletBoxApproximationUp
  deriving DecidableEq

def dirichletBoxApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dirichletBoxApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dirichletBoxApproximationEncodeBHist h

def dirichletBoxApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dirichletBoxApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dirichletBoxApproximationDecodeBHist tail)

private theorem DirichletBoxApproximationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dirichletBoxApproximationDecodeBHist (dirichletBoxApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dirichletBoxApproximationFields : DirichletBoxApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DirichletBoxApproximationUp.mk Q L F A D W G E H C P N =>
      [Q, L, F, A, D, W, G, E, H, C, P, N]

def dirichletBoxApproximationToEventFlow : DirichletBoxApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dirichletBoxApproximationFields x).map dirichletBoxApproximationEncodeBHist

def dirichletBoxApproximationFromEventFlowTail
    (Q L F A D W G E H C : RawEvent) : EventFlow → Option DirichletBoxApproximationUp
  -- BEDC touchpoint anchor: BHist BMark
  | P :: restP =>
      match restP with
      | N :: rest =>
          match rest with
          | [] =>
              some
                (DirichletBoxApproximationUp.mk
                  (dirichletBoxApproximationDecodeBHist Q)
                  (dirichletBoxApproximationDecodeBHist L)
                  (dirichletBoxApproximationDecodeBHist F)
                  (dirichletBoxApproximationDecodeBHist A)
                  (dirichletBoxApproximationDecodeBHist D)
                  (dirichletBoxApproximationDecodeBHist W)
                  (dirichletBoxApproximationDecodeBHist G)
                  (dirichletBoxApproximationDecodeBHist E)
                  (dirichletBoxApproximationDecodeBHist H)
                  (dirichletBoxApproximationDecodeBHist C)
                  (dirichletBoxApproximationDecodeBHist P)
                  (dirichletBoxApproximationDecodeBHist N))
          | _ :: _ => none
      | [] => none
  | [] => none

def dirichletBoxApproximationFromEventFlow :
    EventFlow → Option DirichletBoxApproximationUp
  -- BEDC touchpoint anchor: BHist BMark
  | Q :: restQ =>
      match restQ with
      | L :: restL =>
          match restL with
          | F :: restF =>
              match restF with
              | A :: restA =>
                  match restA with
                  | D :: restD =>
                      match restD with
                      | W :: restW =>
                          match restW with
                          | G :: restG =>
                              match restG with
                              | E :: restE =>
                                  match restE with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          dirichletBoxApproximationFromEventFlowTail
                                            Q L F A D W G E H C restC
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

private theorem dirichletBoxApproximation_mk_congr
    {Q Q' L L' F F' A A' D D' W W' G G' E E' H H' C C' P P' N N' : BHist}
    (hQ : Q' = Q) (hL : L' = L) (hF : F' = F) (hA : A' = A)
    (hD : D' = D) (hW : W' = W) (hG : G' = G) (hE : E' = E)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    DirichletBoxApproximationUp.mk Q' L' F' A' D' W' G' E' H' C' P' N' =
      DirichletBoxApproximationUp.mk Q L F A D W G E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hL
  cases hF
  cases hA
  cases hD
  cases hW
  cases hG
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem DirichletBoxApproximationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DirichletBoxApproximationUp,
      dirichletBoxApproximationFromEventFlow
        (dirichletBoxApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q L F A D W G E H C P N =>
      exact
        congrArg some
          (dirichletBoxApproximation_mk_congr
            (DirichletBoxApproximationTasteGate_single_carrier_alignment_decode Q)
            (DirichletBoxApproximationTasteGate_single_carrier_alignment_decode L)
            (DirichletBoxApproximationTasteGate_single_carrier_alignment_decode F)
            (DirichletBoxApproximationTasteGate_single_carrier_alignment_decode A)
            (DirichletBoxApproximationTasteGate_single_carrier_alignment_decode D)
            (DirichletBoxApproximationTasteGate_single_carrier_alignment_decode W)
            (DirichletBoxApproximationTasteGate_single_carrier_alignment_decode G)
            (DirichletBoxApproximationTasteGate_single_carrier_alignment_decode E)
            (DirichletBoxApproximationTasteGate_single_carrier_alignment_decode H)
            (DirichletBoxApproximationTasteGate_single_carrier_alignment_decode C)
            (DirichletBoxApproximationTasteGate_single_carrier_alignment_decode P)
            (DirichletBoxApproximationTasteGate_single_carrier_alignment_decode N))

private theorem dirichletBoxApproximationToEventFlow_injective
    {x y : DirichletBoxApproximationUp} :
    dirichletBoxApproximationToEventFlow x =
      dirichletBoxApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dirichletBoxApproximationFromEventFlow (dirichletBoxApproximationToEventFlow x) =
        dirichletBoxApproximationFromEventFlow (dirichletBoxApproximationToEventFlow y) :=
    congrArg dirichletBoxApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DirichletBoxApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DirichletBoxApproximationTasteGate_single_carrier_alignment_round_trip y)))

private theorem dirichletBoxApproximation_field_faithful :
    ∀ x y : DirichletBoxApproximationUp,
      dirichletBoxApproximationFields x = dirichletBoxApproximationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q L F A D W G E H C P N =>
      cases y with
      | mk Q' L' F' A' D' W' G' E' H' C' P' N' =>
          cases hfields
          rfl

instance dirichletBoxApproximationBHistCarrier :
    BHistCarrier DirichletBoxApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dirichletBoxApproximationToEventFlow
  fromEventFlow := dirichletBoxApproximationFromEventFlow

instance dirichletBoxApproximationChapterTasteGate :
    ChapterTasteGate DirichletBoxApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dirichletBoxApproximationFromEventFlow (dirichletBoxApproximationToEventFlow x) =
        some x
    exact DirichletBoxApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dirichletBoxApproximationToEventFlow_injective heq)

instance dirichletBoxApproximationFieldFaithful :
    FieldFaithful DirichletBoxApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dirichletBoxApproximationFields
  field_faithful := dirichletBoxApproximation_field_faithful

instance dirichletBoxApproximationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DirichletBoxApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DirichletBoxApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      DirichletBoxApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DirichletBoxApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dirichletBoxApproximationChapterTasteGate

theorem DirichletBoxApproximationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DirichletBoxApproximationUp) ∧
      Nonempty (BHistCarrier DirichletBoxApproximationUp) ∧
        Nonempty (FieldFaithful DirichletBoxApproximationUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial DirichletBoxApproximationUp) ∧
            dirichletBoxApproximationDecodeBHist
                (dirichletBoxApproximationEncodeBHist BHist.Empty) =
              BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨dirichletBoxApproximationChapterTasteGate⟩
  constructor
  · exact ⟨dirichletBoxApproximationBHistCarrier⟩
  constructor
  · exact ⟨dirichletBoxApproximationFieldFaithful⟩
  constructor
  · exact ⟨dirichletBoxApproximationNontrivial⟩
  · rfl

end BEDC.Derived.DirichletBoxApproximationUp
