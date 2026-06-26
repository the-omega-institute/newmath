import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DNAWindowSixTriggerThresholdUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DNAWindowSixTriggerThresholdUp : Type where
  | mk (W B C A F L Q H R P N : BHist) : DNAWindowSixTriggerThresholdUp
  deriving DecidableEq

def dnaWindowSixTriggerThresholdEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dnaWindowSixTriggerThresholdEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dnaWindowSixTriggerThresholdEncodeBHist h

def dnaWindowSixTriggerThresholdDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dnaWindowSixTriggerThresholdDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dnaWindowSixTriggerThresholdDecodeBHist tail)

private theorem DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dnaWindowSixTriggerThresholdDecodeBHist
        (dnaWindowSixTriggerThresholdEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dnaWindowSixTriggerThresholdFields :
    DNAWindowSixTriggerThresholdUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DNAWindowSixTriggerThresholdUp.mk W B C A F L Q H R P N =>
      [W, B, C, A, F, L, Q, H, R, P, N]

def dnaWindowSixTriggerThresholdToEventFlow :
    DNAWindowSixTriggerThresholdUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (dnaWindowSixTriggerThresholdFields x).map dnaWindowSixTriggerThresholdEncodeBHist

def dnaWindowSixTriggerThresholdFromEventFlow :
    EventFlow → Option DNAWindowSixTriggerThresholdUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | W :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | C :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | F :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
                          match rest5 with
                          | [] => none
                          | Q :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | R :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (DNAWindowSixTriggerThresholdUp.mk
                                                      (dnaWindowSixTriggerThresholdDecodeBHist W)
                                                      (dnaWindowSixTriggerThresholdDecodeBHist B)
                                                      (dnaWindowSixTriggerThresholdDecodeBHist C)
                                                      (dnaWindowSixTriggerThresholdDecodeBHist A)
                                                      (dnaWindowSixTriggerThresholdDecodeBHist F)
                                                      (dnaWindowSixTriggerThresholdDecodeBHist L)
                                                      (dnaWindowSixTriggerThresholdDecodeBHist Q)
                                                      (dnaWindowSixTriggerThresholdDecodeBHist H)
                                                      (dnaWindowSixTriggerThresholdDecodeBHist R)
                                                      (dnaWindowSixTriggerThresholdDecodeBHist P)
                                                      (dnaWindowSixTriggerThresholdDecodeBHist N))
                                              | _ :: _ => none

private theorem DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_round_trip
    (x : DNAWindowSixTriggerThresholdUp) :
    dnaWindowSixTriggerThresholdFromEventFlow
        (dnaWindowSixTriggerThresholdToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W B C A F L Q H R P N =>
      change
        some
            (DNAWindowSixTriggerThresholdUp.mk
              (dnaWindowSixTriggerThresholdDecodeBHist
                (dnaWindowSixTriggerThresholdEncodeBHist W))
              (dnaWindowSixTriggerThresholdDecodeBHist
                (dnaWindowSixTriggerThresholdEncodeBHist B))
              (dnaWindowSixTriggerThresholdDecodeBHist
                (dnaWindowSixTriggerThresholdEncodeBHist C))
              (dnaWindowSixTriggerThresholdDecodeBHist
                (dnaWindowSixTriggerThresholdEncodeBHist A))
              (dnaWindowSixTriggerThresholdDecodeBHist
                (dnaWindowSixTriggerThresholdEncodeBHist F))
              (dnaWindowSixTriggerThresholdDecodeBHist
                (dnaWindowSixTriggerThresholdEncodeBHist L))
              (dnaWindowSixTriggerThresholdDecodeBHist
                (dnaWindowSixTriggerThresholdEncodeBHist Q))
              (dnaWindowSixTriggerThresholdDecodeBHist
                (dnaWindowSixTriggerThresholdEncodeBHist H))
              (dnaWindowSixTriggerThresholdDecodeBHist
                (dnaWindowSixTriggerThresholdEncodeBHist R))
              (dnaWindowSixTriggerThresholdDecodeBHist
                (dnaWindowSixTriggerThresholdEncodeBHist P))
              (dnaWindowSixTriggerThresholdDecodeBHist
                (dnaWindowSixTriggerThresholdEncodeBHist N))) =
          some (DNAWindowSixTriggerThresholdUp.mk W B C A F L Q H R P N)
      rw [DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_decode W,
        DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_decode B,
        DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_decode C,
        DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_decode A,
        DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_decode F,
        DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_decode L,
        DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_decode Q,
        DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_decode H,
        DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_decode R,
        DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_decode P,
        DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_decode N]

private theorem DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_injective
    {x y : DNAWindowSixTriggerThresholdUp} :
    dnaWindowSixTriggerThresholdToEventFlow x =
      dnaWindowSixTriggerThresholdToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dnaWindowSixTriggerThresholdFromEventFlow
          (dnaWindowSixTriggerThresholdToEventFlow x) =
        dnaWindowSixTriggerThresholdFromEventFlow
          (dnaWindowSixTriggerThresholdToEventFlow y) :=
    congrArg dnaWindowSixTriggerThresholdFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_round_trip y)))

private theorem DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_fields :
    ∀ x y : DNAWindowSixTriggerThresholdUp,
      dnaWindowSixTriggerThresholdFields x = dnaWindowSixTriggerThresholdFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 B1 C1 A1 F1 L1 Q1 H1 R1 P1 N1 =>
      cases y with
      | mk W2 B2 C2 A2 F2 L2 Q2 H2 R2 P2 N2 =>
          cases hfields
          rfl

instance dnaWindowSixTriggerThresholdBHistCarrier :
    BHistCarrier DNAWindowSixTriggerThresholdUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dnaWindowSixTriggerThresholdToEventFlow
  fromEventFlow := dnaWindowSixTriggerThresholdFromEventFlow

instance dnaWindowSixTriggerThresholdChapterTasteGate :
    ChapterTasteGate DNAWindowSixTriggerThresholdUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dnaWindowSixTriggerThresholdFromEventFlow
        (dnaWindowSixTriggerThresholdToEventFlow x) = some x
    exact DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_injective heq)

instance dnaWindowSixTriggerThresholdFieldFaithful :
    FieldFaithful DNAWindowSixTriggerThresholdUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dnaWindowSixTriggerThresholdFields
  field_faithful := DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_fields

instance dnaWindowSixTriggerThresholdNontrivial :
    Nontrivial DNAWindowSixTriggerThresholdUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DNAWindowSixTriggerThresholdUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DNAWindowSixTriggerThresholdUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DNAWindowSixTriggerThresholdUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dnaWindowSixTriggerThresholdChapterTasteGate

theorem DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment :
    (forall h : BHist,
      dnaWindowSixTriggerThresholdDecodeBHist
        (dnaWindowSixTriggerThresholdEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DNAWindowSixTriggerThresholdUp) ∧
        Nonempty (ChapterTasteGate DNAWindowSixTriggerThresholdUp) ∧
          dnaWindowSixTriggerThresholdEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨DNAWindowSixTriggerThresholdTasteGate_single_carrier_alignment_decode,
      ⟨dnaWindowSixTriggerThresholdBHistCarrier⟩,
      ⟨dnaWindowSixTriggerThresholdChapterTasteGate⟩,
      rfl⟩

theorem DNAWindowSixTriggerThreshold_full_cube_law [AskSetup] [PackageSetup]
    {W B C A F L Q H R P N coverageRead triggerRead lawRead tableRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    dnaWindowSixTriggerThresholdFields
        (DNAWindowSixTriggerThresholdUp.mk W B C A F L Q H R P N) =
        [W, B, C, A, F, L, Q, H, R, P, N] ->
      UnaryHistory W ->
        UnaryHistory B ->
          UnaryHistory C ->
            UnaryHistory A ->
              UnaryHistory F ->
                UnaryHistory L ->
                  UnaryHistory Q ->
                    Cont W B coverageRead ->
                      Cont coverageRead C triggerRead ->
                        Cont triggerRead A lawRead ->
                          Cont F L tableRead ->
                            Cont lawRead Q routeRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row routeRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row W ∨ hsame row B ∨ hsame row C ∨
                                          hsame row A ∨ hsame row F ∨ hsame row L ∨
                                            hsame row Q ∨ Cont lawRead Q routeRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont W B coverageRead ∧
                                          Cont coverageRead C triggerRead ∧
                                            Cont triggerRead A lawRead ∧
                                              Cont F L tableRead ∧
                                                Cont lawRead Q routeRead ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory coverageRead ∧
                                      UnaryHistory triggerRead ∧
                                        UnaryHistory lawRead ∧
                                          UnaryHistory tableRead ∧
                                            UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: DNAWindowSixTriggerThresholdUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fields wUnary bUnary cUnary aUnary fUnary lUnary qUnary coverageRoute
    triggerRoute lawRoute tableRoute routeRoute pPkg nPkg
  have _acceptedFields :
      dnaWindowSixTriggerThresholdFields
          (DNAWindowSixTriggerThresholdUp.mk W B C A F L Q H R P N) =
        [W, B, C, A, F, L, Q, H, R, P, N] := fields
  have coverageUnary : UnaryHistory coverageRead :=
    unary_cont_closed wUnary bUnary coverageRoute
  have triggerUnary : UnaryHistory triggerRead :=
    unary_cont_closed coverageUnary cUnary triggerRoute
  have lawUnary : UnaryHistory lawRead :=
    unary_cont_closed triggerUnary aUnary lawRoute
  have tableUnary : UnaryHistory tableRead :=
    unary_cont_closed fUnary lUnary tableRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed lawUnary qUnary routeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row B ∨ hsame row C ∨ hsame row A ∨ hsame row F ∨
              hsame row L ∨ hsame row Q ∨ Cont lawRead Q routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W B coverageRead ∧ Cont coverageRead C triggerRead ∧
              Cont triggerRead A lawRead ∧ Cont F L tableRead ∧
                Cont lawRead Q routeRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead ⟨hsame_refl routeRead, routeUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      right
      right
      right
      right
      right
      right
      right
      exact routeRoute
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverageRoute, triggerRoute, lawRoute, tableRoute, routeRoute,
          pPkg, nPkg⟩
  }
  exact ⟨cert, coverageUnary, triggerUnary, lawUnary, tableUnary, routeUnary⟩

end BEDC.Derived.DNAWindowSixTriggerThresholdUp
