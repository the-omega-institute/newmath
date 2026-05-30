import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FareySequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FareySequenceUp : Type where
  | mk (B A M L T S D Q W R G E H C P N : BHist) : FareySequenceUp
  deriving DecidableEq

def fareySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fareySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fareySequenceEncodeBHist h

def fareySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fareySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fareySequenceDecodeBHist tail)

private theorem FareySequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, fareySequenceDecodeBHist (fareySequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fareySequenceFields : FareySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FareySequenceUp.mk B A M L T S D Q W R G E H C P N =>
      [B, A, M, L, T, S, D, Q, W, R, G, E, H, C, P, N]

def fareySequenceToEventFlow : FareySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map fareySequenceEncodeBHist (fareySequenceFields x)

def fareySequenceFromEventFlow (ef : EventFlow) : Option FareySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | B :: restB =>
      match restB with
      | [] => none
      | A :: restA =>
          match restA with
          | [] => none
          | M :: restM =>
              match restM with
              | [] => none
              | L :: restL =>
                  match restL with
                  | [] => none
                  | T :: restT =>
                      match restT with
                      | [] => none
                      | S :: restS =>
                          match restS with
                          | [] => none
                          | D :: restD =>
                              match restD with
                              | [] => none
                              | Q :: restQ =>
                                  match restQ with
                                  | [] => none
                                  | W :: restW =>
                                      match restW with
                                      | [] => none
                                      | R :: restR =>
                                          match restR with
                                          | [] => none
                                          | G :: restG =>
                                              match restG with
                                              | [] => none
                                              | E :: restE =>
                                                  match restE with
                                                  | [] => none
                                                  | H :: restH =>
                                                      match restH with
                                                      | [] => none
                                                      | C :: restC =>
                                                          match restC with
                                                          | [] => none
                                                          | P :: restP =>
                                                              match restP with
                                                              | [] => none
                                                              | N :: restN =>
                                                                  match restN with
                                                                  | [] =>
                                                                      some
                                                                        (FareySequenceUp.mk
                                                                          (fareySequenceDecodeBHist B)
                                                                          (fareySequenceDecodeBHist A)
                                                                          (fareySequenceDecodeBHist M)
                                                                          (fareySequenceDecodeBHist L)
                                                                          (fareySequenceDecodeBHist T)
                                                                          (fareySequenceDecodeBHist S)
                                                                          (fareySequenceDecodeBHist D)
                                                                          (fareySequenceDecodeBHist Q)
                                                                          (fareySequenceDecodeBHist W)
                                                                          (fareySequenceDecodeBHist R)
                                                                          (fareySequenceDecodeBHist G)
                                                                          (fareySequenceDecodeBHist E)
                                                                          (fareySequenceDecodeBHist H)
                                                                          (fareySequenceDecodeBHist C)
                                                                          (fareySequenceDecodeBHist P)
                                                                          (fareySequenceDecodeBHist N))
                                                                  | _ :: _ => none

private theorem FareySequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FareySequenceUp,
      fareySequenceFromEventFlow (fareySequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B A M L T S D Q W R G E H C P N =>
      change
        some
          (FareySequenceUp.mk
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist B))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist A))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist M))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist L))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist T))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist S))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist D))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist Q))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist W))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist R))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist G))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist E))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist H))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist C))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist P))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist N))) =
          some (FareySequenceUp.mk B A M L T S D Q W R G E H C P N)
      rw [FareySequenceTasteGate_single_carrier_alignment_decode B,
        FareySequenceTasteGate_single_carrier_alignment_decode A,
        FareySequenceTasteGate_single_carrier_alignment_decode M,
        FareySequenceTasteGate_single_carrier_alignment_decode L,
        FareySequenceTasteGate_single_carrier_alignment_decode T,
        FareySequenceTasteGate_single_carrier_alignment_decode S,
        FareySequenceTasteGate_single_carrier_alignment_decode D,
        FareySequenceTasteGate_single_carrier_alignment_decode Q,
        FareySequenceTasteGate_single_carrier_alignment_decode W,
        FareySequenceTasteGate_single_carrier_alignment_decode R,
        FareySequenceTasteGate_single_carrier_alignment_decode G,
        FareySequenceTasteGate_single_carrier_alignment_decode E,
        FareySequenceTasteGate_single_carrier_alignment_decode H,
        FareySequenceTasteGate_single_carrier_alignment_decode C,
        FareySequenceTasteGate_single_carrier_alignment_decode P,
        FareySequenceTasteGate_single_carrier_alignment_decode N]

private theorem FareySequenceTasteGate_single_carrier_alignment_injective
    {x y : FareySequenceUp} :
    fareySequenceToEventFlow x = fareySequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fareySequenceFromEventFlow (fareySequenceToEventFlow x) =
        fareySequenceFromEventFlow (fareySequenceToEventFlow y) :=
    congrArg fareySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FareySequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FareySequenceTasteGate_single_carrier_alignment_round_trip y)))

instance fareySequenceBHistCarrier : BHistCarrier FareySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fareySequenceToEventFlow
  fromEventFlow := fareySequenceFromEventFlow

instance fareySequenceChapterTasteGate : ChapterTasteGate FareySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fareySequenceFromEventFlow (fareySequenceToEventFlow x) = some x
    exact FareySequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FareySequenceTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate FareySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fareySequenceChapterTasteGate

theorem FareySequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, fareySequenceDecodeBHist (fareySequenceEncodeBHist h) = h) ∧
      (∀ x : FareySequenceUp,
        fareySequenceFromEventFlow (fareySequenceToEventFlow x) = some x) ∧
        (∀ x y : FareySequenceUp,
          fareySequenceToEventFlow x = fareySequenceToEventFlow y → x = y) ∧
          fareySequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨FareySequenceTasteGate_single_carrier_alignment_decode,
      FareySequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ h => FareySequenceTasteGate_single_carrier_alignment_injective h),
      rfl⟩

end BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FareySequenceCarrier [AskSetup] [PackageSetup]
    (B A M L T S D Q W R G E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory B ∧ UnaryHistory A ∧ UnaryHistory M ∧ UnaryHistory L ∧
    UnaryHistory T ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory Q ∧
      UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory G ∧ UnaryHistory E ∧
        UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
          A = BHist.Empty ∧ S = BHist.Empty ∧ M = BHist.Empty ∧
            G = BHist.Empty ∧ E = BHist.Empty ∧ PkgSig bundle P pkg

theorem FareySequenceCarrier_stern_brocot_adjacency_obligations
    [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N adjacencyRead mediantRead approximationRead
      sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg →
      Cont A S adjacencyRead →
        Cont adjacencyRead M mediantRead →
          Cont mediantRead G approximationRead →
            Cont approximationRead E sealedRead →
              PkgSig bundle sealedRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row adjacencyRead ∨ hsame row mediantRead ∨
                        hsame row approximationRead ∨ hsame row sealedRead)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row S ∨ hsame row M ∨ hsame row G ∨
                        hsame row E ∨ hsame row adjacencyRead ∨ hsame row sealedRead)
                    (fun row : BHist =>
                      PkgSig bundle P pkg ∧
                        (hsame row adjacencyRead ∨ hsame row sealedRead))
                    hsame ∧
                  UnaryHistory adjacencyRead ∧ UnaryHistory mediantRead ∧
                    UnaryHistory approximationRead ∧ UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont SemanticNameCert hsame UnaryHistory
  intro carrier adjacencyRoute mediantRoute approximationRoute sealedRoute _sealedPkg
  obtain ⟨_bUnary, aUnary, mUnary, _lUnary, _tUnary, sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, gUnary, eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    aEmpty, sEmpty, mEmpty, gEmpty, eEmpty, provenancePkg⟩ := carrier
  cases aEmpty
  cases sEmpty
  cases mEmpty
  cases gEmpty
  cases eEmpty
  have adjacencyUnary : UnaryHistory adjacencyRead :=
    unary_cont_closed aUnary sUnary adjacencyRoute
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed adjacencyUnary mUnary mediantRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed mediantUnary gUnary approximationRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed approximationUnary eUnary sealedRoute
  have adjacencyEmpty : hsame adjacencyRead BHist.Empty := by
    cases adjacencyRoute
    rfl
  have mediantEmpty : hsame mediantRead BHist.Empty := by
    cases adjacencyEmpty
    cases mediantRoute
    rfl
  have approximationEmpty : hsame approximationRead BHist.Empty := by
    cases mediantEmpty
    cases approximationRoute
    rfl
  have sealedEmpty : hsame sealedRead BHist.Empty := by
    cases approximationEmpty
    cases sealedRoute
    rfl
  have mediantToAdjacency : hsame mediantRead adjacencyRead :=
    hsame_trans mediantEmpty (hsame_symm adjacencyEmpty)
  have approximationToAdjacency : hsame approximationRead adjacencyRead :=
    hsame_trans approximationEmpty (hsame_symm adjacencyEmpty)
  have sealedToAdjacency : hsame sealedRead adjacencyRead :=
    hsame_trans sealedEmpty (hsame_symm adjacencyEmpty)
  have adjacencyPattern :
      ∀ {row : BHist}, hsame row adjacencyRead →
        hsame row BHist.Empty ∨ hsame row BHist.Empty ∨ hsame row BHist.Empty ∨
          hsame row BHist.Empty ∨ hsame row BHist.Empty ∨
            hsame row adjacencyRead ∨ hsame row sealedRead := by
    intro row sameAdjacency
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameAdjacency)))))
  have sourceToAdjacency :
      ∀ {row : BHist},
        hsame row adjacencyRead ∨ hsame row mediantRead ∨
            hsame row approximationRead ∨ hsame row sealedRead →
          hsame row adjacencyRead := by
    intro row source
    cases source with
    | inl sameAdjacency =>
        exact sameAdjacency
    | inr rest =>
        cases rest with
        | inl sameMediant =>
            exact hsame_trans sameMediant mediantToAdjacency
        | inr rest' =>
            cases rest' with
            | inl sameApproximation =>
                exact hsame_trans sameApproximation approximationToAdjacency
            | inr sameSealed =>
                exact hsame_trans sameSealed sealedToAdjacency
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row adjacencyRead ∨ hsame row mediantRead ∨
              hsame row approximationRead ∨ hsame row sealedRead)
          (fun row : BHist =>
            hsame row BHist.Empty ∨ hsame row BHist.Empty ∨ hsame row BHist.Empty ∨
              hsame row BHist.Empty ∨ hsame row BHist.Empty ∨
                hsame row adjacencyRead ∨ hsame row sealedRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ (hsame row adjacencyRead ∨ hsame row sealedRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro adjacencyRead (Or.inl (hsame_refl adjacencyRead))
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
        intro row other sameRows source
        have otherAdjacency : hsame other adjacencyRead :=
          hsame_trans (hsame_symm sameRows) (sourceToAdjacency source)
        exact Or.inl otherAdjacency
    }
    pattern_sound := by
      intro row source
      exact adjacencyPattern (sourceToAdjacency source)
    ledger_sound := by
      intro row source
      exact ⟨provenancePkg, Or.inl (sourceToAdjacency source)⟩
  }
  exact ⟨cert, adjacencyUnary, mediantUnary, approximationUnary, sealedUnary⟩

end BEDC.Derived.FareySequenceUp
