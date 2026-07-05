import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalBisectionUp

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

inductive LocatedIntervalBisectionUp : Type where
  | mk (I D M S W R H C P N : BHist) : LocatedIntervalBisectionUp
  deriving DecidableEq

def locatedIntervalBisectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalBisectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalBisectionEncodeBHist h

def locatedIntervalBisectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalBisectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalBisectionDecodeBHist tail)

private theorem locatedIntervalBisectionDecode_encode_bhist :
    ∀ h : BHist,
      locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedIntervalBisectionFields : LocatedIntervalBisectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalBisectionUp.mk I D M S W R H C P N => [I, D, M, S, W, R, H, C, P, N]

def locatedIntervalBisectionToEventFlow : LocatedIntervalBisectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedIntervalBisectionFields x).map locatedIntervalBisectionEncodeBHist

def locatedIntervalBisectionFromEventFlow : EventFlow → Option LocatedIntervalBisectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: restD =>
      match restD with
      | [] => none
      | D :: restM =>
          match restM with
          | [] => none
          | M :: restS =>
              match restS with
              | [] => none
              | S :: restW =>
                  match restW with
                  | [] => none
                  | W :: restR =>
                      match restR with
                      | [] => none
                      | R :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (LocatedIntervalBisectionUp.mk
                                                  (locatedIntervalBisectionDecodeBHist I)
                                                  (locatedIntervalBisectionDecodeBHist D)
                                                  (locatedIntervalBisectionDecodeBHist M)
                                                  (locatedIntervalBisectionDecodeBHist S)
                                                  (locatedIntervalBisectionDecodeBHist W)
                                                  (locatedIntervalBisectionDecodeBHist R)
                                                  (locatedIntervalBisectionDecodeBHist H)
                                                  (locatedIntervalBisectionDecodeBHist C)
                                                  (locatedIntervalBisectionDecodeBHist P)
                                                  (locatedIntervalBisectionDecodeBHist N))
                                          | _ :: _ => none

private theorem locatedIntervalBisection_round_trip :
    ∀ x : LocatedIntervalBisectionUp,
      locatedIntervalBisectionFromEventFlow (locatedIntervalBisectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D M S W R H C P N =>
      change
        some
          (LocatedIntervalBisectionUp.mk
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist I))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist D))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist M))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist S))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist W))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist R))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist H))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist C))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist P))
            (locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist N))) =
          some (LocatedIntervalBisectionUp.mk I D M S W R H C P N)
      rw [locatedIntervalBisectionDecode_encode_bhist I,
        locatedIntervalBisectionDecode_encode_bhist D,
        locatedIntervalBisectionDecode_encode_bhist M,
        locatedIntervalBisectionDecode_encode_bhist S,
        locatedIntervalBisectionDecode_encode_bhist W,
        locatedIntervalBisectionDecode_encode_bhist R,
        locatedIntervalBisectionDecode_encode_bhist H,
        locatedIntervalBisectionDecode_encode_bhist C,
        locatedIntervalBisectionDecode_encode_bhist P,
        locatedIntervalBisectionDecode_encode_bhist N]

private theorem locatedIntervalBisectionToEventFlow_injective
    {x y : LocatedIntervalBisectionUp} :
    locatedIntervalBisectionToEventFlow x = locatedIntervalBisectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalBisectionFromEventFlow (locatedIntervalBisectionToEventFlow x) =
        locatedIntervalBisectionFromEventFlow (locatedIntervalBisectionToEventFlow y) :=
    congrArg locatedIntervalBisectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedIntervalBisection_round_trip x).symm
      (Eq.trans hread (locatedIntervalBisection_round_trip y)))

instance locatedIntervalBisectionBHistCarrier : BHistCarrier LocatedIntervalBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalBisectionToEventFlow
  fromEventFlow := locatedIntervalBisectionFromEventFlow

instance locatedIntervalBisectionChapterTasteGate :
    ChapterTasteGate LocatedIntervalBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedIntervalBisectionFromEventFlow (locatedIntervalBisectionToEventFlow x) = some x
    exact locatedIntervalBisection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedIntervalBisectionToEventFlow_injective heq)

theorem LocatedIntervalBisectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedIntervalBisectionDecodeBHist (locatedIntervalBisectionEncodeBHist h) = h) ∧
      (∀ x : LocatedIntervalBisectionUp,
        locatedIntervalBisectionFromEventFlow (locatedIntervalBisectionToEventFlow x) = some x) ∧
        (∀ x y : LocatedIntervalBisectionUp,
          locatedIntervalBisectionToEventFlow x = locatedIntervalBisectionToEventFlow y → x = y) ∧
          locatedIntervalBisectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locatedIntervalBisectionDecode_encode_bhist,
      locatedIntervalBisection_round_trip,
      (fun _ _ heq => locatedIntervalBisectionToEventFlow_injective heq),
      rfl⟩

theorem LocatedIntervalBisectionNameCertObligations [AskSetup] [PackageSetup]
    {I D M S W R H C P N intervalRead midpointRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory I ->
      UnaryHistory D ->
        UnaryHistory M ->
          UnaryHistory S ->
            UnaryHistory W ->
              UnaryHistory R ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont I D intervalRead ->
                          Cont intervalRead M midpointRead ->
                            Cont midpointRead W windowRead ->
                              Cont windowRead R sealRead ->
                                PkgSig bundle P pkg ->
                                  PkgSig bundle sealRead pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row sealRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row I ∨ hsame row D ∨ hsame row M ∨
                                            hsame row S ∨ hsame row W ∨ hsame row R ∨
                                              hsame row H ∨ hsame row C ∨
                                                hsame row P ∨ hsame row N ∨
                                                  hsame row intervalRead ∨
                                                    hsame row midpointRead ∨
                                                      hsame row windowRead ∨
                                                        hsame row sealRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont I D intervalRead ∧
                                            Cont intervalRead M midpointRead ∧
                                              Cont midpointRead W windowRead ∧
                                                Cont windowRead R sealRead ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle sealRead pkg)
                                        hsame ∧
                                      UnaryHistory intervalRead ∧
                                        UnaryHistory midpointRead ∧
                                          UnaryHistory windowRead ∧
                                            UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro iUnary dUnary mUnary _sUnary wUnary rUnary _hUnary _cUnary _pUnary _nUnary
    intervalRoute midpointRoute windowRoute sealRoute provenancePkg sealPkg
  have intervalUnary : UnaryHistory intervalRead :=
    unary_cont_closed iUnary dUnary intervalRoute
  have midpointUnary : UnaryHistory midpointRead :=
    unary_cont_closed intervalUnary mUnary midpointRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed midpointUnary wUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary rUnary sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row D ∨ hsame row M ∨ hsame row S ∨
              hsame row W ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row intervalRead ∨
                  hsame row midpointRead ∨ hsame row windowRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I D intervalRead ∧ Cont intervalRead M midpointRead ∧
              Cont midpointRead W windowRead ∧ Cont windowRead R sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, intervalRoute, midpointRoute, windowRoute, sealRoute, provenancePkg,
          sealPkg⟩
  }
  exact ⟨cert, intervalUnary, midpointUnary, windowUnary, sealUnary⟩

theorem LocatedIntervalBisectionCarrier_nonescape [AskSetup] [PackageSetup]
    {I D M S W R H C P N intervalRead midpointRead windowRead sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory I →
      UnaryHistory D →
        UnaryHistory M →
          UnaryHistory S →
            UnaryHistory W →
              UnaryHistory R →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory N →
                        locatedIntervalBisectionFields
                            (LocatedIntervalBisectionUp.mk I D M S W R H C P N) =
                          [I, D, M, S, W, R, H, C, P, N] →
                          Cont I D intervalRead →
                            Cont intervalRead M midpointRead →
                              Cont midpointRead W windowRead →
                                Cont windowRead R sealRead →
                                  Cont sealRead N publicRead →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle sealRead pkg →
                                        PkgSig bundle publicRead pkg →
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row publicRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row I ∨ hsame row D ∨ hsame row M ∨
                                                  hsame row S ∨ hsame row W ∨ hsame row R ∨
                                                    hsame row H ∨ hsame row C ∨
                                                      hsame row P ∨ hsame row N ∨
                                                        hsame row intervalRead ∨
                                                          hsame row midpointRead ∨
                                                            hsame row windowRead ∨
                                                              hsame row sealRead ∨
                                                                hsame row publicRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont I D intervalRead ∧
                                                  Cont intervalRead M midpointRead ∧
                                                    Cont midpointRead W windowRead ∧
                                                      Cont windowRead R sealRead ∧
                                                        Cont sealRead N publicRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle publicRead pkg)
                                              hsame ∧
                                            UnaryHistory intervalRead ∧
                                              UnaryHistory midpointRead ∧
                                                UnaryHistory windowRead ∧
                                                  UnaryHistory sealRead ∧
                                                    UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro iUnary dUnary mUnary _sUnary wUnary rUnary _hUnary _cUnary _pUnary nUnary
    _fieldsExact intervalRoute midpointRoute windowRoute sealRoute publicRoute
    provenancePkg _sealPkg publicPkg
  have intervalUnary : UnaryHistory intervalRead :=
    unary_cont_closed iUnary dUnary intervalRoute
  have midpointUnary : UnaryHistory midpointRead :=
    unary_cont_closed intervalUnary mUnary midpointRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed midpointUnary wUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary rUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary nUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row D ∨ hsame row M ∨ hsame row S ∨
              hsame row W ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row intervalRead ∨
                  hsame row midpointRead ∨ hsame row windowRead ∨ hsame row sealRead ∨
                    hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I D intervalRead ∧ Cont intervalRead M midpointRead ∧
              Cont midpointRead W windowRead ∧ Cont windowRead R sealRead ∧
                Cont sealRead N publicRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr source.left)))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, intervalRoute, midpointRoute, windowRoute, sealRoute, publicRoute,
          provenancePkg, publicPkg⟩
  }
  exact ⟨cert, intervalUnary, midpointUnary, windowUnary, sealUnary, publicUnary⟩

end BEDC.Derived.LocatedIntervalBisectionUp
