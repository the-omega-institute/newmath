import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyFilterBasisUp

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

def LocatedCauchyFilterBasisCarrier [AskSetup] [PackageSetup]
    (B L S R D W T E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory B ∧ UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory R ∧
    UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory T ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont B L S ∧ Cont S R D ∧ Cont D W T ∧ Cont T E C ∧
          PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem LocatedCauchyFilterBasisCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {B L S R D W T E H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧ LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N
              bundle pkg)
          (fun row : BHist => hsame row N ∧ Cont B L S ∧ Cont S R D ∧ Cont D W T)
          (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory B ∧ UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory R ∧
          UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory T ∧ UnaryHistory E ∧
            Cont B L S ∧ Cont S R D ∧ Cont D W T ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨bUnary, lUnary, sUnary, rUnary, dUnary, wUnary, tUnary, eUnary,
    hUnary, cUnary, pUnary, nUnary, basisLocated, windowReadback, toleranceWitness,
    tailSeal, provenancePkg, namePkg⟩ := carrier
  have carrierRows :
      LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N bundle pkg :=
    ⟨bUnary, lUnary, sUnary, rUnary, dUnary, wUnary, tUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, basisLocated, windowReadback, toleranceWitness,
      tailSeal, provenancePkg, namePkg⟩
  have sourceName :
      (fun row : BHist =>
        hsame row N ∧ LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N
          bundle pkg) N := by
    exact ⟨hsame_refl N, carrierRows⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row N ∧ LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N
            bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro N sourceName
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧ LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N
              bundle pkg)
          (fun row : BHist => hsame row N ∧ Cont B L S ∧ Cont S R D ∧ Cont D W T)
          (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        exact ⟨source.left, basisLocated, windowReadback, toleranceWitness⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, provenancePkg, namePkg⟩
    }
  exact
    ⟨cert, bUnary, lUnary, sUnary, rUnary, dUnary, wUnary, tUnary, eUnary,
      basisLocated, windowReadback, toleranceWitness, provenancePkg, namePkg⟩

inductive LocatedCauchyFilterBasisUp : Type where
  | mk (B L S R D W T E H C P N : BHist) : LocatedCauchyFilterBasisUp
  deriving DecidableEq

def locatedCauchyFilterBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchyFilterBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchyFilterBasisEncodeBHist h

def locatedCauchyFilterBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchyFilterBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchyFilterBasisDecodeBHist tail)

theorem LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCauchyFilterBasisToEventFlow : LocatedCauchyFilterBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyFilterBasisUp.mk B L S R D W T E H C P N =>
      [locatedCauchyFilterBasisEncodeBHist B,
        locatedCauchyFilterBasisEncodeBHist L,
        locatedCauchyFilterBasisEncodeBHist S,
        locatedCauchyFilterBasisEncodeBHist R,
        locatedCauchyFilterBasisEncodeBHist D,
        locatedCauchyFilterBasisEncodeBHist W,
        locatedCauchyFilterBasisEncodeBHist T,
        locatedCauchyFilterBasisEncodeBHist E,
        locatedCauchyFilterBasisEncodeBHist H,
        locatedCauchyFilterBasisEncodeBHist C,
        locatedCauchyFilterBasisEncodeBHist P,
        locatedCauchyFilterBasisEncodeBHist N]

def locatedCauchyFilterBasisFromEventFlow : EventFlow → Option LocatedCauchyFilterBasisUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | B :: restL =>
      match restL with
      | [] => none
      | L :: restS =>
          match restS with
          | [] => none
          | S :: restR =>
              match restR with
              | [] => none
              | R :: restD =>
                  match restD with
                  | [] => none
                  | D :: restW =>
                      match restW with
                      | [] => none
                      | W :: restT =>
                          match restT with
                          | [] => none
                          | T :: restE =>
                              match restE with
                              | [] => none
                              | E :: restH =>
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
                                                        (LocatedCauchyFilterBasisUp.mk
                                                          (locatedCauchyFilterBasisDecodeBHist B)
                                                          (locatedCauchyFilterBasisDecodeBHist L)
                                                          (locatedCauchyFilterBasisDecodeBHist S)
                                                          (locatedCauchyFilterBasisDecodeBHist R)
                                                          (locatedCauchyFilterBasisDecodeBHist D)
                                                          (locatedCauchyFilterBasisDecodeBHist W)
                                                          (locatedCauchyFilterBasisDecodeBHist T)
                                                          (locatedCauchyFilterBasisDecodeBHist E)
                                                          (locatedCauchyFilterBasisDecodeBHist H)
                                                          (locatedCauchyFilterBasisDecodeBHist C)
                                                          (locatedCauchyFilterBasisDecodeBHist P)
                                                          (locatedCauchyFilterBasisDecodeBHist N))
                                                  | _ :: _ => none

theorem LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCauchyFilterBasisUp,
      locatedCauchyFilterBasisFromEventFlow
        (locatedCauchyFilterBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B L S R D W T E H C P N =>
      change
        some
          (LocatedCauchyFilterBasisUp.mk
            (locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist B))
            (locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist L))
            (locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist S))
            (locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist R))
            (locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist D))
            (locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist W))
            (locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist T))
            (locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist E))
            (locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist H))
            (locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist C))
            (locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist P))
            (locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist N))) =
          some (LocatedCauchyFilterBasisUp.mk B L S R D W T E H C P N)
      rw [LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode B,
        LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode L,
        LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode S,
        LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode R,
        LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode D,
        LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode W,
        LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode T,
        LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode E,
        LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode H,
        LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode C,
        LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode P,
        LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode N]

theorem LocatedCauchyFilterBasisToEventFlow_injective
    {x y : LocatedCauchyFilterBasisUp} :
    locatedCauchyFilterBasisToEventFlow x = locatedCauchyFilterBasisToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCauchyFilterBasisFromEventFlow (locatedCauchyFilterBasisToEventFlow x) =
        locatedCauchyFilterBasisFromEventFlow (locatedCauchyFilterBasisToEventFlow y) :=
    congrArg locatedCauchyFilterBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCauchyFilterBasisBHistCarrier :
    BHistCarrier LocatedCauchyFilterBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchyFilterBasisToEventFlow
  fromEventFlow := locatedCauchyFilterBasisFromEventFlow

instance locatedCauchyFilterBasisChapterTasteGate :
    ChapterTasteGate LocatedCauchyFilterBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCauchyFilterBasisToEventFlow_injective heq)

theorem LocatedCauchyFilterBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedCauchyFilterBasisDecodeBHist (locatedCauchyFilterBasisEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedCauchyFilterBasisUp) ∧
        Nonempty (ChapterTasteGate LocatedCauchyFilterBasisUp) ∧
          locatedCauchyFilterBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedCauchyFilterBasisTasteGate_single_carrier_alignment_decode,
      ⟨locatedCauchyFilterBasisBHistCarrier⟩,
      ⟨locatedCauchyFilterBasisChapterTasteGate⟩,
      rfl⟩

theorem LocatedCauchyFilterBasisCarrier_tail_refinement [AskSetup] [PackageSetup]
    {B L S R D W T E H C P N tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N bundle pkg →
      Cont W T tailRead →
        PkgSig bundle tailRead pkg →
          UnaryHistory B ∧ UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory R ∧
            UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory T ∧ UnaryHistory tailRead ∧
              Cont B L S ∧ Cont S R D ∧ Cont D W T ∧ Cont W T tailRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier tailRoute tailPkg
  obtain ⟨bUnary, lUnary, sUnary, rUnary, dUnary, wUnary, tUnary, _eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, basisLocated, windowReadback,
    toleranceWitness, _tailSeal, provenancePkg, _namePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed wUnary tUnary tailRoute
  exact
    ⟨bUnary, lUnary, sUnary, rUnary, dUnary, wUnary, tUnary, tailUnary,
      basisLocated, windowReadback, toleranceWitness, tailRoute, provenancePkg, tailPkg⟩

theorem LocatedCauchyFilterBasisCarrier_real_seal_handoff [AskSetup] [PackageSetup]
    {B L S R D W T E H C P N tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N bundle pkg ->
      Cont W T tailRead ->
        Cont tailRead E sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row B ∨ hsame row L ∨ hsame row S ∨ hsame row R ∨
                    hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row E ∨
                      hsame row sealRead)
                (fun row : BHist =>
                  hsame row sealRead ∧ Cont W T tailRead ∧
                    Cont tailRead E sealRead ∧ PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory B ∧ UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory R ∧
                UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory T ∧ UnaryHistory E ∧
                  UnaryHistory tailRead ∧ UnaryHistory sealRead ∧ Cont B L S ∧
                    Cont S R D ∧ Cont D W T ∧ Cont W T tailRead ∧
                      Cont tailRead E sealRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier tailRoute sealRoute sealPkg
  obtain ⟨bUnary, lUnary, sUnary, rUnary, dUnary, wUnary, tUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, basisLocated, windowReadback,
    toleranceWitness, _tailSeal, provenancePkg, _namePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed wUnary tUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary eUnary sealRoute
  have sourceAtSeal : hsame sealRead sealRead ∧ UnaryHistory sealRead :=
    ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row L ∨ hsame row S ∨ hsame row R ∨
              hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row E ∨
                hsame row sealRead)
          (fun row : BHist =>
            hsame row sealRead ∧ Cont W T tailRead ∧ Cont tailRead E sealRead ∧
              PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceAtSeal
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, tailRoute, sealRoute, sealPkg⟩
  }
  exact
    ⟨cert, bUnary, lUnary, sUnary, rUnary, dUnary, wUnary, tUnary, eUnary, tailUnary,
      sealUnary, basisLocated, windowReadback, toleranceWitness, tailRoute, sealRoute,
      provenancePkg, sealPkg⟩

theorem LocatedCauchyFilterBasisRealNonescape [AskSetup] [PackageSetup]
    {B L S R D W T E H C P N tailRead sealRead transported replayed namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N bundle pkg ->
      Cont W T tailRead ->
        Cont tailRead E sealRead ->
          Cont sealRead H transported ->
            Cont transported C replayed ->
              Cont replayed N namedRead ->
                PkgSig bundle namedRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row B ∨ hsame row L ∨ hsame row S ∨ hsame row R ∨
                          hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row E ∨
                            hsame row H ∨ hsame row C ∨ hsame row N ∨
                              hsame row namedRead)
                      (fun row : BHist =>
                        hsame row namedRead ∧ Cont W T tailRead ∧
                          Cont tailRead E sealRead ∧ Cont sealRead H transported ∧
                            Cont transported C replayed ∧ Cont replayed N namedRead ∧
                              PkgSig bundle namedRead pkg)
                      hsame ∧
                    UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory transported ∧ UnaryHistory replayed ∧
                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier tailRoute sealRoute transportRoute replayRoute nameRoute namedPkg
  obtain ⟨_bUnary, _lUnary, _sUnary, _rUnary, _dUnary, wUnary, tUnary, eUnary,
    hUnary, cUnary, _pUnary, nUnary, _basisLocated, _windowReadback, _toleranceWitness,
    _tailSeal, _provenancePkg, _namePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed wUnary tUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary eUnary sealRoute
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed sealUnary hUnary transportRoute
  have replayedUnary : UnaryHistory replayed :=
    unary_cont_closed transportedUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayedUnary nUnary nameRoute
  have sourceAtNamed : hsame namedRead namedRead ∧ UnaryHistory namedRead :=
    ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row L ∨ hsame row S ∨ hsame row R ∨
              hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            hsame row namedRead ∧ Cont W T tailRead ∧ Cont tailRead E sealRead ∧
              Cont sealRead H transported ∧ Cont transported C replayed ∧
                Cont replayed N namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceAtNamed
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, tailRoute, sealRoute, transportRoute, replayRoute, nameRoute,
          namedPkg⟩
  }
  exact ⟨cert, tailUnary, sealUnary, transportedUnary, replayedUnary, namedUnary⟩

end BEDC.Derived.LocatedCauchyFilterBasisUp
