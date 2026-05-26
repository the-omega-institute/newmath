import BEDC.Derived.BoundedSetUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedSetCarrier [AskSetup] [PackageSetup]
    (X S center radius ball transport replay provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  UnaryHistory X ∧ UnaryHistory S ∧ UnaryHistory center ∧ UnaryHistory radius ∧
    UnaryHistory ball ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧
        Cont S center transport ∧ Cont transport radius replay ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg

theorem BoundedSetCarrier_ball_containment_route [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow memberRead ballRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont S center memberRead ->
        Cont memberRead radius ballRead ->
          PkgSig bundle ballRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row ballRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row ball ∨ hsame row ballRead ∨ Cont memberRead radius ballRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle ballRead pkg ∧ hsame row ballRead)
                hsame ∧
              UnaryHistory memberRead ∧ UnaryHistory ballRead ∧ Cont S center memberRead ∧
                Cont memberRead radius ballRead ∧ PkgSig bundle ballRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier subsetCenter memberRadius ballPkg
  obtain ⟨_xUnary, sUnary, centerUnary, radiusUnary, _ballUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have memberUnary : UnaryHistory memberRead :=
    unary_cont_closed sUnary centerUnary subsetCenter
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed memberUnary radiusUnary memberRadius
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ballRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row ball ∨ hsame row ballRead ∨ Cont memberRead radius ballRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle ballRead pkg ∧ hsame row ballRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ballRead ⟨hsame_refl ballRead, ballReadUnary⟩
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
        have otherSame : hsame other ballRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, ballPkg, source.left⟩
  }
  exact ⟨cert, memberUnary, ballReadUnary, subsetCenter, memberRadius, ballPkg⟩

theorem BoundedSetCarrier_real_bound_nonescape [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      UnaryHistory radius ∧ Cont transport radius replay ∧ PkgSig bundle provenance pkg ∧
        PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier
  obtain ⟨_xUnary, _sUnary, _centerUnary, radiusUnary, _ballUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, carrierBoundRoute,
    provenancePkg, namePkg⟩ := carrier
  exact ⟨radiusUnary, carrierBoundRoute, provenancePkg, namePkg⟩

theorem BoundedSetCarrier_finite_net_consumer_boundary [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow finiteNetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont ball replay finiteNetRead ->
        PkgSig bundle finiteNetRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row finiteNetRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row S ∨ hsame row ball ∨
                  Cont ball replay finiteNetRead)
              (fun row : BHist => PkgSig bundle finiteNetRead pkg ∧ hsame row finiteNetRead)
              hsame ∧
            UnaryHistory finiteNetRead ∧ Cont ball replay finiteNetRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle finiteNetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier ballReplayFinite finiteNetPkg
  obtain ⟨_xUnary, _sUnary, _centerUnary, _radiusUnary, ballUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed ballUnary replayUnary ballReplayFinite
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finiteNetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row ball ∨ Cont ball replay finiteNetRead)
          (fun row : BHist => PkgSig bundle finiteNetRead pkg ∧ hsame row finiteNetRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro finiteNetRead
        ⟨hsame_refl finiteNetRead, finiteNetUnary⟩
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
        have otherSame : hsame other finiteNetRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr ballReplayFinite))
    ledger_sound := by
      intro _row source
      exact ⟨finiteNetPkg, source.left⟩
  }
  exact ⟨cert, finiteNetUnary, ballReplayFinite, provenancePkg, finiteNetPkg⟩

end BEDC.Derived.BoundedSetUp
