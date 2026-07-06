import BEDC.Derived.DirectedSubnetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DirectedSubnetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DirectedSubnetCarrier [AskSetup] [PackageSetup]
    (I J phi K L S R D A H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory I ∧ UnaryHistory J ∧ UnaryHistory phi ∧ UnaryHistory K ∧
    UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧
      UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem DirectedSubnetNameCertObligations [AskSetup] [PackageSetup]
    {I J phi K L S R D A H C P N targetRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirectedSubnetCarrier I J phi K L S R D A H C P N bundle pkg →
      Cont K phi targetRead →
        Cont targetRead A sealRead →
          PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row N ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row I ∨ hsame row J ∨ hsame row phi ∨ hsame row K ∨
                    hsame row L ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                      hsame row A ∨ hsame row N)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory targetRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier routeTarget routeSeal namePkg
  obtain ⟨_unaryI, _unaryJ, unaryPhi, unaryK, _unaryL, _unaryS, _unaryR,
    _unaryD, unaryA, _unaryH, _unaryC, _unaryP, unaryN, provenancePkg,
    _carrierNamePkg⟩ := carrier
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed unaryK unaryPhi routeTarget
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed targetUnary unaryA routeSeal
  have sourceN :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryN⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row J ∨ hsame row phi ∨ hsame row K ∨
              hsame row L ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                hsame row A ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceN
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, targetUnary, sealUnary⟩

theorem DirectedSubnetTargetCauchyWindow [AskSetup] [PackageSetup]
    {I J phi K L S R D A H C P N targetRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirectedSubnetCarrier I J phi K L S R D A H C P N bundle pkg →
      Cont J phi targetRead →
        Cont targetRead L sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row J ∨ hsame row phi ∨ hsame row L ∨ hsame row S ∨
                    hsame row R ∨ hsame row D ∨ hsame row A ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont J phi targetRead ∧
                    Cont targetRead L sealRead ∧ PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory targetRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier targetRoute sealRoute sealPkg
  obtain ⟨_unaryI, unaryJ, unaryPhi, _unaryK, unaryL, _unaryS, _unaryR,
    _unaryD, _unaryA, _unaryH, _unaryC, _unaryP, _unaryN, _provenancePkg,
    _namePkg⟩ := carrier
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed unaryJ unaryPhi targetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed targetUnary unaryL sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row J ∨ hsame row phi ∨ hsame row L ∨ hsame row S ∨
              hsame row R ∨ hsame row D ∨ hsame row A ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J phi targetRead ∧
              Cont targetRead L sealRead ∧ PkgSig bundle sealRead pkg)
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, targetRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, targetUnary, sealUnary⟩

theorem DirectedSubnetObligationRoute [AskSetup] [PackageSetup]
    {I J phi K L S R D A H C P N targetRead sealRead obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirectedSubnetCarrier I J phi K L S R D A H C P N bundle pkg →
      Cont J phi targetRead →
        Cont targetRead L sealRead →
          Cont sealRead N obligationRead →
            PkgSig bundle obligationRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row I ∨ hsame row J ∨ hsame row phi ∨ hsame row K ∨
                      hsame row L ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                        hsame row A ∨ hsame row obligationRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont J phi targetRead ∧
                      Cont targetRead L sealRead ∧ Cont sealRead N obligationRead ∧
                        PkgSig bundle obligationRead pkg)
                  hsame ∧
                UnaryHistory targetRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory obligationRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier targetRoute sealRoute obligationRoute obligationPkg
  obtain ⟨_unaryI, unaryJ, unaryPhi, _unaryK, unaryL, _unaryS, _unaryR,
    _unaryD, _unaryA, _unaryH, _unaryC, _unaryP, unaryN, _provenancePkg,
    _namePkg⟩ := carrier
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed unaryJ unaryPhi targetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed targetUnary unaryL sealRoute
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed sealUnary unaryN obligationRoute
  have sourceObligation :
      (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row) obligationRead := by
    exact ⟨hsame_refl obligationRead, obligationUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row J ∨ hsame row phi ∨ hsame row K ∨
              hsame row L ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                hsame row A ∨ hsame row obligationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J phi targetRead ∧ Cont targetRead L sealRead ∧
              Cont sealRead N obligationRead ∧ PkgSig bundle obligationRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obligationRead sourceObligation
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, targetRoute, sealRoute, obligationRoute, obligationPkg⟩
  }
  exact ⟨cert, targetUnary, sealUnary, obligationUnary⟩

theorem DirectedSubnetCarrier_cauchynet_handoff [AskSetup] [PackageSetup]
    {I J phi K L S R D A H C P N targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirectedSubnetCarrier I J phi K L S R D A H C P N bundle pkg →
      Cont K phi targetRead →
        UnaryHistory targetRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig
  intro carrier route
  obtain ⟨_unaryI, _unaryJ, unaryPhi, unaryK, _unaryL, _unaryS, _unaryR,
    _unaryD, _unaryA, _unaryH, _unaryC, _unaryP, _unaryN, provenancePkg,
    namePkg⟩ := carrier
  exact ⟨unary_cont_closed unaryK unaryPhi route, provenancePkg, namePkg⟩

theorem DirectedSubnetCofinalReplay [AskSetup] [PackageSetup]
    {I J phi K L S R D A H C P N targetRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirectedSubnetCarrier I J phi K L S R D A H C P N bundle pkg →
      Cont J phi targetRead →
        Cont targetRead I replayRead →
          PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row I ∨ hsame row J ∨ hsame row phi ∨ hsame row K ∨
                    hsame row L ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                      hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row targetRead ∨ hsame row replayRead)
                (fun row : BHist =>
                  hsame row replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory targetRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: DirectedSubnetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier targetRoute replayRoute namePkg
  obtain ⟨sourceUnary, targetUnary, mapUnary, _sourceCauchyUnary, _targetCauchyUnary,
    _windowUnary, _readbackUnary, _toleranceUnary, _sealUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, provenancePkg, _carrierNamePkg⟩ :=
    carrier
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed targetUnary mapUnary targetRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed targetReadUnary sourceUnary replayRoute
  have sourceReplay :
      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row) replayRead := by
    exact ⟨hsame_refl replayRead, replayReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row J ∨ hsame row phi ∨ hsame row K ∨
              hsame row L ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row targetRead ∨ hsame row replayRead)
          (fun row : BHist =>
            hsame row replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead sourceReplay
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, namePkg⟩
  }
  exact ⟨cert, targetReadUnary, replayReadUnary⟩

theorem DirectedSubnetTargetFilterNonescape [AskSetup] [PackageSetup]
    {I J Phi K L S R D A H C P N filterRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirectedSubnetCarrier I J Phi K L S R D A H C P N bundle pkg →
      Cont Phi K filterRead →
        Cont filterRead L targetRead →
          PkgSig bundle targetRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row I ∨ hsame row J ∨ hsame row Phi ∨ hsame row K ∨
                    hsame row L ∨ hsame row targetRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Phi K filterRead ∧
                    Cont filterRead L targetRead ∧ PkgSig bundle targetRead pkg)
                hsame ∧
              UnaryHistory filterRead ∧ UnaryHistory targetRead := by
  -- BEDC touchpoint anchor: DirectedSubnetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier filterRoute targetRoute targetPkg
  obtain ⟨_unaryI, _unaryJ, unaryPhi, unaryK, unaryL, _unaryS, _unaryR,
    _unaryD, _unaryA, _unaryH, _unaryC, _unaryP, _unaryN, _provenancePkg,
    _namePkg⟩ := carrier
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed unaryPhi unaryK filterRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed filterUnary unaryL targetRoute
  have sourceTarget :
      (fun row : BHist => hsame row targetRead ∧ UnaryHistory row) targetRead := by
    exact ⟨hsame_refl targetRead, targetUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row J ∨ hsame row Phi ∨ hsame row K ∨
              hsame row L ∨ hsame row targetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Phi K filterRead ∧
              Cont filterRead L targetRead ∧ PkgSig bundle targetRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro targetRead sourceTarget
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
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, filterRoute, targetRoute, targetPkg⟩
  }
  exact ⟨cert, filterUnary, targetUnary⟩

theorem DirectedSubnetPublicNameCertExport [AskSetup] [PackageSetup]
    {I J phi K L S R D A H C P N targetRead sealRead obligationRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirectedSubnetCarrier I J phi K L S R D A H C P N bundle pkg →
      Cont J phi targetRead →
        Cont targetRead L sealRead →
          Cont sealRead N obligationRead →
            Cont obligationRead P publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row I ∨ hsame row J ∨ hsame row phi ∨ hsame row K ∨
                        hsame row L ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                          hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont J phi targetRead ∧
                        Cont targetRead L sealRead ∧ Cont sealRead N obligationRead ∧
                          Cont obligationRead P publicRead ∧ PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: DirectedSubnetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier targetRoute sealRoute obligationRoute publicRoute publicPkg
  obtain ⟨_unaryI, unaryJ, unaryPhi, _unaryK, unaryL, _unaryS, _unaryR,
    _unaryD, _unaryA, _unaryH, _unaryC, unaryP, unaryN, _provenancePkg,
    _namePkg⟩ := carrier
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed unaryJ unaryPhi targetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed targetUnary unaryL sealRoute
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed sealUnary unaryN obligationRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed obligationUnary unaryP publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row J ∨ hsame row phi ∨ hsame row K ∨
              hsame row L ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J phi targetRead ∧
              Cont targetRead L sealRead ∧ Cont sealRead N obligationRead ∧
                Cont obligationRead P publicRead ∧ PkgSig bundle publicRead pkg)
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, targetRoute, sealRoute, obligationRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.DirectedSubnetUp
