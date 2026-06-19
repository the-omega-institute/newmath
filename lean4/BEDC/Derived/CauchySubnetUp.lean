import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.CauchySubnetUp.TasteGate

namespace BEDC.Derived.CauchySubnetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySubnetCarrier_cofinal_ledger_coverage
    {filter subnet window readback tolerance limit sealRow transport replay provenance
      localName : BHist} :
    SemanticNameCert
      (fun row : BHist =>
        hsame row localName ∧
          ∃ S : CauchySubnetUp,
            cauchySubnetFields S =
              [filter, subnet, window, readback, tolerance, limit, sealRow, transport,
                replay, provenance, localName])
      (fun row : BHist =>
        hsame row filter ∨ hsame row subnet ∨ hsame row window ∨
          hsame row readback ∨ hsame row tolerance ∨ hsame row limit ∨
            hsame row sealRow ∨ hsame row localName)
      (fun row : BHist =>
        hsame row localName ∧
          cauchySubnetToEventFlow
              (CauchySubnetUp.mk filter subnet window readback tolerance limit sealRow
                transport replay provenance localName) =
            [cauchySubnetEncodeBHist filter, cauchySubnetEncodeBHist subnet,
              cauchySubnetEncodeBHist window, cauchySubnetEncodeBHist readback,
              cauchySubnetEncodeBHist tolerance, cauchySubnetEncodeBHist limit,
              cauchySubnetEncodeBHist sealRow, cauchySubnetEncodeBHist transport,
              cauchySubnetEncodeBHist replay, cauchySubnetEncodeBHist provenance,
              cauchySubnetEncodeBHist localName])
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  let S :=
    CauchySubnetUp.mk filter subnet window readback tolerance limit sealRow transport replay
      provenance localName
  have sourceLocal :
      (fun row : BHist =>
        hsame row localName ∧
          ∃ S : CauchySubnetUp,
            cauchySubnetFields S =
              [filter, subnet, window, readback, tolerance, limit, sealRow, transport,
                replay, provenance, localName]) localName := by
    exact ⟨hsame_refl localName, Exists.intro S rfl⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro localName sourceLocal
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨hsame_refl localName, rfl⟩
  }

def CauchySubnetCarrier [AskSetup] [PackageSetup]
    (filter subnet window readback tolerance limit sealRow transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory filter ∧ UnaryHistory subnet ∧ UnaryHistory window ∧
    UnaryHistory readback ∧ UnaryHistory tolerance ∧ UnaryHistory limit ∧
      UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont filter subnet window ∧
          Cont window readback tolerance ∧ Cont tolerance limit sealRow ∧
            Cont sealRow transport replay ∧ PkgSig bundle provenance pkg

theorem CauchySubnetNameCertObligations [AskSetup] [PackageSetup]
    {F J W R D L E H C P N handoff sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySubnetCarrier F J W R D L E H C P N bundle pkg →
      Cont D L handoff →
        Cont handoff E sealRead →
          PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row N ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
                    hsame row D ∨ hsame row L ∨ hsame row E ∨ hsame row N)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory handoff ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier routeHandoff routeSeal namePkg
  obtain ⟨unaryF, _unaryJ, _unaryW, _unaryR, unaryD, unaryL, unaryE, _unaryH,
    _unaryC, _unaryP, unaryN, _fjw, _wrd, _dle, _ehc, provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed unaryD unaryL routeHandoff
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary unaryE routeSeal
  have sourceN :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryN⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
              hsame row D ∨ hsame row L ∨ hsame row E ∨ hsame row N)
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, handoffUnary, sealUnary⟩

theorem CauchySubnet_obligation_closure_package [AskSetup] [PackageSetup]
    {F J W R D L E H C P N handoff sealRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySubnetCarrier F J W R D L E H C P N bundle pkg →
      Cont D L handoff →
        Cont handoff E sealRead →
          Cont F J endpointRead →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row N ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
                      hsame row D ∨ hsame row L ∨ hsame row E ∨ hsame row N)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory handoff ∧ UnaryHistory sealRead ∧
                  UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: CauchySubnetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier routeHandoff routeSeal endpointRoute namePkg
  obtain ⟨unaryF, unaryJ, _unaryW, _unaryR, unaryD, unaryL, unaryE, _unaryH,
    _unaryC, _unaryP, unaryN, _fjw, _wrd, _dle, _ehc, provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed unaryD unaryL routeHandoff
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary unaryE routeSeal
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed unaryF unaryJ endpointRoute
  have sourceN :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryN⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
              hsame row D ∨ hsame row L ∨ hsame row E ∨ hsame row N)
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, handoffUnary, sealUnary, endpointUnary⟩

theorem CauchySubnet_filter_limit_handoff [AskSetup] [PackageSetup]
    {filter subnet window readback tolerance limit sealRow transport replay provenance localName
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySubnetCarrier filter subnet window readback tolerance limit sealRow transport replay
        provenance localName bundle pkg →
      Cont limit sealRow handoffRead →
        PkgSig bundle handoffRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row filter ∨ hsame row subnet ∨ hsame row window ∨
                  hsame row readback ∨ hsame row tolerance ∨ hsame row limit ∨
                    hsame row sealRow ∨ hsame row handoffRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont limit sealRow handoffRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg)
              hsame ∧
            UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: CauchySubnetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier limitSealHandoff handoffPkg
  obtain ⟨_filterUnary, _subnetUnary, _windowUnary, _readbackUnary, _toleranceUnary,
    limitUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _filterSubnetWindow, _windowReadbackTolerance, _toleranceLimitSeal,
    _sealTransportReplay, provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed limitUnary sealUnary limitSealHandoff
  have sourceHandoff :
      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row) handoffRead := by
    exact ⟨hsame_refl handoffRead, handoffUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row subnet ∨ hsame row window ∨
              hsame row readback ∨ hsame row tolerance ∨ hsame row limit ∨
                hsame row sealRow ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont limit sealRow handoffRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceHandoff
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, limitSealHandoff, provenancePkg, handoffPkg⟩
  }
  exact ⟨cert, handoffUnary⟩

theorem CauchySubnet_cofinal_ledger_coverage [AskSetup] [PackageSetup]
    {filter subnet window readback tolerance limit sealRow transport replay provenance
      localName cofinalRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySubnetCarrier filter subnet window readback tolerance limit sealRow transport replay
        provenance localName bundle pkg →
      Cont filter subnet cofinalRead →
        Cont cofinalRead limit endpointRead →
          PkgSig bundle endpointRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row filter ∨ hsame row subnet ∨ hsame row cofinalRead ∨
                    hsame row limit ∨ hsame row endpointRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont filter subnet cofinalRead ∧
                    Cont cofinalRead limit endpointRead ∧ PkgSig bundle endpointRead pkg)
                hsame ∧
              UnaryHistory cofinalRead ∧ UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: CauchySubnetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier cofinalRoute endpointRoute endpointPkg
  obtain ⟨filterUnary, subnetUnary, _windowUnary, _readbackUnary, _toleranceUnary,
    limitUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _filterSubnetWindow, _windowReadbackTolerance, _toleranceLimitSeal,
    _sealTransportReplay, _provenancePkg⟩ := carrier
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed filterUnary subnetUnary cofinalRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed cofinalUnary limitUnary endpointRoute
  have sourceEndpoint :
      (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row) endpointRead := by
    exact ⟨hsame_refl endpointRead, endpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row subnet ∨ hsame row cofinalRead ∨
              hsame row limit ∨ hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont filter subnet cofinalRead ∧
              Cont cofinalRead limit endpointRead ∧ PkgSig bundle endpointRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointRead sourceEndpoint
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, cofinalRoute, endpointRoute, endpointPkg⟩
  }
  exact ⟨cert, cofinalUnary, endpointUnary⟩

theorem CauchySubnetCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {F J W R D L E H C P N handoff sealRead cofinalRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySubnetCarrier F J W R D L E H C P N bundle pkg →
      Cont D L handoff →
        Cont handoff E sealRead →
          Cont F J cofinalRead →
            Cont cofinalRead L endpointRead →
              PkgSig bundle N pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row sealRead ∨ hsame row endpointRead ∨ hsame row N) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
                        hsame row D ∨ hsame row L ∨ hsame row E ∨
                          hsame row sealRead ∨ hsame row endpointRead ∨ hsame row N)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont D L handoff ∧
                        Cont handoff E sealRead ∧ Cont F J cofinalRead ∧
                          Cont cofinalRead L endpointRead ∧ PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory handoff ∧ UnaryHistory sealRead ∧
                    UnaryHistory cofinalRead ∧ UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: CauchySubnetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier routeHandoff routeSeal routeCofinal routeEndpoint namePkg
  obtain ⟨filterUnary, cofinalUnaryBase, _windowUnary, _readbackUnary, toleranceUnary,
    limitUnary, sealBaseUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, _filterSubnetWindow, _windowReadbackTolerance, _toleranceLimitSeal,
    _sealTransportReplay, _provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed toleranceUnary limitUnary routeHandoff
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary sealBaseUnary routeSeal
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed filterUnary cofinalUnaryBase routeCofinal
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed cofinalUnary limitUnary routeEndpoint
  have sourceN :
      (fun row : BHist =>
          (hsame row sealRead ∨ hsame row endpointRead ∨ hsame row N) ∧
            UnaryHistory row) N := by
    exact ⟨Or.inr (Or.inr (hsame_refl N)), localNameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sealRead ∨ hsame row endpointRead ∨ hsame row N) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
              hsame row D ∨ hsame row L ∨ hsame row E ∨
                hsame row sealRead ∨ hsame row endpointRead ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D L handoff ∧ Cont handoff E sealRead ∧
              Cont F J cofinalRead ∧ Cont cofinalRead L endpointRead ∧
                PkgSig bundle N pkg)
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
        intro row other sameRows source
        constructor
        · cases source.left with
          | inl sameSeal =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSeal)
          | inr rest =>
              cases rest with
              | inl sameEndpoint =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameEndpoint))
              | inr sameName =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameName))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSeal =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inl sameSeal)))))))
      | inr rest =>
          cases rest with
          | inl sameEndpoint =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl sameEndpoint))))))))
          | inr sameName =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr sameName))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeHandoff, routeSeal, routeCofinal, routeEndpoint, namePkg⟩
  }
  exact ⟨cert, handoffUnary, sealUnary, cofinalUnary, endpointUnary⟩

end BEDC.Derived.CauchySubnetUp
