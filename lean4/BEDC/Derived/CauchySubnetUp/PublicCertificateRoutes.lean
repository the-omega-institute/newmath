import BEDC.Derived.CauchySubnetUp

namespace BEDC.Derived.CauchySubnetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySubnetCarrier_regseqrat_tail_handoff [AskSetup] [PackageSetup]
    {F J W R D L E H C P N tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySubnetCarrier F J W R D L E H C P N bundle pkg →
      Cont W R tailRead →
        Cont tailRead E sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
                    hsame row D ∨ hsame row L ∨ hsame row E ∨ hsame row H ∨
                      hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row tailRead ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont W R tailRead ∧ Cont tailRead E sealRead ∧
                    PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory tailRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchySubnetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier routeTail routeSeal sealPkg
  obtain ⟨_unaryF, _unaryJ, unaryW, unaryR, _unaryD, _unaryL, unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, _filterSubnetWindow, _windowReadbackTolerance,
    _toleranceLimitSeal, _sealTransportReplay, _provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed unaryW unaryR routeTail
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary unaryE routeSeal
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
              hsame row D ∨ hsame row L ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row tailRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R tailRead ∧ Cont tailRead E sealRead ∧
              PkgSig bundle sealRead pkg)
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
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeTail, routeSeal, sealPkg⟩
  }
  exact ⟨cert, tailUnary, sealUnary⟩

theorem CauchySubnetCarrier_public_certificate_route [AskSetup] [PackageSetup]
    {F J W R D L E H C P N cofinalRead endpointRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySubnetCarrier F J W R D L E H C P N bundle pkg →
      Cont F J cofinalRead →
        Cont cofinalRead L endpointRead →
          Cont endpointRead N publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
                      hsame row D ∨ hsame row L ∨ hsame row E ∨ hsame row H ∨
                        hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row cofinalRead ∨ hsame row endpointRead ∨
                            hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont F J cofinalRead ∧
                      Cont cofinalRead L endpointRead ∧ Cont endpointRead N publicRead ∧
                        PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory cofinalRead ∧ UnaryHistory endpointRead ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: CauchySubnetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier routeCofinal routeEndpoint routePublic publicPkg
  obtain ⟨unaryF, unaryJ, _unaryW, _unaryR, _unaryD, unaryL, _unaryE, _unaryH,
    _unaryC, _unaryP, unaryN, _filterSubnetWindow, _windowReadbackTolerance,
    _toleranceLimitSeal, _sealTransportReplay, _provenancePkg⟩ := carrier
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed unaryF unaryJ routeCofinal
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed cofinalUnary unaryL routeEndpoint
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary unaryN routePublic
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
              hsame row D ∨ hsame row L ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row cofinalRead ∨ hsame row endpointRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F J cofinalRead ∧ Cont cofinalRead L endpointRead ∧
              Cont endpointRead N publicRead ∧ PkgSig bundle publicRead pkg)
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
      exact ⟨source.right, routeCofinal, routeEndpoint, routePublic, publicPkg⟩
  }
  exact ⟨cert, cofinalUnary, endpointUnary, publicUnary⟩

end BEDC.Derived.CauchySubnetUp
