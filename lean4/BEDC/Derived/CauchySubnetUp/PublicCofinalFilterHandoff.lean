import BEDC.Derived.CauchySubnetUp.EndpointNonescape

namespace BEDC.Derived.CauchySubnetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySubnetCarrier_public_cofinal_filter_handoff [AskSetup] [PackageSetup]
    {F J W R D L E H C P N handoff sealRead cofinalRead endpointRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySubnetCarrier F J W R D L E H C P N bundle pkg →
      Cont D L handoff →
        Cont handoff E sealRead →
          Cont F J cofinalRead →
            Cont cofinalRead E endpointRead →
              Cont endpointRead N publicRead →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
                          hsame row D ∨ hsame row L ∨ hsame row E ∨ hsame row H ∨
                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                              hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont D L handoff ∧
                          Cont handoff E sealRead ∧ Cont F J cofinalRead ∧
                            Cont cofinalRead E endpointRead ∧
                              Cont endpointRead N publicRead ∧
                                PkgSig bundle publicRead pkg)
                      hsame ∧
                    UnaryHistory handoff ∧ UnaryHistory sealRead ∧
                      UnaryHistory cofinalRead ∧ UnaryHistory endpointRead ∧
                        UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: CauchySubnetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier routeHandoff routeSeal routeCofinal routeEndpoint routePublic publicPkg
  obtain ⟨unaryF, unaryJ, _unaryW, _unaryR, unaryD, unaryL, unaryE, _unaryH,
    _unaryC, _unaryP, unaryN, _filterSubnetWindow, _windowReadbackTolerance,
    _toleranceLimitSeal, _sealTransportReplay, _provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed unaryD unaryL routeHandoff
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary unaryE routeSeal
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed unaryF unaryJ routeCofinal
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed cofinalUnary unaryE routeEndpoint
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
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D L handoff ∧ Cont handoff E sealRead ∧
              Cont F J cofinalRead ∧ Cont cofinalRead E endpointRead ∧
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
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeHandoff, routeSeal, routeCofinal, routeEndpoint,
          routePublic, publicPkg⟩
  }
  exact ⟨cert, handoffUnary, sealUnary, cofinalUnary, endpointUnary, publicUnary⟩

end BEDC.Derived.CauchySubnetUp
