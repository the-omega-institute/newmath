import BEDC.Derived.CauchySubnetUp

namespace BEDC.Derived.CauchySubnetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySubnetCofinalReindexingRoute [AskSetup] [PackageSetup]
    {F J W R D L E H C P N cofinalRead windowRead readbackRead toleranceRead limitRead
      endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySubnetCarrier F J W R D L E H C P N bundle pkg →
      Cont F J cofinalRead →
        Cont cofinalRead W windowRead →
          Cont windowRead R readbackRead →
            Cont readbackRead D toleranceRead →
              Cont toleranceRead L limitRead →
                Cont limitRead E endpointRead →
                  PkgSig bundle endpointRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
                            hsame row D ∨ hsame row L ∨ hsame row E ∨
                              hsame row endpointRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont F J cofinalRead ∧
                            Cont cofinalRead W windowRead ∧
                              Cont windowRead R readbackRead ∧
                                Cont readbackRead D toleranceRead ∧
                                  Cont toleranceRead L limitRead ∧
                                    Cont limitRead E endpointRead ∧
                                      PkgSig bundle endpointRead pkg)
                        hsame ∧
                      UnaryHistory cofinalRead ∧ UnaryHistory windowRead ∧
                        UnaryHistory readbackRead ∧ UnaryHistory toleranceRead ∧
                          UnaryHistory limitRead ∧ UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: CauchySubnetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier cofinalRoute windowRoute readbackRoute toleranceRoute limitRoute
    endpointRoute endpointPkg
  obtain ⟨unaryF, unaryJ, unaryW, unaryR, unaryD, unaryL, unaryE, _unaryH, _unaryC,
    _unaryP, _unaryN, _filterSubnetWindow, _windowReadbackTolerance,
    _toleranceLimitSeal, _sealTransportReplay, _provenancePkg⟩ := carrier
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed unaryF unaryJ cofinalRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed cofinalUnary unaryW windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary unaryR readbackRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackUnary unaryD toleranceRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed toleranceUnary unaryL limitRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed limitUnary unaryE endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
              hsame row L ∨ hsame row E ∨ hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F J cofinalRead ∧ Cont cofinalRead W windowRead ∧
              Cont windowRead R readbackRead ∧ Cont readbackRead D toleranceRead ∧
                Cont toleranceRead L limitRead ∧ Cont limitRead E endpointRead ∧
                  PkgSig bundle endpointRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, cofinalRoute, windowRoute, readbackRoute, toleranceRoute, limitRoute,
          endpointRoute, endpointPkg⟩
  }
  exact
    ⟨cert, cofinalUnary, windowUnary, readbackUnary, toleranceUnary, limitUnary,
      endpointUnary⟩

end BEDC.Derived.CauchySubnetUp
