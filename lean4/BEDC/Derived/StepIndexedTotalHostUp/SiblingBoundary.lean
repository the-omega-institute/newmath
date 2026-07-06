import BEDC.Derived.StepIndexedTotalHostUp

namespace BEDC.Derived.StepIndexedTotalHostUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StepIndexedTotalHostCarrier_public_sibling_boundary [AskSetup] [PackageSetup]
    {host fuel trace normal bounded refusal transport route provenance nameCert boundaryRead
      namedRead publicRead sibling : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StepIndexedTotalHostCarrier host fuel trace normal bounded refusal transport route
        provenance nameCert bundle pkg →
      Cont normal refusal boundaryRead →
        Cont boundaryRead nameCert namedRead →
          Cont namedRead route publicRead →
            Cont publicRead bounded sibling →
              PkgSig bundle namedRead pkg →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row host ∨ hsame row fuel ∨ hsame row trace ∨
                          hsame row normal ∨ hsame row bounded ∨ hsame row refusal ∨
                            hsame row transport ∨ hsame row route ∨
                              hsame row boundaryRead ∨ hsame row namedRead ∨
                                hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont host fuel trace ∧
                          Cont trace bounded normal ∧ Cont refusal transport route ∧
                            Cont normal refusal boundaryRead ∧
                              Cont boundaryRead nameCert namedRead ∧
                                Cont namedRead route publicRead ∧
                                  PkgSig bundle publicRead pkg)
                      hsame ∧
                    UnaryHistory publicRead ∧ UnaryHistory bounded ∧
                      UnaryHistory sibling ∧ Cont publicRead bounded sibling ∧
                        PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: StepIndexedTotalHostCarrier SemanticNameCert BHist Cont PkgSig UnaryHistory
  intro carrier boundaryRoute namedRoute publicRoute siblingRoute namedPkg publicPkg
  have publicResult :=
    StepIndexedTotalHostCarrier_public_interface carrier boundaryRoute namedRoute publicRoute
      namedPkg publicPkg
  have siblingUnary : UnaryHistory sibling :=
    unary_cont_closed publicResult.right carrier.bounded_unary siblingRoute
  exact
    ⟨publicResult.left, publicResult.right, carrier.bounded_unary, siblingUnary,
      siblingRoute, publicPkg⟩

theorem StepIndexedTotalHostCarrier_bounded_sibling_boundary [AskSetup] [PackageSetup]
    {host fuel trace normal bounded refusal transport route provenance nameCert boundaryRead
      namedRead publicRead sibling : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StepIndexedTotalHostCarrier host fuel trace normal bounded refusal transport route
        provenance nameCert bundle pkg →
      Cont normal refusal boundaryRead →
        Cont boundaryRead nameCert namedRead →
          Cont namedRead route publicRead →
            Cont publicRead bounded sibling →
              PkgSig bundle namedRead pkg →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sibling ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row host ∨ hsame row fuel ∨ hsame row trace ∨
                          hsame row normal ∨ hsame row bounded ∨ hsame row refusal ∨
                            hsame row transport ∨ hsame row route ∨
                              hsame row boundaryRead ∨ hsame row namedRead ∨
                                hsame row publicRead ∨ hsame row sibling)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont host fuel trace ∧
                          Cont trace bounded normal ∧ Cont refusal transport route ∧
                            Cont normal refusal boundaryRead ∧
                              Cont boundaryRead nameCert namedRead ∧
                                Cont namedRead route publicRead ∧
                                  Cont publicRead bounded sibling ∧
                                    PkgSig bundle publicRead pkg)
                      hsame ∧
                    UnaryHistory publicRead ∧ UnaryHistory bounded ∧ UnaryHistory sibling := by
  -- BEDC touchpoint anchor: StepIndexedTotalHostCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute namedRoute publicRoute siblingRoute namedPkg publicPkg
  have publicResult :=
    StepIndexedTotalHostCarrier_public_interface carrier boundaryRoute namedRoute publicRoute
      namedPkg publicPkg
  have publicUnary : UnaryHistory publicRead := publicResult.right
  have siblingUnary : UnaryHistory sibling :=
    unary_cont_closed publicUnary carrier.bounded_unary siblingRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sibling ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row host ∨ hsame row fuel ∨ hsame row trace ∨ hsame row normal ∨
              hsame row bounded ∨ hsame row refusal ∨ hsame row transport ∨
                hsame row route ∨ hsame row boundaryRead ∨ hsame row namedRead ∨
                  hsame row publicRead ∨ hsame row sibling)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont host fuel trace ∧ Cont trace bounded normal ∧
              Cont refusal transport route ∧ Cont normal refusal boundaryRead ∧
                Cont boundaryRead nameCert namedRead ∧ Cont namedRead route publicRead ∧
                  Cont publicRead bounded sibling ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sibling ⟨hsame_refl sibling, siblingUnary⟩
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
        ⟨source.right, carrier.host_fuel_trace, carrier.trace_bounded_normal,
          carrier.refusal_transport_route, boundaryRoute, namedRoute, publicRoute,
          siblingRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary, carrier.bounded_unary, siblingUnary⟩

end BEDC.Derived.StepIndexedTotalHostUp
