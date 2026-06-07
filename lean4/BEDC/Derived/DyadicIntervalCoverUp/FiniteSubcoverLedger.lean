import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverFiniteSubcoverLedger [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead windowRead readbackRead coverRead sealRead
      subcoverRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg) →
      Cont L U endpointRead →
        Cont W Q windowRead →
          Cont windowRead R readbackRead →
            Cont readbackRead V coverRead →
              Cont coverRead A sealRead →
                Cont endpointRead sealRead subcoverRead →
                  Cont subcoverRead N namedRead →
                    PkgSig bundle namedRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                              hsame row V ∨ hsame row W ∨ hsame row Q ∨
                                hsame row A ∨ hsame row endpointRead ∨
                                  hsame row windowRead ∨ hsame row readbackRead ∨
                                    hsame row coverRead ∨ hsame row sealRead ∨
                                      hsame row subcoverRead ∨ hsame row namedRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont L U endpointRead ∧
                              Cont W Q windowRead ∧ Cont windowRead R readbackRead ∧
                                Cont readbackRead V coverRead ∧
                                  Cont coverRead A sealRead ∧
                                    Cont endpointRead sealRead subcoverRead ∧
                                      Cont subcoverRead N namedRead ∧
                                        PkgSig bundle namedRead pkg)
                          hsame ∧ UnaryHistory endpointRead ∧ UnaryHistory windowRead ∧
                        UnaryHistory readbackRead ∧ UnaryHistory coverRead ∧
                          UnaryHistory sealRead ∧ UnaryHistory subcoverRead ∧
                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro surface endpointRoute windowRoute readbackRoute coverRoute sealRoute subcoverRoute
    namedRoute namedPkg
  obtain ⟨unaryL, unaryU, _unaryM, unaryR, unaryV, unaryW, unaryQ, unaryA, _unaryH,
    _unaryC, _unaryP, unaryN, _provenancePkg, _localNamePkg⟩ := surface
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed unaryL unaryU endpointRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryW unaryQ windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary unaryR readbackRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed readbackUnary unaryV coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary unaryA sealRoute
  have subcoverUnary : UnaryHistory subcoverRead :=
    unary_cont_closed endpointUnary sealUnary subcoverRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed subcoverUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row endpointRead ∨
                hsame row windowRead ∨ hsame row readbackRead ∨ hsame row coverRead ∨
                  hsame row sealRead ∨ hsame row subcoverRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont W Q windowRead ∧
              Cont windowRead R readbackRead ∧ Cont readbackRead V coverRead ∧
                Cont coverRead A sealRead ∧ Cont endpointRead sealRead subcoverRead ∧
                  Cont subcoverRead N namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr source.left)))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, windowRoute, readbackRoute, coverRoute,
          sealRoute, subcoverRoute, namedRoute, namedPkg⟩
  }
  exact
    ⟨cert, endpointUnary, windowUnary, readbackUnary, coverUnary, sealUnary,
      subcoverUnary, namedUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
