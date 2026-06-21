import BEDC.Derived.LocatedSpaceUp.MetricRequestLedger

namespace BEDC.Derived.LocatedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSpaceCarrier_obligation_closure_route [AskSetup] [PackageSetup]
    {X R A G W Q E H C P N requestRead gapRead windowRead readbackRead sealRead ledgerRead
      closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory X ∧ UnaryHistory R ∧ UnaryHistory A ∧ UnaryHistory G ∧
      UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧
        UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg) →
      Cont X R requestRead →
        Cont A G gapRead →
          Cont requestRead W windowRead →
            Cont windowRead Q readbackRead →
              Cont readbackRead E sealRead →
                Cont sealRead N ledgerRead →
                  Cont ledgerRead C closureRead →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row R ∨ hsame row A ∨ hsame row G ∨
                              hsame row W ∨ hsame row Q ∨ hsame row E ∨
                                hsame row sealRead ∨ hsame row ledgerRead ∨
                                  hsame row closureRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont X R requestRead ∧ Cont A G gapRead ∧
                              Cont requestRead W windowRead ∧
                                Cont windowRead Q readbackRead ∧
                                  Cont readbackRead E sealRead ∧ Cont sealRead N ledgerRead ∧
                                    Cont ledgerRead C closureRead ∧ PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory requestRead ∧ UnaryHistory gapRead ∧
                          UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                            UnaryHistory sealRead ∧ UnaryHistory ledgerRead ∧
                              UnaryHistory closureRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro rows requestRoute gapRoute windowRoute readbackRoute sealRoute ledgerRoute closureRoute
    namePkg
  obtain ⟨xUnary, rUnary, aUnary, gUnary, wUnary, qUnary, eUnary, _hUnary, cUnary,
    _pUnary, nUnary, _pPkg⟩ := rows
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed xUnary rUnary requestRoute
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed aUnary gUnary gapRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed requestUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed sealUnary nUnary ledgerRoute
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed ledgerUnary cUnary closureRoute
  have sourceClosure :
      (fun row : BHist => hsame row closureRead ∧ UnaryHistory row) closureRead := by
    exact ⟨hsame_refl closureRead, closureUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row R ∨ hsame row A ∨ hsame row G ∨ hsame row W ∨
              hsame row Q ∨ hsame row E ∨ hsame row sealRead ∨ hsame row ledgerRead ∨
                hsame row closureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X R requestRead ∧ Cont A G gapRead ∧
              Cont requestRead W windowRead ∧ Cont windowRead Q readbackRead ∧
                Cont readbackRead E sealRead ∧ Cont sealRead N ledgerRead ∧
                  Cont ledgerRead C closureRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro closureRead sourceClosure
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, requestRoute, gapRoute, windowRoute, readbackRoute, sealRoute,
          ledgerRoute, closureRoute, namePkg⟩
  }
  exact
    ⟨cert, requestUnary, gapUnary, windowUnary, readbackUnary, sealUnary, ledgerUnary,
      closureUnary⟩

end BEDC.Derived.LocatedSpaceUp
