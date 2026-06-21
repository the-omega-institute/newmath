import BEDC.Derived.CompactIntervalFixedPointUp.PublicSeal
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CompactIntervalFixedPointUp.ResidualModulusReadback

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactIntervalFixedPointResidualModulusReadback [AskSetup] [PackageSetup]
    {J G R B W Q E H C P N residualRead bisectionRead windowRead readbackRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactIntervalFixedPointCarrier J G R B W Q E H C P N bundle pkg →
      Cont G R residualRead →
        Cont residualRead B bisectionRead →
          Cont bisectionRead W windowRead →
            Cont windowRead Q readbackRead →
              Cont readbackRead E sealRead →
                PkgSig bundle sealRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row sealRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                      (fun row : BHist =>
                        hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row B ∨
                          hsame row W ∨ hsame row Q ∨ hsame row E ∨
                            hsame row residualRead ∨ hsame row sealRead)
                      (fun row : BHist =>
                        hsame row sealRead ∧ Cont G R residualRead ∧
                          Cont residualRead B bisectionRead ∧
                            Cont bisectionRead W windowRead ∧
                              Cont windowRead Q readbackRead ∧
                                Cont readbackRead E sealRead ∧
                                  PkgSig bundle sealRead pkg)
                      hsame ∧
                    UnaryHistory residualRead ∧ UnaryHistory bisectionRead ∧
                      UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier residualRoute bisectionRoute windowRoute readbackRoute sealRoute sealPkg
  obtain ⟨_jUnary, gUnary, rUnary, bUnary, wUnary, qUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _provenancePkg, _namePkg, _packetWitness⟩ := carrier
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed gUnary rUnary residualRoute
  have bisectionUnary : UnaryHistory bisectionRead :=
    unary_cont_closed residualUnary bUnary bisectionRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bisectionUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row ∧
        PkgSig bundle row pkg) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary, sealPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row sealRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row B ∨
              hsame row W ∨ hsame row Q ∨ hsame row E ∨ hsame row residualRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            hsame row sealRead ∧ Cont G R residualRead ∧
              Cont residualRead B bisectionRead ∧ Cont bisectionRead W windowRead ∧
                Cont windowRead Q readbackRead ∧ Cont readbackRead E sealRead ∧
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
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr sourceRow.left)))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, residualRoute, bisectionRoute, windowRoute, readbackRoute,
          sealRoute, sealPkg⟩
  }
  exact
    ⟨cert, residualUnary, bisectionUnary, windowUnary, readbackUnary, sealUnary⟩

end BEDC.Derived.CompactIntervalFixedPointUp.ResidualModulusReadback
