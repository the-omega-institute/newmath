import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyLocatedLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyLocatedLimitNameCertObligations [AskSetup] [PackageSetup]
    {window dyadic readback interval locator realSeal transport replay provenance localName
      windowDyadicRead readbackRead intervalRead locatorRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory window →
      UnaryHistory dyadic →
        UnaryHistory readback →
          UnaryHistory interval →
            UnaryHistory locator →
              UnaryHistory realSeal →
                UnaryHistory localName →
                  Cont window dyadic windowDyadicRead →
                    Cont windowDyadicRead readback readbackRead →
                      Cont readbackRead interval intervalRead →
                        Cont intervalRead locator locatorRead →
                          Cont locatorRead realSeal sealRead →
                            Cont sealRead localName namedRead →
                              PkgSig bundle provenance pkg →
                                PkgSig bundle namedRead pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row window ∨ hsame row dyadic ∨
                                          hsame row readback ∨ hsame row interval ∨
                                            hsame row locator ∨ hsame row realSeal ∨
                                              hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧
                                          Cont window dyadic windowDyadicRead ∧
                                            Cont windowDyadicRead readback readbackRead ∧
                                              Cont readbackRead interval intervalRead ∧
                                                Cont intervalRead locator locatorRead ∧
                                                  Cont locatorRead realSeal sealRead ∧
                                                    Cont sealRead localName namedRead ∧
                                                      PkgSig bundle provenance pkg ∧
                                                        PkgSig bundle namedRead pkg)
                                      hsame ∧
                                    UnaryHistory windowDyadicRead ∧
                                      UnaryHistory readbackRead ∧
                                        UnaryHistory intervalRead ∧
                                          UnaryHistory locatorRead ∧
                                            UnaryHistory sealRead ∧
                                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: RegularCauchyLocatedLimitUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro windowUnary dyadicUnary readbackUnary intervalUnary locatorUnary realSealUnary
    localNameUnary windowDyadicRoute readbackRoute intervalRoute locatorRoute sealRoute
    namedRoute provenancePkg namedPkg
  have windowDyadicUnary : UnaryHistory windowDyadicRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowDyadicUnary readbackUnary readbackRoute
  have intervalReadUnary : UnaryHistory intervalRead :=
    unary_cont_closed readbackReadUnary intervalUnary intervalRoute
  have locatorReadUnary : UnaryHistory locatorRead :=
    unary_cont_closed intervalReadUnary locatorUnary locatorRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed locatorReadUnary realSealUnary sealRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed sealReadUnary localNameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row window ∨ hsame row dyadic ∨ hsame row readback ∨
              hsame row interval ∨ hsame row locator ∨ hsame row realSeal ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont window dyadic windowDyadicRead ∧
              Cont windowDyadicRead readback readbackRead ∧
                Cont readbackRead interval intervalRead ∧
                  Cont intervalRead locator locatorRead ∧
                    Cont locatorRead realSeal sealRead ∧
                      Cont sealRead localName namedRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowDyadicRoute, readbackRoute, intervalRoute, locatorRoute,
          sealRoute, namedRoute, provenancePkg, namedPkg⟩
  }
  exact
    ⟨cert, windowDyadicUnary, readbackReadUnary, intervalReadUnary, locatorReadUnary,
      sealReadUnary, namedReadUnary⟩

end BEDC.Derived.RegularCauchyLocatedLimitUp
