import BEDC.Derived.CalculusUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusIntegralSumObligation [AskSetup] [PackageSetup]
    {realRow graphRow integralRow readbackRow provenance localName integralRead graphRead
      sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory integralRow →
      UnaryHistory graphRow →
        UnaryHistory readbackRow →
          UnaryHistory realRow →
            UnaryHistory localName →
              Cont integralRow readbackRow integralRead →
                Cont graphRow readbackRow graphRead →
                  Cont integralRead realRow sealRead →
                    Cont sealRead localName namedRead →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle localName pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row integralRow ∨ hsame row graphRow ∨
                                  hsame row readbackRow ∨ hsame row realRow ∨
                                    hsame row sealRead ∨ hsame row namedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont integralRow readbackRow integralRead ∧
                                  Cont graphRow readbackRow graphRead ∧
                                    Cont integralRead realRow sealRead ∧
                                      Cont sealRead localName namedRead ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle localName pkg)
                              hsame ∧
                            UnaryHistory integralRead ∧ UnaryHistory graphRead ∧
                              UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro integralUnary graphUnary readbackUnary realUnary localNameUnary integralRoute graphRoute
    sealRoute namedRoute provenancePkg localNamePkg
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary readbackUnary integralRoute
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed graphUnary readbackUnary graphRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed integralReadUnary realUnary sealRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed sealReadUnary localNameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row integralRow ∨ hsame row graphRow ∨ hsame row readbackRow ∨
              hsame row realRow ∨ hsame row sealRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont integralRow readbackRow integralRead ∧
              Cont graphRow readbackRow graphRead ∧ Cont integralRead realRow sealRead ∧
                Cont sealRead localName namedRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, integralRoute, graphRoute, sealRoute, namedRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, integralReadUnary, graphReadUnary, sealReadUnary, namedReadUnary⟩

end BEDC.Derived.CalculusUp
