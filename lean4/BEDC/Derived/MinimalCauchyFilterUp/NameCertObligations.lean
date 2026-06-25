import BEDC.Derived.MinimalCauchyFilterUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.MinimalCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MinimalCauchyFilterCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source support regular stream dyadic realSeal _transport replay provenance localName
      sourceRead supportRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory support →
        UnaryHistory regular →
          UnaryHistory stream →
            UnaryHistory dyadic →
              UnaryHistory realSeal →
                UnaryHistory replay →
                  UnaryHistory localName →
                    Cont source support sourceRead →
                      Cont support stream supportRead →
                        Cont regular realSeal sealRead →
                          PkgSig bundle provenance pkg →
                            PkgSig bundle localName pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row localName ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row source ∨ hsame row support ∨
                                      hsame row regular ∨ hsame row stream ∨
                                        hsame row dyadic ∨ hsame row realSeal ∨
                                          hsame row sourceRead ∨ hsame row supportRead ∨
                                            hsame row sealRead ∨ hsame row localName)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont source support sourceRead ∧
                                      Cont support stream supportRead ∧
                                        Cont regular realSeal sealRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory sourceRead ∧ UnaryHistory supportRead ∧
                                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro sourceUnary supportUnary regularUnary streamUnary _dyadicUnary realUnary _replayUnary
    localUnary sourceRoute supportRoute sealRoute provenancePkg localPkg
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary supportUnary sourceRoute
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed supportUnary streamUnary supportRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary realUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row support ∨ hsame row regular ∨
              hsame row stream ∨ hsame row dyadic ∨ hsame row realSeal ∨
                hsame row sourceRead ∨ hsame row supportRead ∨ hsame row sealRead ∨
                  hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source support sourceRead ∧
              Cont support stream supportRead ∧ Cont regular realSeal sealRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨hsame_refl localName, localUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, sourceRoute, supportRoute, sealRoute, provenancePkg, localPkg⟩
  }
  exact ⟨cert, sourceReadUnary, supportReadUnary, sealReadUnary⟩

end BEDC.Derived.MinimalCauchyFilterUp
