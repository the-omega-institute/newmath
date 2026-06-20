import BEDC.Derived.AspectChainUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AspectChainUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AspectChainConsumerBoundary [AskSetup] [PackageSetup] {x : AspectChainUp}
    {records inscription gap locality otherMinds transport routes provenance nameCert consumerRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    x =
        AspectChainUp.mk records inscription gap locality otherMinds transport routes provenance
          nameCert →
      UnaryHistory records →
        UnaryHistory inscription →
          UnaryHistory routes →
            Cont records inscription consumerRead →
              Cont consumerRead routes boundaryRead →
                PkgSig bundle provenance pkg →
                  PkgSig bundle nameCert pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row records ∨ hsame row inscription ∨ hsame row gap ∨
                            hsame row locality ∨ hsame row otherMinds ∨ hsame row transport ∨
                              hsame row routes ∨ hsame row provenance ∨ hsame row nameCert ∨
                                hsame row boundaryRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont records inscription consumerRead ∧
                            Cont consumerRead routes boundaryRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg)
                        hsame ∧
                      UnaryHistory consumerRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro hx recordsUnary inscriptionUnary routesUnary consumerRoute boundaryRoute provenancePkg
    nameCertPkg
  cases hx
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed recordsUnary inscriptionUnary consumerRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed consumerUnary routesUnary boundaryRoute
  have sourceBoundary :
      (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row) boundaryRead := by
    exact ⟨hsame_refl boundaryRead, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row records ∨ hsame row inscription ∨ hsame row gap ∨ hsame row locality ∨
              hsame row otherMinds ∨ hsame row transport ∨ hsame row routes ∨
                hsame row provenance ∨ hsame row nameCert ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont records inscription consumerRead ∧
              Cont consumerRead routes boundaryRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle nameCert pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead sourceBoundary
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
      exact ⟨source.right, consumerRoute, boundaryRoute, provenancePkg, nameCertPkg⟩
  }
  exact ⟨cert, consumerUnary, boundaryUnary⟩

end BEDC.Derived.AspectChainUp
