import BEDC.Derived.CauchyRealFieldUp.OperationComposition
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyRealFieldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyRealFieldCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {regseq stream dyadic realSeal add product reciprocal order transport replay provenance
      localName obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRealFieldCarrier regseq stream dyadic realSeal add product reciprocal order transport
        replay provenance localName bundle pkg →
      Cont replay localName obligationRead →
        PkgSig bundle obligationRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row regseq ∨ hsame row stream ∨ hsame row dyadic ∨
                  hsame row realSeal ∨ hsame row add ∨ hsame row product ∨
                    hsame row reciprocal ∨ hsame row order ∨ hsame row obligationRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle obligationRead pkg)
              hsame ∧
            UnaryHistory obligationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier replayRoute obligationPkg
  have replayUnary : UnaryHistory replay :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have localNameUnary : UnaryHistory localName :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed replayUnary localNameUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row regseq ∨ hsame row stream ∨ hsame row dyadic ∨
              hsame row realSeal ∨ hsame row add ∨ hsame row product ∨
                hsame row reciprocal ∨ hsame row order ∨ hsame row obligationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle obligationRead pkg)
          hsame := by
    refine
      { core :=
          { carrier_inhabited := ?_
            equiv_refl := ?_
            equiv_symm := ?_
            equiv_trans := ?_
            carrier_respects_equiv := ?_ }
        pattern_sound := ?_
        ledger_sound := ?_ }
    · exact ⟨obligationRead, hsame_refl obligationRead, obligationUnary⟩
    · intro row _source
      exact hsame_refl row
    · intro _row _other sameRows
      exact hsame_symm sameRows
    · intro _row _middle _other sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro _row _other sameRows source
      exact
        ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    · intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    · intro _row source
      exact ⟨source.right, provenancePkg, obligationPkg⟩
  exact ⟨cert, obligationUnary⟩

end BEDC.Derived.CauchyRealFieldUp
