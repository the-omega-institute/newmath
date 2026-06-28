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

theorem CauchyRealFieldCarrier_order_compatible_reciprocal_boundary [AskSetup] [PackageSetup]
    {regseq stream dyadic realSeal add product reciprocal order transport replay provenance
      localName orderGate reciprocalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRealFieldCarrier regseq stream dyadic realSeal add product reciprocal order transport
        replay provenance localName bundle pkg →
      Cont order reciprocal orderGate →
        Cont orderGate dyadic reciprocalRead →
          PkgSig bundle reciprocalRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row reciprocalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row order ∨ hsame row reciprocal ∨ hsame row dyadic ∨
                    hsame row reciprocalRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle reciprocalRead pkg)
                hsame ∧
              UnaryHistory orderGate ∧ UnaryHistory reciprocalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier orderRoute reciprocalRoute reciprocalPkg
  have dyadicUnary : UnaryHistory dyadic := carrier.right.right.left
  have reciprocalUnary : UnaryHistory reciprocal :=
    carrier.right.right.right.right.right.right.left
  have orderUnary : UnaryHistory order :=
    carrier.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  have orderGateUnary : UnaryHistory orderGate :=
    unary_cont_closed orderUnary reciprocalUnary orderRoute
  have reciprocalReadUnary : UnaryHistory reciprocalRead :=
    unary_cont_closed orderGateUnary dyadicUnary reciprocalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row reciprocalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row order ∨ hsame row reciprocal ∨ hsame row dyadic ∨
              hsame row reciprocalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle reciprocalRead pkg)
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
    · exact ⟨reciprocalRead, hsame_refl reciprocalRead, reciprocalReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    · intro _row source
      exact ⟨source.right, provenancePkg, reciprocalPkg⟩
  exact ⟨cert, orderGateUnary, reciprocalReadUnary⟩

end BEDC.Derived.CauchyRealFieldUp
