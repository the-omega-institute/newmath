import BEDC.Derived.FiniteLebesgueNumberUp.Core
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberPhaseRealRadiusConsumerNonescape [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead streamRead sealRead
      sourceRead consumerRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont radius mesh dyadicRead →
        Cont dyadicRead window streamRead →
          Cont streamRead route sealRead →
            Cont sealRead nameRow sourceRead →
              Cont sourceRead provenance consumerRead →
                PkgSig bundle consumerRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row dyadicRead ∨ hsame row streamRead ∨
                          hsame row sealRead ∨ hsame row sourceRead ∨
                            hsame row consumerRead)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle consumerRead pkg ∧ hsame row consumerRead)
                      hsame ∧
                    UnaryHistory consumerRead ∧ Cont sourceRead provenance consumerRead ∧
                      PkgSig bundle consumerRead pkg ∧
                        (Cont consumerRead (BHist.e0 hostTail) sourceRead → False) ∧
                          (Cont consumerRead (BHist.e1 hostTail) sourceRead → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier radiusMeshDyadic dyadicWindowStream streamRouteSeal sealNameSource
    sourceProvenanceConsumer consumerPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshDyadic
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowStream
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed streamUnary routeUnary streamRouteSeal
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed sealUnary nameRowUnary sealNameSource
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sourceUnary provenanceUnary sourceProvenanceConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row sealRead ∨
              hsame row sourceRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
              hsame row consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceConsumer
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, consumerPkg, source.left⟩
  }
  exact
    ⟨cert, consumerUnary, sourceProvenanceConsumer, consumerPkg,
      fun exit => cont_mutual_extension_right_tail_absurd.left sourceProvenanceConsumer exit,
      fun exit => cont_mutual_extension_right_tail_absurd.right sourceProvenanceConsumer exit⟩

end BEDC.Derived.FiniteLebesgueNumberUp
