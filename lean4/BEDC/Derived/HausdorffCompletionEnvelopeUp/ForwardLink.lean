import BEDC.Derived.HausdorffCompletionEnvelopeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HausdorffCompletionEnvelopeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffCompletionEnvelopeForwardLink [AskSetup] [PackageSetup]
    {H S M W D R L T K P N netRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont H S M ->
      Cont M W D ->
        Cont D R L ->
          Cont R L netRead ->
            Cont netRead L completionRead ->
              UnaryHistory H ->
                UnaryHistory S ->
                  UnaryHistory M ->
                    UnaryHistory W ->
                      UnaryHistory D ->
                        UnaryHistory R ->
                          UnaryHistory L ->
                            PkgSig bundle completionRead pkg ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row completionRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row H ∨ hsame row S ∨ hsame row M ∨
                                      hsame row W ∨ hsame row D ∨ hsame row R ∨
                                        hsame row L ∨ hsame row T ∨ hsame row K ∨
                                          hsame row P ∨ hsame row N ∨
                                            hsame row netRead ∨
                                              hsame row completionRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont R L netRead ∧
                                      Cont netRead L completionRead ∧
                                        PkgSig bundle completionRead pkg)
                                  hsame ∧
                                UnaryHistory netRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro _hausdorffSeparatedRoute _metricStreamRoute _dyadicRegseqRoute netRoute
    completionRoute _unaryH _unaryS _unaryM _unaryW _unaryD unaryR unaryL completionPkg
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed unaryR unaryL netRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed netUnary unaryL completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H ∨ hsame row S ∨ hsame row M ∨ hsame row W ∨
              hsame row D ∨ hsame row R ∨ hsame row L ∨ hsame row T ∨
                hsame row K ∨ hsame row P ∨ hsame row N ∨ hsame row netRead ∨
                  hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R L netRead ∧ Cont netRead L completionRead ∧
              PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr sourceRow.left)))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, netRoute, completionRoute, completionPkg⟩
  }
  exact ⟨cert, netUnary, completionUnary⟩

end BEDC.Derived.HausdorffCompletionEnvelopeUp
