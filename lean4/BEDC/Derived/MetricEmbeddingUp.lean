import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetricEmbeddingCarrier (X Y F D R S H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory F ∧ UnaryHistory D ∧
    UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont X F D ∧ Cont D R S ∧ Cont H C P

theorem MetricEmbeddingCarrier_surface
    {X Y F D R S H C P N : BHist} :
    MetricEmbeddingCarrier X Y F D R S H C P N ->
      UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory P ∧
        Cont X F D ∧ Cont D R S ∧ Cont H C P := by
  -- BEDC touchpoint anchor: MetricEmbeddingCarrier BHist Cont UnaryHistory
  intro carrier
  obtain ⟨xUnary, _yUnary, fUnary, _dUnary, rUnary, _sUnary, hUnary, cUnary,
    _pUnary, _nUnary, graphRoute, separatedRoute, provenanceRoute⟩ := carrier
  have dClosed : UnaryHistory D :=
    unary_cont_closed xUnary fUnary graphRoute
  have sClosed : UnaryHistory S :=
    unary_cont_closed dClosed rUnary separatedRoute
  have pClosed : UnaryHistory P :=
    unary_cont_closed hUnary cUnary provenanceRoute
  exact ⟨dClosed, sClosed, pClosed, graphRoute, separatedRoute, provenanceRoute⟩

theorem MetricEmbeddingCarrier_kernel_scope [AskSetup] [PackageSetup]
    {X Y F D R S H C P N scopeRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    MetricEmbeddingCarrier X Y F D R S H C P N →
      Cont S H scopeRead →
        PkgSig bundle P pkg →
          PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row X ∨ hsame row Y ∨ hsame row F ∨ hsame row D ∨
                    hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨
                      hsame row P ∨ hsame row N ∨ hsame row scopeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont X F D ∧ Cont D R S ∧
                    Cont S H scopeRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: MetricEmbeddingCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier scopeRoute provenancePkg namePkg
  obtain ⟨xUnary, _yUnary, fUnary, _dUnary, rUnary, sUnary, hUnary, _cUnary,
    _pUnary, _nUnary, graphRoute, separatedRoute, _provenanceRoute⟩ := carrier
  have dClosed : UnaryHistory D :=
    unary_cont_closed xUnary fUnary graphRoute
  have sClosed : UnaryHistory S :=
    unary_cont_closed dClosed rUnary separatedRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed sUnary hUnary scopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row F ∨ hsame row D ∨
              hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X F D ∧ Cont D R S ∧ Cont S H scopeRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeUnary⟩
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
      cases source.left
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
                          (Or.inr (hsame_refl scopeRead))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, graphRoute, separatedRoute, scopeRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, scopeUnary⟩

end BEDC.Derived.MetricEmbeddingUp
