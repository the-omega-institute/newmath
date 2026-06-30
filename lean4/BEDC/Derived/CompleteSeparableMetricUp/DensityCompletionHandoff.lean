import BEDC.Derived.CompleteSeparableMetricUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompleteSeparableMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompleteSeparableMetricCarrier [AskSetup] [PackageSetup]
    (M K D W T R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory M ∧ UnaryHistory K ∧ UnaryHistory D ∧ UnaryHistory W ∧
    UnaryHistory T ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle N pkg

theorem CompleteSeparableMetricCarrier_density_completion_handoff [AskSetup]
    [PackageSetup] {M K D W T R E H C P N denseWindow toleranceRead regularRead sealRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompleteSeparableMetricCarrier M K D W T R E H C P N bundle pkg ->
      Cont D W denseWindow ->
        Cont denseWindow T toleranceRead ->
          Cont toleranceRead R regularRead ->
            Cont regularRead K sealRead ->
              Cont sealRead E boundaryRead ->
                PkgSig bundle boundaryRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row D ∨ hsame row W ∨ hsame row T ∨
                          hsame row R ∨ hsame row K ∨ hsame row E ∨ hsame row boundaryRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont D W denseWindow ∧
                          Cont denseWindow T toleranceRead ∧ Cont toleranceRead R regularRead ∧
                            Cont regularRead K sealRead ∧ Cont sealRead E boundaryRead ∧
                              PkgSig bundle boundaryRead pkg)
                      hsame ∧
                    UnaryHistory denseWindow ∧ UnaryHistory toleranceRead ∧
                      UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier denseWindowRow toleranceReadRow regularReadRow sealReadRow boundaryReadRow
    boundaryReadPkg
  obtain ⟨_mUnary, kUnary, dUnary, wUnary, tUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _nPkg⟩ := carrier
  have denseWindowUnary : UnaryHistory denseWindow :=
    unary_cont_closed dUnary wUnary denseWindowRow
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed denseWindowUnary tUnary toleranceReadRow
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed toleranceReadUnary rUnary regularReadRow
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary kUnary sealReadRow
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealReadUnary eUnary boundaryReadRow
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row R ∨
            hsame row K ∨ hsame row E ∨ hsame row boundaryRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont D W denseWindow ∧ Cont denseWindow T toleranceRead ∧
            Cont toleranceRead R regularRead ∧ Cont regularRead K sealRead ∧
              Cont sealRead E boundaryRead ∧ PkgSig bundle boundaryRead pkg)
        hsame := by
    constructor
    · constructor
      · exact ⟨boundaryRead, hsame_refl boundaryRead, boundaryReadUnary⟩
      · intro row source
        exact hsame_refl row
      · intro row other same
        exact hsame_symm same
      · intro row other final same₁ same₂
        exact hsame_trans same₁ same₂
      · intro row other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    · intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    · intro row source
      exact
        ⟨source.right, denseWindowRow, toleranceReadRow, regularReadRow, sealReadRow,
          boundaryReadRow, boundaryReadPkg⟩
  exact
    ⟨cert, denseWindowUnary, toleranceReadUnary, regularReadUnary, sealReadUnary,
      boundaryReadUnary⟩

end BEDC.Derived.CompleteSeparableMetricUp
