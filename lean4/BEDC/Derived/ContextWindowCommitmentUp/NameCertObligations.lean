import BEDC.Derived.ContextWindowCommitmentUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContextWindowCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContextWindowCommitmentCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {scope prompt boundary refusal consumer transport routes provenance nameCert promptRead
      boundaryRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory scope ->
      UnaryHistory prompt ->
        UnaryHistory boundary ->
          UnaryHistory consumer ->
            Cont scope prompt promptRead ->
              Cont promptRead boundary boundaryRead ->
                Cont boundaryRead consumer consumerRead ->
                  PkgSig bundle provenance pkg ->
                    PkgSig bundle nameCert pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row scope ∨ hsame row prompt ∨ hsame row boundary ∨
                              hsame row refusal ∨ hsame row consumer ∨
                                hsame row transport ∨ hsame row routes ∨
                                  hsame row provenance ∨ hsame row nameCert ∨
                                    hsame row consumerRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont scope prompt promptRead ∧
                              Cont promptRead boundary boundaryRead ∧
                                Cont boundaryRead consumer consumerRead ∧
                                  PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg)
                          hsame ∧ UnaryHistory promptRead ∧ UnaryHistory boundaryRead ∧
                            UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro scopeUnary promptUnary boundaryUnary consumerUnary promptRoute boundaryRoute
    consumerRoute provenancePkg namePkg
  have promptReadUnary : UnaryHistory promptRead :=
    unary_cont_closed scopeUnary promptUnary promptRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed promptReadUnary boundaryUnary boundaryRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed boundaryReadUnary consumerUnary consumerRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row scope ∨ hsame row prompt ∨ hsame row boundary ∨ hsame row refusal ∨
            hsame row consumer ∨ hsame row transport ∨ hsame row routes ∨
              hsame row provenance ∨ hsame row nameCert ∨ hsame row consumerRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont scope prompt promptRead ∧
            Cont promptRead boundary boundaryRead ∧ Cont boundaryRead consumer consumerRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg)
        hsame := by
    refine
      { core := ?core
        pattern_sound := ?pattern_sound
        ledger_sound := ?ledger_sound }
    · refine
        { carrier_inhabited := ?carrier_inhabited
          equiv_refl := ?equiv_refl
          equiv_symm := ?equiv_symm
          equiv_trans := ?equiv_trans
          carrier_respects_equiv := ?carrier_respects_equiv }
      · exact Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerReadUnary⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row other same source
        exact ⟨hsame_trans (hsame_symm same) source.left,
          unary_transport source.right same⟩
    · intro row source
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact source.left
    · intro row source
      exact
        ⟨source.right, promptRoute, boundaryRoute, consumerRoute, provenancePkg, namePkg⟩
  exact ⟨cert, promptReadUnary, boundaryReadUnary, consumerReadUnary⟩

end BEDC.Derived.ContextWindowCommitmentUp
