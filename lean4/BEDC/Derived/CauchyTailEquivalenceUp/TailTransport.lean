import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailEquivalenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyTailEquivalenceTailTransport [AskSetup] [PackageSetup]
    {X Y W M D T H C P N X' Y' T' : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    UnaryHistory X -> UnaryHistory Y -> UnaryHistory W -> UnaryHistory M ->
      UnaryHistory D -> UnaryHistory T -> UnaryHistory H -> UnaryHistory C ->
        UnaryHistory P -> UnaryHistory N -> hsame X X' -> hsame Y Y' ->
          hsame T T' -> Cont W M D -> Cont D T C -> PkgSig bundle P pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row T' ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row X' ∨ hsame row Y' ∨ hsame row W ∨ hsame row M ∨
                    hsame row D ∨ hsame row T' ∨ hsame row H ∨ hsame row C ∨
                      hsame row P ∨ hsame row N)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont W M D ∧ Cont D T C ∧
                    PkgSig bundle P pkg)
                hsame ∧ UnaryHistory X' ∧ UnaryHistory Y' ∧ UnaryHistory T' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro xUnary yUnary _wUnary _mUnary _dUnary tUnary _hUnary _cUnary _pUnary _nUnary
    sameX sameY sameT windowThreshold tailRoute provenancePkg
  have xPrimeUnary : UnaryHistory X' :=
    unary_transport xUnary sameX
  have yPrimeUnary : UnaryHistory Y' :=
    unary_transport yUnary sameY
  have tPrimeUnary : UnaryHistory T' :=
    unary_transport tUnary sameT
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row T' ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X' ∨ hsame row Y' ∨ hsame row W ∨ hsame row M ∨
              hsame row D ∨ hsame row T' ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W M D ∧ Cont D T C ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro T' ⟨hsame_refl T', tPrimeUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowThreshold, tailRoute, provenancePkg⟩
  }
  exact ⟨cert, xPrimeUnary, yPrimeUnary, tPrimeUnary⟩

end BEDC.Derived.CauchyTailEquivalenceUp
