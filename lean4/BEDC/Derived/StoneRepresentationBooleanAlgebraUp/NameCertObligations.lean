import BEDC.Derived.StoneRepresentationBooleanAlgebraUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StoneRepresentationBooleanAlgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StoneRepresentationBooleanAlgebraCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {B U T L M H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory U ->
        UnaryHistory T ->
          UnaryHistory L ->
            UnaryHistory M ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont B U T ->
                        Cont T L M ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle N pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row B ∨ hsame row U ∨ hsame row T ∨
                                      hsame row L ∨ hsame row M ∨ hsame row H ∨
                                        hsame row C ∨ hsame row P ∨ hsame row N)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont B U T ∧ Cont T L M ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                  hsame ∧ UnaryHistory B ∧ UnaryHistory U ∧
                                UnaryHistory T ∧ UnaryHistory L ∧ UnaryHistory M := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro bUnary uUnary tUnary lUnary mUnary _hUnary _cUnary _pUnary nUnary boolRoute
    clopenRoute provenancePkg localPkg
  have sourceLocal :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, nUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row U ∨ hsame row T ∨ hsame row L ∨ hsame row M ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B U T ∧ Cont T L M ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceLocal
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
      right
      right
      right
      right
      right
      right
      right
      right
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, boolRoute, clopenRoute, provenancePkg, localPkg⟩
  }
  exact ⟨cert, bUnary, uUnary, tUnary, lUnary, mUnary⟩

end BEDC.Derived.StoneRepresentationBooleanAlgebraUp
