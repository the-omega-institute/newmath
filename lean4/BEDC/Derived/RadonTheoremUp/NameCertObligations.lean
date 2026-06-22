import BEDC.Derived.RadonTheoremUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RadonTheoremUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RadonTheoremNameCertObligations [AskSetup] [PackageSetup]
    {affine family dependence partition positiveHull negativeHull transport replay provenance
      localName overlapRead convexRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory affine ->
      UnaryHistory family ->
        UnaryHistory dependence ->
          UnaryHistory partition ->
            UnaryHistory positiveHull ->
              UnaryHistory negativeHull ->
                UnaryHistory transport ->
                  UnaryHistory replay ->
                    PkgSig bundle provenance pkg ->
                      PkgSig bundle localName pkg ->
                        Cont dependence partition overlapRead ->
                          Cont positiveHull negativeHull convexRead ->
                            PkgSig bundle convexRead pkg ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    (hsame row overlapRead ∨ hsame row convexRead) ∧
                                      UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row affine ∨ hsame row family ∨
                                      hsame row dependence ∨ hsame row partition ∨
                                        hsame row positiveHull ∨ hsame row negativeHull ∨
                                          hsame row overlapRead ∨ hsame row convexRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg ∧
                                        PkgSig bundle convexRead pkg)
                                  hsame ∧
                                UnaryHistory overlapRead ∧ UnaryHistory convexRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro _affineUnary _familyUnary dependenceUnary partitionUnary positiveHullUnary
    negativeHullUnary _transportUnary _replayUnary provenancePkg localNamePkg overlapRoute
    convexRoute convexPkg
  have overlapReadUnary : UnaryHistory overlapRead :=
    unary_cont_closed dependenceUnary partitionUnary overlapRoute
  have convexReadUnary : UnaryHistory convexRead :=
    unary_cont_closed positiveHullUnary negativeHullUnary convexRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row overlapRead ∨ hsame row convexRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row affine ∨ hsame row family ∨ hsame row dependence ∨
              hsame row partition ∨ hsame row positiveHull ∨ hsame row negativeHull ∨
                hsame row overlapRead ∨ hsame row convexRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg ∧ PkgSig bundle convexRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro overlapRead ⟨Or.inl (hsame_refl overlapRead), overlapReadUnary⟩
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
          constructor
          · cases source.left with
            | inl sameOverlap =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameOverlap)
            | inr sameConvex =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) sameConvex)
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameOverlap =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl sameOverlap))))))
        | inr sameConvex =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr sameConvex))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, localNamePkg, convexPkg⟩
    }
  exact ⟨cert, overlapReadUnary, convexReadUnary⟩

end BEDC.Derived.RadonTheoremUp
