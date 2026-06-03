import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathL10FourFaceObligationClosurePackage [AskSetup] [PackageSetup]
    {dyadic stream regseq realSeal support transport replay provenance localName faceRoute
      obligationRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dyadic →
      UnaryHistory stream →
        UnaryHistory regseq →
          UnaryHistory realSeal →
            UnaryHistory support →
              Cont dyadic stream faceRoute →
                Cont regseq realSeal support →
                  Cont faceRoute support obligationRoute →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle localName pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row obligationRoute ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                                hsame row realSeal ∨ hsame row obligationRoute)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle localName pkg)
                            hsame ∧
                          UnaryHistory faceRoute ∧ UnaryHistory obligationRoute := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro dyadicUnary streamUnary _regseqUnary _realSealUnary supportUnary faceRouteStep
    _supportStep obligationStep provenancePkg localNamePkg
  have faceRouteUnary : UnaryHistory faceRoute :=
    unary_cont_closed dyadicUnary streamUnary faceRouteStep
  have obligationRouteUnary : UnaryHistory obligationRoute :=
    unary_cont_closed faceRouteUnary supportUnary obligationStep
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obligationRoute ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row obligationRoute)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro obligationRoute ⟨hsame_refl obligationRoute, obligationRouteUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, faceRouteUnary, obligationRouteUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
